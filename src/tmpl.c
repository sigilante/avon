/**  tmpl.c
 *
 *  Supercombinator templates: a rule's formals and open body, as skijack
 *  writes them (python/skijack/templates.py) beside the pure SKI term the
 *  rule compiles to.  In share mode a template's key at the head with its
 *  arguments is replaced by the body, instantiated over them: one step for
 *  the S/K plumbing bracket abstraction built.
 *
 *  Nothing is trusted.  A template is used only if abstracting its body
 *  over its formals, the last first, gives its key; the check runs here,
 *  on terms built in one hash-consed table, so equal trees are one node
 *  and every comparison is node identity.  The hash only finds
 *  candidates: a loaded term's jet node is kept for a template only if its
 *  subterm, interned in the same table, is the template's term.
 *
 *  A body's maximal closed subterms are its globals, built once per arena
 *  (with their inner templates wrapped, so a nested root stays a root) and
 *  held by a->tmpl_globals, a collection root.  An instance writes only the
 *  body's open part, in children-first order: lean-ski's ibuild, so that a
 *  template here and a supercombinator proof jet are one object.
 */

#define _POSIX_C_SOURCE 200809L

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "jets.h"

/*  ------------------------------------------------------ the hash-cons */

/*  Canonical nodes: one per distinct tree, leaves the arena's interned
 *  leaves, applications by their canonical children.  Each carries its
 *  digest and the set of formal markers in it (bit i: @x<i>). */
typedef struct {
    uint64_t *key;              /* (l << 32 | r) + 1, 0 empty: S S is 0 0 */
    uint32_t *node;
    size_t    cap, n;
    dmap      digest;           /* canonical node -> digest */
    nmap      vars;             /* canonical node -> marker bits, if any */
    nmap      canon;            /* any node -> its canonical node */
} hcons;

static void hc_free(hcons *h) {
    free(h->key);
    free(h->node);
    dmap_free(&h->digest);
    nmap_free(&h->vars);
    nmap_free(&h->canon);
    memset(h, 0, sizeof *h);
}

static size_t hc_slot(uint64_t k, size_t cap) {
    return (size_t)(k * 0x9e3779b97f4a7c15u >> 17) & (cap - 1);
}

static bool hc_grow(hcons *h) {
    size_t cap = h->cap ? 2 * h->cap : 1024;
    uint64_t *k = calloc(cap, sizeof *k);
    uint32_t *v = malloc(cap * sizeof *v);
    if (!k || !v) { free(k); free(v); return false; }
    for (size_t i = 0; i < h->cap; i++) {
        if (!h->key[i]) continue;
        size_t s = hc_slot(h->key[i], cap);
        while (k[s]) s = (s + 1) & (cap - 1);
        k[s] = h->key[i];
        v[s] = h->node[i];
    }
    free(h->key);
    free(h->node);
    h->key = k;
    h->node = v;
    h->cap = cap;
    return true;
}

/*  The leaf's canonical node: itself, its digest and marker bits noted. */
static uint32_t hc_leaf(av_arena *a, hcons *h, uint32_t leaf) {
    av_digest d;
    if (dmap_get(&h->digest, leaf, &d)) return leaf;
    const char *nm = av_leaf_name(a, av_right(a, leaf));
    if (!dmap_put(&h->digest, leaf, digest_leaf(nm))) return AV_NONE;
    for (unsigned i = 0; i < AV_JET_ARITY_MAX; i++)
        if (leaf == a->jet_mark[i] && !nmap_put(&h->vars, leaf, (uint64_t)1 << i))
            return AV_NONE;
    return leaf;
}

/*  The canonical application of two canonical nodes. */
static uint32_t hc_app(av_arena *a, hcons *h, uint32_t l, uint32_t r) {
    if (2 * (h->n + 1) > h->cap && !hc_grow(h)) return AV_NONE;
    uint64_t k = ((uint64_t)l << 32 | r) + 1;   /* no operand is AV_NONE */
    size_t s = hc_slot(k, h->cap);
    while (h->key[s] && h->key[s] != k) s = (s + 1) & (h->cap - 1);
    if (h->key[s]) return h->node[s];
    av_digest dl, dr;
    uint64_t vl = 0, vr = 0;
    if (!dmap_get(&h->digest, l, &dl) || !dmap_get(&h->digest, r, &dr))
        return AV_NONE;                     /* an operand not canonical */
    uint32_t n = av_app(a, l, r);
    if (n == AV_NONE) return AV_NONE;
    nmap_get(&h->vars, l, &vl);
    nmap_get(&h->vars, r, &vr);
    if (!dmap_put(&h->digest, n, digest_app(dl, dr))) return AV_NONE;
    if ((vl | vr) && !nmap_put(&h->vars, n, vl | vr)) return AV_NONE;
    h->key[s] = k;
    h->node[s] = n;
    h->n++;
    return n;
}

/*  The canonical node of the tree t if the table holds it already, else
 *  AV_NONE: nothing is added.  For a small tree, a pinned term. */
static uint32_t hc_find(const av_arena *a, const hcons *h, uint32_t t, unsigned depth) {
    uint32_t x = av_view(a, t);
    av_digest d;
    if (av_tag(a, x) == AV_LEAF) return dmap_get(&h->digest, x, &d) ? x : AV_NONE;
    if (av_tag(a, x) != AV_APP || depth > 256 || !h->cap) return AV_NONE;
    uint32_t l = hc_find(a, h, av_left(a, x), depth + 1);
    uint32_t r = l == AV_NONE ? AV_NONE : hc_find(a, h, av_right(a, x), depth + 1);
    if (r == AV_NONE) return AV_NONE;
    uint64_t k = ((uint64_t)l << 32 | r) + 1;
    for (size_t s = hc_slot(k, h->cap); h->key[s]; s = (s + 1) & (h->cap - 1))
        if (h->key[s] == k) return h->node[s];
    return AV_NONE;
}

/*  Any term's canonical node, looking through jet nodes and indirections;
 *  memoized by node, so a DAG costs its size. */
static uint32_t hc_canon(av_arena *a, hcons *h, uint32_t t) {
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 256, top = 0;
    item *todo = malloc(cap * sizeof *todo);
    uint32_t out = AV_NONE;
    if (!todo) return AV_NONE;
    todo[top++] = (item){ t, false };
    while (top) {
        item it = todo[--top];
        uint32_t x = av_view(a, it.node);
        uint64_t v;
        if (!it.done && nmap_get(&h->canon, x, &v)) continue;
        uint32_t c;
        if (av_tag(a, x) == AV_LEAF) {
            c = hc_leaf(a, h, x);
        } else if (!it.done) {
            if (top + 3 > cap) {
                item *q = realloc(todo, (cap *= 2) * sizeof *q);
                if (!q) goto done;
                todo = q;
            }
            todo[top++] = (item){ x, true };
            todo[top++] = (item){ av_right(a, x), false };
            todo[top++] = (item){ av_left(a, x), false };
            continue;
        } else {
            uint64_t l, r;
            nmap_get(&h->canon, av_view(a, av_left(a, x)), &l);
            nmap_get(&h->canon, av_view(a, av_right(a, x)), &r);
            c = hc_app(a, h, (uint32_t)l, (uint32_t)r);
        }
        if (c == AV_NONE || !nmap_put(&h->canon, x, c)) goto done;
    }
    uint64_t r;
    if (nmap_get(&h->canon, av_view(a, t), &r)) out = (uint32_t)r;
done:
    free(todo);
    return out;
}

static bool hc_free_in(hcons *h, uint32_t n, unsigned var) {
    uint64_t v = 0;
    nmap_get(&h->vars, n, &v);
    return (v >> var) & 1;
}

/*  [x] t over canonical nodes, x the marker @x<var>: aviary's bracket
 *  abstraction with η (and the core's, and lean-ski's absN). */
static uint32_t hc_abstract(av_arena *a, hcons *h, unsigned var, uint32_t t) {
    uint32_t x = a->jet_mark[var];
    if (av_tag(a, t) != AV_APP)
        return t == x ? AV_NODE_I : hc_app(a, h, AV_NODE_K, t);
    if (!hc_free_in(h, t, var)) return hc_app(a, h, AV_NODE_K, t);
    uint32_t e = av_left(a, t), f = av_right(a, t);
    if (f == x && !hc_free_in(h, e, var)) return e;          /* η */
    uint32_t ae = hc_abstract(a, h, var, e);
    uint32_t af = ae == AV_NONE ? AV_NONE : hc_abstract(a, h, var, f);
    if (af == AV_NONE) return AV_NONE;
    uint32_t s = hc_app(a, h, AV_NODE_S, ae);
    return s == AV_NONE ? AV_NONE : hc_app(a, h, s, af);
}

/*  ------------------------------------------------------------ bodies */

enum { B_VAR, B_REF, B_APP };

/*  A body as parsed: B_VAR (var id), B_REF (a canonical closed node: a
 *  referenced term or S, K, I), B_APP (two earlier nodes). */
typedef struct { uint8_t kind; uint32_t x, y; } bnode;

typedef struct {
    bnode   *n;
    size_t   len, cap;
} body;

static bool body_push(body *b, bnode x) {
    if (b->len == b->cap) {
        size_t cap = b->cap ? 2 * b->cap : 32;
        bnode *q = realloc(b->n, cap * sizeof *q);
        if (!q) return false;
        b->n = q;
        b->cap = cap;
    }
    b->n[b->len++] = x;
    return true;
}

/*  A referenced term, by its 32 hex digits of hash. */
typedef struct { av_digest digest; uint32_t node; } tref;

static int tref_cmp(const void *x, const void *y) {
    return av_digest_cmp(((const tref *)x)->digest, ((const tref *)y)->digest);
}

/*  Parse a prefix body into b; its root's index.  AV_NONE if malformed. */
static uint32_t parse_body(av_arena *a, hcons *h, const char **p, const tref *refs,
                           size_t nrefs, body *b, unsigned *depth) {
    if (++*depth > 100000) return AV_NONE;
    const char *s = *p;
    while (*s == ' ') s++;
    uint32_t out = AV_NONE;
    if (*s == '`') {
        *p = s + 1;
        uint32_t f = parse_body(a, h, p, refs, nrefs, b, depth);
        uint32_t x = f == AV_NONE ? AV_NONE : parse_body(a, h, p, refs, nrefs, b, depth);
        if (x != AV_NONE && body_push(b, (bnode){ B_APP, f, x })) out = (uint32_t)(b->len - 1);
    } else if (*s == 'v') {
        char *end;
        unsigned long v = strtoul(s + 1, &end, 10);
        if (end != s + 1 && v < AV_JET_ARITY_MAX && body_push(b, (bnode){ B_VAR, (uint32_t)v, 0 }))
            out = (uint32_t)(b->len - 1);
        *p = end;
    } else if (*s == '#') {
        av_digest d;
        char hash[AV_HASH_LEN + 1] = AV_HASH_VERSION ":";
        if (strlen(s + 1) >= 32) {
            memcpy(hash + 10, s + 1, 32);
            hash[AV_HASH_LEN] = '\0';
            tref key = { { 0, 0 }, 0 };
            if (av_hash_parse(hash, &d)) {
                key.digest = d;
                const tref *r = bsearch(&key, refs, nrefs, sizeof key, tref_cmp);
                if (r && body_push(b, (bnode){ B_REF, r->node, 0 })) out = (uint32_t)(b->len - 1);
            }
        }
        *p = s + 33;
    } else if (*s == 'S' || *s == 'K' || *s == 'I') {
        uint32_t leaf = *s == 'S' ? AV_NODE_S : *s == 'K' ? AV_NODE_K : AV_NODE_I;
        if (hc_leaf(a, h, leaf) != AV_NONE && body_push(b, (bnode){ B_REF, leaf, 0 }))
            out = (uint32_t)(b->len - 1);
        *p = s + 1;
    }
    --*depth;
    return out;
}

/*  ------------------------------------------------------------ loading */

struct av_tmplset {
    hcons    h;
    nmap     key_jet;           /* canonical key node -> jet id + 1 */
    uint64_t collections;       /* the arena's, at load: the table's node
                                   ids hold only until the next one */
    long     accepted, refused, eta, open, duplicate, wide, unbound;
    long     discarded;                 /* discovered keys saving too little */
    long     words, words_refused;      /* numeral operations */
    long     bits, bits_refused;        /* bit-string operations */
    bool     fix;                       /* Y registered */
};

static bool global_push(av_arena *a, uint32_t node, uint32_t *ix) {
    if (a->nglobals == a->globcap) {
        uint32_t cap = a->globcap ? 2 * a->globcap : 256;
        uint32_t *q = realloc(a->tmpl_globals, cap * sizeof *q);
        if (!q) return false;
        a->tmpl_globals = q;
        a->globcap = cap;
    }
    a->tmpl_globals[a->nglobals] = node;
    *ix = a->nglobals++;
    return true;
}

/*  One template: validate, register, compile.  0 accepted, else why not. */
static int load_one(av_arena *a, av_tmplset *ts, av_digest key, const uint32_t *formals,
                    unsigned k, const body *b, uint32_t root) {
    hcons *h = &ts->h;
    /* the variables' argument positions, the last occurrence binding */
    int argix[AV_JET_ARITY_MAX];
    for (unsigned i = 0; i < AV_JET_ARITY_MAX; i++) argix[i] = -1;
    for (unsigned i = 0; i < k; i++) argix[formals[i]] = (int)i;
    /* canonical nodes of the body, markers for variables; closedness; each
     * node's parent (a parsed body is a tree, children first) */
    uint32_t *cn = malloc((b->len ? b->len : 1) * sizeof *cn);
    bool *closed = malloc((b->len ? b->len : 1) * sizeof *closed);
    uint32_t *parent = malloc((b->len ? b->len : 1) * sizeof *parent);
    int why = 0;
    if (!cn || !closed || !parent) { why = -1; goto done; }
    for (size_t i = 0; i < b->len; i++) parent[i] = UINT32_MAX;
    for (size_t i = 0; i < b->len; i++)
        if (b->n[i].kind == B_APP) parent[b->n[i].x] = parent[b->n[i].y] = (uint32_t)i;
    for (size_t i = 0; i < b->len; i++) {
        const bnode *x = &b->n[i];
        if (x->kind == B_VAR) {
            if (argix[x->x] < 0) { why = 2; goto done; }            /* open */
            cn[i] = hc_leaf(a, h, a->jet_mark[x->x]);
            closed[i] = false;
        } else if (x->kind == B_REF) {
            cn[i] = x->x;
            closed[i] = true;
        } else {
            cn[i] = hc_app(a, h, cn[x->x], cn[x->y]);
            closed[i] = closed[x->x] && closed[x->y];
        }
        if (cn[i] == AV_NONE) { why = -1; goto done; }
    }
    /* η: the body is H applied to the formals in order, H closed */
    {
        uint32_t spine = root;
        bool eta = true;
        for (unsigned i = k; i-- > 0;) {
            const bnode *x = &b->n[spine];
            if (x->kind != B_APP || b->n[x->y].kind != B_VAR || b->n[x->y].x != formals[i]) {
                eta = false;
                break;
            }
            spine = x->x;
        }
        if (eta && closed[spine]) { why = 3; goto done; }
    }
    /* the key: the body abstracted over the formals, the last first */
    uint32_t t = cn[root];
    for (unsigned i = k; i-- > 0 && t != AV_NONE;) t = hc_abstract(a, h, formals[i], t);
    if (t == AV_NONE) { why = -1; goto done; }
    if (av_tag(a, t) != AV_APP) { why = 5; goto done; }          /* S, K or I */
    av_digest d;
    dmap_get(&h->digest, t, &d);
    if (!av_digest_eq(d, key)) { why = 1; goto done; }              /* refused */
    uint64_t have;
    if (nmap_get(&ts->key_jet, t, &have)) { why = 4; goto done; }   /* a duplicate */
    const char *refusal = NULL;
    uint32_t id = jet_entry_for(a, key, t, &refusal);
    if (id == AV_NONE) { why = refusal == jet_collision ? 1 : -1; goto done; }
    if (a->jets[id].tmpl) { why = 4; goto done; }
    if (!nmap_put(&ts->key_jet, t, (uint64_t)id + 1)) { why = -1; goto done; }
    /* compile: open applications are instructions, variables arguments,
     * maximal closed subterms constants (made globals once all keys are in) */
    if (a->ntmpls == a->tmplcap) {
        uint32_t cap = a->tmplcap ? 2 * a->tmplcap : 64;
        av_tmpl *q = realloc(a->tmpls, cap * sizeof *q);
        if (!q) { why = -1; goto done; }
        a->tmpls = q;
        a->tmplcap = cap;
    }
    av_tmpl *T = &a->tmpls[a->ntmpls];
    memset(T, 0, sizeof *T);
    T->jet = id;
    T->k = k;
    uint32_t *opnd = malloc((b->len ? b->len : 1) * sizeof *opnd);
    T->ops = malloc((b->len ? 2 * b->len : 2) * sizeof *T->ops);
    T->consts = malloc((b->len ? b->len : 1) * sizeof *T->consts);
    if (!opnd || !T->ops || !T->consts) {
        free(opnd); free(T->ops); free(T->consts);
        why = -1;
        goto done;
    }
    for (size_t i = 0; i < b->len; i++) {
        const bnode *x = &b->n[i];
        if (x->kind == B_VAR) {
            opnd[i] = TMPL_OPND(TMPL_ARG, (uint32_t)argix[x->x]);
        } else if (closed[i] && (i == root || !closed[parent[i]])) {
            T->consts[T->nconsts] = cn[i];          /* canonical, until globals */
            opnd[i] = TMPL_OPND(TMPL_CONST, T->nconsts++);
        } else if (closed[i]) {
            opnd[i] = UINT32_MAX;                   /* inside a constant */
        } else {
            T->ops[2 * T->nops] = opnd[x->x];
            T->ops[2 * T->nops + 1] = opnd[x->y];
            opnd[i] = TMPL_OPND(TMPL_RES, T->nops++);
        }
    }
    T->root = opnd[root];
    T->root_last = T->nops && T->root == TMPL_OPND(TMPL_RES, T->nops - 1);
    T->key = t;
    free(opnd);
    /* a constructor: the body is argument h applied to the first
     * m arguments in order, h past them; its shape (m, h - m, k - m) */
    {
        uint32_t x = T->root, m = 0;
        bool shape = true;
        while (shape && x >> 30 == TMPL_RES) {
            uint32_t j = x & AV_PAYLOAD, arg = T->ops[2 * j + 1];
            shape = arg >> 30 == TMPL_ARG && j == T->nops - 1 - m;
            x = T->ops[2 * j];
            m++;
        }
        /* the arguments, innermost first, must be 0 .. m-1 */
        for (uint32_t j = 0; shape && j < m; j++)
            shape = T->ops[2 * j + 1] == TMPL_OPND(TMPL_ARG, j);
        if (shape && m == T->nops && x >> 30 == TMPL_ARG &&
            (x & AV_PAYLOAD) >= m && (x & AV_PAYLOAD) < k)
            T->ctor = (av_ctor){ m, (x & AV_PAYLOAD) - m, k - m };
    }
    /* a case: the body is a formal applied to p operands, its root
     * the last instruction, each application of its spine below the root
     * used by its parent alone; an instance meeting that formal as a value
     * joins the dispatch after it (reduce.c, case_join) */
    if (T->root_last && !av_ctor_is(T->ctor)) {
        uint32_t *uses = calloc(T->nops, sizeof *uses);
        if (uses) {
            for (uint32_t i = 0; i < 2 * T->nops; i++)
                if (T->ops[i] >> 30 == TMPL_RES) uses[T->ops[i] & AV_PAYLOAD]++;
            uint32_t j = T->nops - 1, f = T->ops[2 * j], p = 1;
            bool ok = true;
            while (ok && f >> 30 == TMPL_RES) {
                j = f & AV_PAYLOAD;
                ok = uses[j] == 1 && ++p <= AV_JET_ARITY_MAX;
                f = T->ops[2 * j];
            }
            if (ok && f >> 30 == TMPL_ARG && p <= AV_JET_ARITY_MAX &&
                (T->case_spine = calloc(T->nops, 1))) {
                T->case_h = (uint8_t)((f & AV_PAYLOAD) + 1);
                T->case_p = (uint8_t)p;
                for (uint32_t i = T->nops - 1, g = i;; ) {
                    T->case_spine[i] = 1;
                    g = T->ops[2 * i];
                    if (g >> 30 != TMPL_RES) break;
                    i = g & AV_PAYLOAD;
                }
            }
            free(uses);
        }
    }
    /* the root's spine (reduce.c, "Deferred roots"): each application below
     * the root along its function parts, used by its parent alone.  Out of
     * memory, the template has none, and its instances write every node */
    uint32_t *uses = T->root_last ? calloc(T->nops, sizeof *uses) : NULL;
    if (uses) {
        for (uint32_t i = 0; i < 2 * T->nops; i++)
            if (T->ops[i] >> 30 == TMPL_RES) uses[T->ops[i] & AV_PAYLOAD]++;
        for (uint32_t f = T->ops[2 * (T->nops - 1)];
             f >> 30 == TMPL_RES && uses[f & AV_PAYLOAD] == 1; f = T->ops[2 * (f & AV_PAYLOAD)]) {
            if (!T->vspine && !(T->vspine = calloc(T->nops, 1))) break;
            T->vspine[f & AV_PAYLOAD] = 1;
            T->nvspine++;
        }
        free(uses);
    }
    a->jets[id].tmpl = ++a->ntmpls;
done:
    free(cn);
    free(closed);
    free(parent);
    return why;
}

/*  --------------------------------------------------------- the globals */

/*  Each template's constants, rebuilt once with every inner key wrapped as
 *  its jet: a global of a body that is itself a template's term, or holds
 *  one, stays a root.  Memoized over the hash-consed DAG. */
static bool make_globals(av_arena *a, av_tmplset *ts) {
    nmap done = { 0 };
    bool ok = true;
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 256;
    item *todo = malloc(cap * sizeof *todo);
    if (!todo) return false;
    for (uint32_t ti = 0; ok && ti < a->ntmpls; ti++) {
        av_tmpl *T = &a->tmpls[ti];
        if (T->globals_made) continue;
        for (uint32_t c = 0; ok && c < T->nconsts; c++) {
            size_t top = 0;
            todo[top++] = (item){ T->consts[c], false };
            while (ok && top) {
                item it = todo[--top];
                uint32_t x = it.node;
                uint64_t v;
                if (!it.done && nmap_get(&done, x, &v)) continue;
                uint32_t built;
                if (av_tag(a, x) == AV_LEAF) {
                    built = x;
                } else if (!it.done) {
                    if (top + 3 > cap) {
                        item *q = realloc(todo, (cap *= 2) * sizeof *q);
                        if (!q) { ok = false; break; }
                        todo = q;
                    }
                    todo[top++] = (item){ x, true };
                    todo[top++] = (item){ av_right(a, x), false };
                    todo[top++] = (item){ av_left(a, x), false };
                    continue;
                } else {
                    uint64_t l, r;
                    nmap_get(&done, av_left(a, x), &l);
                    nmap_get(&done, av_right(a, x), &r);
                    built = av_app(a, (uint32_t)l, (uint32_t)r);
                }
                uint64_t jid;
                if (built != AV_NONE && nmap_get(&ts->key_jet, x, &jid))
                    built = jet_wrap(a, (uint32_t)jid - 1, built);
                if (built == AV_NONE || !nmap_put(&done, x, built)) { ok = false; break; }
            }
            uint64_t g;
            uint32_t ix;
            if (ok && nmap_get(&done, T->consts[c], &g) && global_push(a, (uint32_t)g, &ix))
                T->consts[c] = ix;
            else
                ok = false;
        }
        T->globals_made = ok;
    }
    free(todo);
    nmap_free(&done);
    return ok;
}

/*  ------------------------------------------------------------ the files */

static char *slurp_path(const char *path, size_t *len) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    size_t cap = 1 << 16, n = 0;
    char *buf = malloc(cap + 1);
    size_t got;
    while (buf && (got = fread(buf + n, 1, cap - n, f)) > 0) {
        n += got;
        if (n == cap) {
            char *q = realloc(buf, (cap *= 2) + 1);
            if (!q) { free(buf); buf = NULL; }
            buf = q;
        }
    }
    fclose(f);
    if (buf) { buf[n] = '\0'; *len = n; }
    return buf;
}

/*  What follows the templates, from a file or discovered: the bit-string
 *  operations, Y, the globals and the scratch.  False, with *msg, on
 *  failure. */
static bool load_tail(av_arena *a, av_tmplset *ts, const char **msg) {
    /* the bit-string operations, with words, where the program holds their
     * terms: pinned (words.c), run on small bit strings before they are
     * keyed, as the numeral operations are */
    for (unsigned op = AV_WOP_BEQ; a->word_suc && op <= AV_WOP_IDEQ; op++) {
        const char *pin = av_bits_pinned(op);
        av_parse_error pe;
        uint32_t pt = av_parse(a, pin, strlen(pin), &pe);
        if (pt == AV_NONE) { *msg = "a pinned bit-string operation does not parse"; return false; }
        uint32_t c = hc_find(a, &ts->h, pt, 0);
        av_digest d;
        uint64_t have;
        if (c == AV_NONE || !dmap_get(&ts->h.digest, c, &d)) continue;   /* not the program's */
        if (nmap_get(&ts->key_jet, c, &have)) {
            /* a template's key, as a function with formals is: the
             * operation on the template's own jet, which instantiates when
             * the operation declines */
            uint32_t tid = (uint32_t)have - 1;
            if (!a->jets[tid].tmpl || a->jets[tid].word_op || a->jets[tid].fix) continue;
            if (!bits_admit(a, c, op)) { ts->bits_refused++; continue; }
            a->jets[tid].word_op = (uint8_t)op;
            ts->bits++;
            continue;
        }
        if (!bits_admit(a, c, op)) { ts->bits_refused++; continue; }
        const char *refusal = NULL;
        uint32_t id = jet_entry_for(a, d, c, &refusal);
        if (id == AV_NONE && refusal == jet_collision) { ts->bits_refused++; continue; }
        if (id == AV_NONE) return false;
        if (a->jets[id].tmpl || a->jets[id].word_op) { ts->bits_refused++; continue; }
        if (!nmap_put(&ts->key_jet, c, (uint64_t)id + 1)) return false;
        a->jets[id].word_op = (uint8_t)op;
        ts->bits++;
    }
    /* Curry's Y, when asked for: keyed like a numeral operation, so
     * its occurrences in the term and in the globals are wrapped */
    if (a->fix_on) {
        static const char Y[] = "S (K (S I I)) (S (S (K S) K) (K (S I I)))";
        av_parse_error pe;
        uint32_t t = av_parse(a, Y, sizeof Y - 1, &pe);
        uint32_t c = t == AV_NONE ? AV_NONE : hc_canon(a, &ts->h, t);
        av_digest d;
        uint64_t have;
        if (c == AV_NONE || !dmap_get(&ts->h.digest, c, &d)) return false;
        if (!nmap_get(&ts->key_jet, c, &have)) {
            const char *refusal = NULL;
            uint32_t id = jet_entry_for(a, d, c, &refusal);
            if (id == AV_NONE && refusal != jet_collision) return false;
            if (id != AV_NONE && !a->jets[id].tmpl && !a->jets[id].word_op) {
                if (!nmap_put(&ts->key_jet, c, (uint64_t)id + 1)) return false;
                a->jets[id].fix = true;
                ts->fix = true;
            }
        }
    }
    if (!make_globals(a, ts)) return false;
    /* one scratch for every instance: the largest template's results and
     * constants, so a fire checks nothing */
    for (uint32_t ti = 0; ti < a->ntmpls; ti++) {
        uint32_t need = a->tmpls[ti].nops + a->tmpls[ti].nconsts;
        if (need > a->tmpl_scratch_cap) {
            uint32_t *q = realloc(a->tmpl_scratch, need * sizeof *q);
            if (!q) return false;
            a->tmpl_scratch = q;
            a->tmpl_scratch_cap = need;
        }
    }
    return true;
}

av_tmplset *av_templates_load(av_arena *a, const char *dir, const char **err) {
    char path[4096];
    size_t len;
    const char *msg = "out of memory";
    av_tmplset *ts = calloc(1, sizeof *ts);
    tref *refs = NULL;
    size_t nrefs = 0, rcap = 0;
    char *text = NULL;
    body b = { 0 };
    if (!ts || !jet_marks(a)) goto fail;
    ts->collections = a->collections;
    if (hc_leaf(a, &ts->h, AV_NODE_S) == AV_NONE || hc_leaf(a, &ts->h, AV_NODE_K) == AV_NONE ||
        hc_leaf(a, &ts->h, AV_NODE_I) == AV_NONE)
        goto fail;
    /* the referenced terms, each checked against its hash */
    snprintf(path, sizeof path, "%s/template_terms.tsv", dir);
    if (!(text = slurp_path(path, &len))) { msg = "cannot read template_terms.tsv"; goto fail; }
    for (char *line = text, *nl; *line; line = nl ? nl + 1 : line + strlen(line)) {
        nl = strchr(line, '\n');
        if (nl) *nl = '\0';
        char *t1 = strchr(line, '\t'), *t2 = t1 ? strchr(t1 + 1, '\t') : NULL;
        if (!t2) { if (*line) { msg = "malformed template_terms.tsv line"; goto fail; } continue; }
        *t1 = '\0';
        av_digest want;
        if (!av_hash_parse(line, &want)) { msg = "malformed hash in template_terms.tsv"; goto fail; }
        /* a term printed as a tree, or in the DAG form, its sharing kept:
         * a large program's referenced terms unfold to trees many times
         * the size of their graphs */
        const char *src = t2 + 1, *dmsg = NULL;
        av_parse_error pe;
        uint32_t t = strncmp(src, "dag ", 4) == 0 ? av_parse_dag(a, src, strlen(src), &dmsg)
                                                  : av_parse(a, src, strlen(src), &pe);
        if (t == AV_NONE) { msg = "unparsable term in template_terms.tsv"; goto fail; }
        uint32_t c = hc_canon(a, &ts->h, t);
        av_digest d;
        if (c == AV_NONE || !dmap_get(&ts->h.digest, c, &d)) goto fail;
        if (!av_digest_eq(d, want)) { msg = "a template term does not match its hash"; goto fail; }
        if (nrefs == rcap) {
            tref *q = realloc(refs, (rcap = rcap ? 2 * rcap : 256) * sizeof *q);
            if (!q) goto fail;
            refs = q;
        }
        refs[nrefs++] = (tref){ d, c };
    }
    free(text);
    text = NULL;
    if (nrefs) qsort(refs, nrefs, sizeof *refs, tref_cmp);
    /* the templates */
    snprintf(path, sizeof path, "%s/templates.tsv", dir);
    if (!(text = slurp_path(path, &len))) { msg = "cannot read templates.tsv"; goto fail; }
    for (char *line = text, *nl; *line; line = nl ? nl + 1 : line + strlen(line)) {
        nl = strchr(line, '\n');
        if (nl) *nl = '\0';
        char *fld[6];
        int k = 0;
        for (char *q = line; k < 6 && q; k++) {
            fld[k] = q;
            q = strchr(q, '\t');
            if (q) *q++ = '\0';
        }
        if (k < 6) { if (*line) { msg = "malformed templates.tsv line"; goto fail; } continue; }
        av_digest key;
        if (!av_hash_parse(fld[0], &key)) { msg = "malformed hash in templates.tsv"; goto fail; }
        unsigned long arity = strtoul(fld[3], NULL, 10);
        if (arity > AV_JET_ARITY_MAX) { ts->wide++; continue; }   /* past the cap */
        uint32_t formals[AV_JET_ARITY_MAX];
        unsigned nf = 0;
        bool fok = arity > 0;
        for (char *q = fld[4]; fok && *q; ) {
            char *end;
            unsigned long v = strtoul(q, &end, 10);
            if (end == q || v >= AV_JET_ARITY_MAX || nf == AV_JET_ARITY_MAX) { fok = false; break; }
            formals[nf++] = (uint32_t)v;
            q = *end == ',' ? end + 1 : end;
            if (*end && *end != ',') fok = false;
        }
        if (!fok || nf != arity) { ts->refused++; continue; }
        b.len = 0;
        const char *bp = fld[5];
        unsigned depth = 0;
        uint32_t root = parse_body(a, &ts->h, &bp, refs, nrefs, &b, &depth);
        while (root != AV_NONE && *bp == ' ') bp++;
        if (root == AV_NONE || *bp) { ts->refused++; continue; }
        int why = load_one(a, ts, key, formals, nf, &b, root);
        if (why < 0) goto fail;
        if (why == 0) ts->accepted++;
        else if (why == 1) ts->refused++;
        else if (why == 2) ts->open++;
        else if (why == 3 || why == 5) ts->eta++;
        else ts->duplicate++;
    }
    /* the numeral operations, when words are on: each term checked
     * against its hash, then run on small numerals before it is keyed */
    free(text);
    text = NULL;
    snprintf(path, sizeof path, "%s/words.tsv", dir);
    if (a->word_suc && (text = slurp_path(path, &len)) != NULL) {
        for (char *line = text, *nl; *line; line = nl ? nl + 1 : line + strlen(line)) {
            nl = strchr(line, '\n');
            if (nl) *nl = '\0';
            char *fld[4];
            int k = 0;
            for (char *q = line; k < 4 && q; k++) {
                fld[k] = q;
                q = strchr(q, '\t');
                if (q) *q++ = '\0';
            }
            if (k < 4) { if (*line) { msg = "malformed words.tsv line"; goto fail; } continue; }
            static const char *const opname[] = { "", "add", "sub", "mul", "ifeq", "ifle", "div", "rem",
                                                  "len", "at", "app", "take", "drop" };
            unsigned op = 0;
            for (unsigned i = 1; i < sizeof opname / sizeof *opname; i++)
                if (strcmp(fld[1], opname[i]) == 0) op = i;
            av_digest want;
            if (!op || !av_hash_parse(fld[0], &want)) { msg = "malformed words.tsv line"; goto fail; }
            av_parse_error pe;
            uint32_t t = av_parse(a, fld[3], strlen(fld[3]), &pe);
            if (t == AV_NONE) { msg = "unparsable term in words.tsv"; goto fail; }
            uint32_t c = hc_canon(a, &ts->h, t);
            av_digest d;
            uint64_t have;
            if (c == AV_NONE || !dmap_get(&ts->h.digest, c, &d)) goto fail;
            if (!av_digest_eq(d, want)) { msg = "a word operation does not match its hash"; goto fail; }
            /* skijack's operation, node for node, or it runs as its term */
            const char *pin = av_word_pinned(op);
            uint32_t pt = pin ? av_parse(a, pin, strlen(pin), &pe) : AV_NONE;
            uint32_t pc = pt == AV_NONE ? AV_NONE : hc_canon(a, &ts->h, pt);
            if (pc == AV_NONE || pc != c || nmap_get(&ts->key_jet, c, &have) || !word_admit(a, c, op)) {
                ts->words_refused++;
                continue;
            }
            const char *refusal = NULL;
            uint32_t id = jet_entry_for(a, want, c, &refusal);
            if (id == AV_NONE && refusal == jet_collision) { ts->words_refused++; continue; }
            if (id == AV_NONE) goto fail;
            if (a->jets[id].tmpl || a->jets[id].word_op) { ts->words_refused++; continue; }
            if (!nmap_put(&ts->key_jet, c, (uint64_t)id + 1)) goto fail;
            a->jets[id].word_op = (uint8_t)op;
            ts->words++;
        }
    }
    if (!load_tail(a, ts, &msg)) goto fail;
    free(text);
    free(refs);
    free(b.n);
    return ts;
fail:
    if (err) *err = msg;
    free(text);
    free(refs);
    free(b.n);
    av_templates_free(ts);
    return NULL;
}

/*  ----------------------------------------------------------- discovery */

/*  Templates found in the program itself, with no compiler's file: bracket
 *  abstraction inverted.  The forward rules (hc_abstract) are
 *
 *      [x] x = I,  [x] M = K M (x not in M),  [x] (M x) = M (x not in M),
 *      [x] (M N) = S ([x] M) ([x] N),
 *
 *  so a body b with [x] b = t is x for I, M for K M, and for S P Q the
 *  bodies of P and Q applied, when the forward rules would take that
 *  application back to S P Q; failing those, t x, which abstracts to t by
 *  η and is no formal at all.  Peeling formals from a key until only η is
 *  left gives its arity and body, and load_one checks the body against the
 *  key as it checks a compiler's: the inversion proposes, the abstraction
 *  decides.  A body is a weak reduct of its key over the formals, the
 *  contractions the inversion undid; a key whose instance would save fewer
 *  than min_steps of them is not worth a template. */

typedef struct {
    nmap memo[AV_JET_ARITY_MAX];    /* per formal: node -> body | steps << 32 */
} decomp;

static void decomp_free(decomp *d) {
    for (unsigned i = 0; i < AV_JET_ARITY_MAX; i++) nmap_free(&d->memo[i]);
}

/*  The body of canonical t over the marker of formal var, and the
 *  contractions from t applied to the marker to it (0: only η).  AV_NONE
 *  out of memory.  Iterative: keys run deep. */
static uint32_t dec_one(av_arena *a, hcons *h, decomp *d, unsigned var, uint32_t t,
                        uint32_t *steps) {
    nmap *memo = &d->memo[var];
    uint32_t x = a->jet_mark[var];
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 64, top = 0;
    item *todo = malloc(cap * sizeof *todo);
    uint64_t v;
    uint32_t out = AV_NONE;
    if (!todo) return AV_NONE;
    todo[top++] = (item){ t, false };
    while (top) {
        item it = todo[--top];
        uint32_t n = it.node;
        if (!it.done && nmap_get(memo, n, &v)) continue;
        uint32_t body, st = 0;
        bool sapp = av_tag(a, n) == AV_APP && av_tag(a, av_left(a, n)) == AV_APP &&
                    av_left(a, av_left(a, n)) == AV_NODE_S;
        if (n == AV_NODE_I) {
            body = x;
            st = 1;
        } else if (av_tag(a, n) == AV_APP && av_left(a, n) == AV_NODE_K) {
            body = av_right(a, n);
            st = 1;
        } else if (sapp && !it.done) {
            if (top + 3 > cap) {
                item *q = realloc(todo, (cap *= 2) * sizeof *q);
                if (!q) goto done;
                todo = q;
            }
            todo[top++] = (item){ n, true };
            todo[top++] = (item){ av_right(a, n), false };
            todo[top++] = (item){ av_right(a, av_left(a, n)), false };
            continue;
        } else if (sapp) {
            uint64_t vp, vq;
            nmap_get(memo, av_right(a, av_left(a, n)), &vp);
            nmap_get(memo, av_right(a, n), &vq);
            uint32_t bp = (uint32_t)vp, bq = (uint32_t)vq;
            body = hc_app(a, h, bp, bq);
            if (body == AV_NONE) goto done;
            /* forward: x in it, and not η's M x with x not in M */
            bool back = hc_free_in(h, body, var) && !(bq == x && !hc_free_in(h, bp, var));

            uint64_t s2 = 1 + (vp >> 32) + (vq >> 32);
            if (back) {
                st = s2 > UINT32_MAX ? UINT32_MAX : (uint32_t)s2;
            } else if ((body = hc_app(a, h, n, x)) == AV_NONE) {
                goto done;
            }
        } else if ((body = hc_app(a, h, n, x)) == AV_NONE) {
            goto done;
        }
        if (!nmap_put(memo, n, (uint64_t)st << 32 | body)) goto done;
    }
    if (nmap_get(memo, t, &v)) {
        out = (uint32_t)v;
        *steps = (uint32_t)(v >> 32);
    }
done:
    free(todo);
    return out;
}

/*  A canonical open body as a parsed one: a tree, children first, its
 *  closed subterms references, its markers variables.  False past `limit`
 *  nodes, as a shared open subterm unfolds, or out of memory. */
static bool body_of(av_arena *a, hcons *h, uint32_t t, body *b, uint32_t *root, size_t limit) {
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 64, top = 0;
    item *todo = malloc(cap * sizeof *todo);
    uint32_t *val = malloc(cap * sizeof *val);
    size_t nval = 0, vcap = cap;
    bool ok = todo && val;
    b->len = 0;
    if (ok) todo[top++] = (item){ t, false };
    while (ok && top) {
        item it = todo[--top];
        uint64_t vars = 0;
        nmap_get(&h->vars, it.node, &vars);
        if (b->len >= limit) { ok = false; break; }
        bnode x;
        if (!vars) {
            x = (bnode){ B_REF, it.node, 0 };
        } else if (av_tag(a, it.node) != AV_APP) {
            unsigned i = (unsigned)__builtin_ctzll(vars);        /* a marker */
            x = (bnode){ B_VAR, i, 0 };
        } else if (!it.done) {
            if (top + 3 > cap) {
                item *q = realloc(todo, (cap *= 2) * sizeof *q);
                if (!q) { ok = false; break; }
                todo = q;
            }
            todo[top++] = (item){ it.node, true };
            todo[top++] = (item){ av_right(a, it.node), false };
            todo[top++] = (item){ av_left(a, it.node), false };
            continue;
        } else {
            uint32_t r = val[--nval], l = val[--nval];
            x = (bnode){ B_APP, l, r };
        }
        if (!body_push(b, x)) { ok = false; break; }
        if (nval == vcap) {
            uint32_t *q = realloc(val, (vcap *= 2) * sizeof *q);
            if (!q) { ok = false; break; }
            val = q;
        }
        val[nval++] = (uint32_t)(b->len - 1);
    }
    if (ok && nval == 1) *root = val[0];
    else ok = false;
    free(todo);
    free(val);
    return ok;
}

av_tmplset *av_templates_discover(av_arena *a, uint32_t t, unsigned min_steps,
                                  const char **err) {
    const char *msg = "out of memory";
    av_tmplset *ts = calloc(1, sizeof *ts);
    decomp d;
    memset(&d, 0, sizeof d);
    body b = { 0 };
    nmap seen = { 0 };
    uint32_t *todo = NULL;
    if (!ts || !jet_marks(a)) goto fail;
    ts->collections = a->collections;
    hcons *h = &ts->h;
    if (hc_leaf(a, h, AV_NODE_S) == AV_NONE || hc_leaf(a, h, AV_NODE_K) == AV_NONE ||
        hc_leaf(a, h, AV_NODE_I) == AV_NONE)
        goto fail;
    for (unsigned i = 0; i < AV_JET_ARITY_MAX; i++)
        if (hc_leaf(a, h, a->jet_mark[i]) == AV_NONE) goto fail;
    /* the program, canonical: every node a candidate key */
    uint32_t root = hc_canon(a, h, t);
    if (root == AV_NONE) goto fail;
    size_t cap = 256, top = 0;
    if (!(todo = malloc(cap * sizeof *todo))) goto fail;
    todo[top++] = root;
    while (top) {
        uint32_t n = todo[--top];
        uint64_t v;
        if (av_tag(a, n) != AV_APP || nmap_get(&seen, n, &v)) continue;
        if (!nmap_put(&seen, n, 1)) goto fail;
        if (top + 2 > cap) {
            uint32_t *q = realloc(todo, (cap *= 2) * sizeof *q);
            if (!q) goto fail;
            todo = q;
        }
        todo[top++] = av_right(a, n);
        todo[top++] = av_left(a, n);
        /* only an S or K application can be an abstraction */
        bool sk = av_left(a, n) == AV_NODE_K ||
                  (av_tag(a, av_left(a, n)) == AV_APP && av_left(a, av_left(a, n)) == AV_NODE_S);
        if (!sk) continue;
        /* η erases a formal its body applies last, as [g] (S (K f) g) is
         * S (K f) and [y] (K y) is K: a partial S P, S or K meets only η,
         * but applied to the formal it inverts at the next.  So such η
         * formals are kept pending, and taken with the next formal that
         * inverts */
        uint32_t cur = n, best = n, formals[AV_JET_ARITY_MAX];
        unsigned k = 0, pend = 0;
        uint64_t saved = 0;
        while (k + pend < AV_JET_ARITY_MAX) {
            uint32_t st = 0;
            uint32_t next = dec_one(a, h, &d, k + pend, cur, &st);
            if (next == AV_NONE) goto fail;
            if (st) {
                for (unsigned i = 0; i <= pend; i++, k++) formals[k] = k;
                pend = 0;
                saved += st;
                cur = best = next;
            } else if (cur == AV_NODE_S || cur == AV_NODE_K ||
                       (av_tag(a, cur) == AV_APP && av_left(a, cur) == AV_NODE_S)) {
                pend++;                         /* S P, S or K: η, pending */
                cur = next;
            } else {
                break;                          /* only η: no formal here */
            }
        }
        cur = best;
        if (!k || saved < min_steps) { ts->discarded++; continue; }
        uint32_t broot;
        if (!body_of(a, h, cur, &b, &broot, 1u << 16)) { ts->wide++; continue; }
        av_digest key;
        if (!dmap_get(&h->digest, n, &key)) goto fail;
        int why = load_one(a, ts, key, formals, k, &b, broot);
        if (why < 0) goto fail;
        if (why == 0) ts->accepted++;
        else if (why == 1) ts->refused++;
        else if (why == 2) ts->open++;
        else if (why == 3 || why == 5) ts->eta++;
        else ts->duplicate++;
    }
    if (!load_tail(a, ts, &msg)) goto fail;
    free(todo);
    nmap_free(&seen);
    decomp_free(&d);
    free(b.n);
    return ts;
fail:
    if (err) *err = msg;
    free(todo);
    nmap_free(&seen);
    decomp_free(&d);
    free(b.n);
    av_templates_free(ts);
    return NULL;
}

/*  ------------------------------------------------------------- binding */

bool av_templates_bind(av_arena *a, av_tmplset *ts, uint32_t t) {
    if (a->collections != ts->collections) return false;   /* the table moved */
    nmap seen = { 0 };
    size_t cap = 256, top = 0;
    uint32_t *todo = malloc(cap * sizeof *todo);
    bool ok = todo != NULL;
    if (ok) todo[top++] = t;
    while (ok && top) {
        uint32_t x = av_res(a, todo[--top]);
        uint64_t v;
        if (nmap_get(&seen, x, &v)) continue;
        if (!(ok = nmap_put(&seen, x, 1))) break;
        if (av_is_word(a, x)) continue;
        if (av_is_list(a, x)) x = av_res(a, av_right(a, x));   /* a list word: its cells */
        if (av_tag(a, x) == AV_JET) {
            uint32_t id = AV_JET_ID(av_left(a, x));
            uint32_t inner = av_right(a, x);
            if (a->jets[id].word_op || a->jets[id].fix) {
                /* a numeral operation or Y, likewise, on its own term only */
                uint32_t c = hc_canon(a, &ts->h, inner);
                uint64_t have;
                if (c == AV_NONE) { ok = false; break; }
                if (!nmap_get(&ts->key_jet, c, &have) || have != (uint64_t)id + 1) {
                    arena_set(a, x, (av_node){ (AV_IND << AV_TAG_SHIFT) | inner, 0 });
                    ts->unbound++;
                }
            } else if (a->jets[id].tmpl) {
                /* the template fires here only on its own term */
                uint32_t c = hc_canon(a, &ts->h, inner);
                if (c == AV_NONE) { ok = false; break; }
                if (c != a->tmpls[a->jets[id].tmpl - 1].key) {
                    arena_set(a, x, (av_node){ (AV_IND << AV_TAG_SHIFT) | inner, 0 });
                    ts->unbound++;
                }
            }
            x = inner;
        }
        if (av_tag(a, x) != AV_APP) continue;
        if (top + 2 > cap) {
            uint32_t *q = realloc(todo, (cap *= 2) * sizeof *q);
            if (!q) { ok = false; break; }
            todo = q;
        }
        todo[top++] = av_left(a, x);
        todo[top++] = av_right(a, x);
    }
    free(todo);
    nmap_free(&seen);
    return ok;
}

void av_templates_free(av_tmplset *ts) {
    if (!ts) return;
    hc_free(&ts->h);
    nmap_free(&ts->key_jet);
    free(ts);
}

long av_templates_discarded(const av_tmplset *ts) {
    return ts->discarded;
}

bool av_templates_fix(const av_tmplset *ts) {
    return ts->fix;
}

void av_templates_word_counts(const av_tmplset *ts, long *admitted, long *refused) {
    *admitted = ts->words;
    *refused = ts->words_refused;
}

void av_templates_bit_counts(const av_tmplset *ts, long *admitted, long *refused) {
    *admitted = ts->bits;
    *refused = ts->bits_refused;
}

void av_templates_counts(const av_tmplset *ts, long *accepted, long *refused,
                         long *skipped, long *unbound) {
    *accepted = ts->accepted;
    *refused = ts->refused;
    *skipped = ts->eta + ts->open + ts->duplicate + ts->wide;
    *unbound = ts->unbound;
}
