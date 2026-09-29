/**  jets.c
 *
 *  The structural hash, the dashboard, residual jets, and the loader's
 *  match (docs/DESIGN.md §5, §6).  The hash is skijack's (dictionary.py):
 *  computed at load and registration only, never while reducing.
 */

#define _POSIX_C_SOURCE 200809L

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "jets.h"

/*  ------------------------------------------------------------ node maps */

void nmap_free(nmap *m) {
    free(m->key);
    free(m->val);
    memset(m, 0, sizeof *m);
}

static size_t slot(uint32_t k, size_t cap) {
    return (size_t)(k * 2654435761u) & (cap - 1);
}

bool nmap_get(const nmap *m, uint32_t k, uint64_t *v) {
    if (!m->cap) return false;
    for (size_t i = slot(k, m->cap);; i = (i + 1) & (m->cap - 1)) {
        if (m->key[i] == AV_NONE) return false;
        if (m->key[i] == k) { *v = m->val[i]; return true; }
    }
}

bool nmap_put(nmap *m, uint32_t k, uint64_t v) {
    if (2 * (m->n + 1) > m->cap) {
        nmap g = { NULL, NULL, m->cap ? m->cap * 2 : 256, 0 };
        g.key = malloc(g.cap * sizeof *g.key);
        g.val = malloc(g.cap * sizeof *g.val);
        if (!g.key || !g.val) { free(g.key); free(g.val); return false; }
        for (size_t i = 0; i < g.cap; i++) g.key[i] = AV_NONE;
        for (size_t i = 0; i < m->cap; i++)
            if (m->key[i] != AV_NONE) nmap_put(&g, m->key[i], m->val[i]);
        nmap_free(m);
        *m = g;
    }
    size_t i = slot(k, m->cap);
    while (m->key[i] != AV_NONE && m->key[i] != k) i = (i + 1) & (m->cap - 1);
    if (m->key[i] == AV_NONE) m->n++;
    m->key[i] = k;
    m->val[i] = v;
    return true;
}

/*  ----------------------------------------------------------------- hash */

static uint64_t digest_of(const void *text, size_t n) {
    uint8_t d[32];
    av_sha256(text, n, d);
    uint64_t v = 0;
    for (int i = 0; i < 8; i++) v = v << 8 | d[i];
    return v;
}

static void hex16(uint64_t v, char out[16]) {
    static const char hx[] = "0123456789abcdef";
    for (int i = 15; i >= 0; i--) { out[i] = hx[v & 15]; v >>= 4; }
}

uint64_t digest_leaf(const char *name) { return digest_of(name, strlen(name)); }

uint64_t digest_app(uint64_t f, uint64_t x) {
    char text[35];
    text[0] = '(';
    hex16(f, text + 1);
    text[17] = ' ';
    hex16(x, text + 18);
    text[34] = ')';
    return digest_of(text, sizeof text);
}

/*  Every node's digest below t, into m keyed by viewed node. */
bool hash_all(const av_arena *a, uint32_t t, nmap *m) {
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 256, top = 0;
    item *todo = malloc(cap * sizeof *todo);
    bool ok = todo != NULL;
    if (ok) todo[top++] = (item){ av_view(a, t), false };
    while (ok && top) {
        item it = todo[--top];
        uint64_t v;
        if (nmap_get(m, it.node, &v)) continue;
        if (av_tag(a, it.node) == AV_LEAF) {
            const char *nm = av_leaf_name(a, av_right(a, it.node));
            ok = nmap_put(m, it.node, digest_of(nm, strlen(nm)));
            continue;
        }
        uint32_t f = av_view(a, av_left(a, it.node));
        uint32_t x = av_view(a, av_right(a, it.node));
        if (it.done) {
            uint64_t hf, hx;
            nmap_get(m, f, &hf);
            nmap_get(m, x, &hx);
            char text[35];
            text[0] = '(';
            hex16(hf, text + 1);
            text[17] = ' ';
            hex16(hx, text + 18);
            text[34] = ')';
            ok = nmap_put(m, it.node, digest_of(text, sizeof text));
            continue;
        }
        if (top + 3 > cap) {
            item *q = realloc(todo, (cap *= 2) * sizeof *q);
            if (!q) { ok = false; break; }
            todo = q;
        }
        todo[top++] = (item){ it.node, true };
        todo[top++] = (item){ x, false };
        todo[top++] = (item){ f, false };
    }
    free(todo);
    return ok;
}

bool av_structural_hash(const av_arena *a, uint32_t t, char out[27]) {
    nmap m = { 0 };
    uint64_t v;
    bool ok = hash_all(a, t, &m) && nmap_get(&m, av_view(a, t), &v);
    nmap_free(&m);
    if (!ok) return false;
    memcpy(out, AV_HASH_VERSION ":", 10);
    hex16(v, out + 10);
    out[26] = '\0';
    return true;
}

bool av_hash_parse(const char *s, uint64_t *digest) {
    if (strncmp(s, AV_HASH_VERSION ":", 10) != 0) return false;
    uint64_t v = 0;
    for (int i = 0; i < 16; i++) {
        char c = s[10 + i];
        unsigned d = c >= '0' && c <= '9' ? (unsigned)(c - '0')
                   : c >= 'a' && c <= 'f' ? (unsigned)(c - 'a' + 10) : 16;
        if (d == 16) return false;
        v = v << 4 | d;
    }
    if (s[26] != '\0' && s[26] != '\t' && s[26] != '\n') return false;
    *digest = v;
    return true;
}

/*  ----------------------------------------------------------- dashboard */

uint32_t jet_find(const av_arena *a, uint64_t digest) {
    if (!a->jet_index_cap) return AV_NONE;
    size_t cap = a->jet_index_cap;
    for (size_t i = (size_t)(digest * 0x9e3779b97f4a7c15u >> 32) & (cap - 1);;
         i = (i + 1) & (cap - 1)) {
        uint32_t id = a->jet_index[i];
        if (id == AV_NONE) return AV_NONE;
        if (a->jets[id].digest == digest) return id;
    }
}

static bool index_put(av_arena *a, uint32_t id) {
    if (2 * (a->njets + 1) > a->jet_index_cap) {
        uint32_t cap = a->jet_index_cap ? a->jet_index_cap * 2 : 64;
        uint32_t *ix = malloc(cap * sizeof *ix);
        if (!ix) return false;
        for (uint32_t i = 0; i < cap; i++) ix[i] = AV_NONE;
        free(a->jet_index);
        a->jet_index = ix;
        a->jet_index_cap = cap;
        for (uint32_t j = 0; j < a->njets; j++)
            if (j != id && !index_put(a, j)) return false;
    }
    uint64_t d = a->jets[id].digest;
    size_t cap = a->jet_index_cap;
    size_t i = (size_t)(d * 0x9e3779b97f4a7c15u >> 32) & (cap - 1);
    while (a->jet_index[i] != AV_NONE) i = (i + 1) & (cap - 1);
    a->jet_index[i] = id;
    return true;
}

static bool marks(av_arena *a) {
    for (unsigned i = 0; i < AV_JET_ARITY_MAX; i++) {
        char nm[8];
        int n = snprintf(nm, sizeof nm, "@x%u", i);
        a->jet_mark[i] = av_leaf(a, nm, (size_t)n);
        if (a->jet_mark[i] == AV_NONE) return false;
    }
    return true;
}

/*  Leaves in the tree unfolding, saturating at SIZE_MAX. */
/*  Every node's leaf count below t, saturating, into m keyed by viewed
 *  node: one pass, each shared node once. */
static bool atoms_all(const av_arena *a, uint32_t t, nmap *m) {
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 256, top = 0;
    item *todo = malloc(cap * sizeof *todo);
    bool ok = todo != NULL;
    if (ok) todo[top++] = (item){ av_view(a, t), false };
    while (ok && top) {
        item it = todo[--top];
        uint64_t v;
        if (nmap_get(m, it.node, &v)) continue;
        if (av_tag(a, it.node) == AV_LEAF) {
            ok = nmap_put(m, it.node, 1);
            continue;
        }
        uint32_t f = av_view(a, av_left(a, it.node)), x = av_view(a, av_right(a, it.node));
        if (it.done) {
            uint64_t sf, sx;
            nmap_get(m, f, &sf);
            nmap_get(m, x, &sx);
            ok = nmap_put(m, it.node, sf + sx < sf ? UINT64_MAX : sf + sx);
            continue;
        }
        if (top + 3 > cap) {
            item *q = realloc(todo, (cap *= 2) * sizeof *q);
            if (!q) { ok = false; break; }
            todo = q;
        }
        todo[top++] = (item){ it.node, true };
        todo[top++] = (item){ x, false };
        todo[top++] = (item){ f, false };
    }
    free(todo);
    return ok;
}

static size_t tree_atoms(const av_arena *a, uint32_t t) {
    nmap m = { 0 };
    uint64_t v;
    size_t out = atoms_all(a, t, &m) && nmap_get(&m, av_view(a, t), &v)
                 ? (v > SIZE_MAX ? SIZE_MAX : (size_t)v) : SIZE_MAX;
    nmap_free(&m);
    return out;
}

/*  The nodes a copy of a template allocates: its distinct application
 *  nodes and jet nodes, the jets' terms not entered. */
static uint32_t template_nodes(const av_arena *a, uint32_t t) {
    nmap seen = { 0 };
    size_t cap = 256, top = 0;
    uint32_t *stk = malloc(cap * sizeof *stk), n = 0;
    if (!stk) return AV_NONE;
    stk[top++] = t;
    while (top) {
        uint32_t x = av_res(a, stk[--top]);
        uint64_t v;
        if (av_tag(a, x) == AV_LEAF || nmap_get(&seen, x, &v)) continue;
        if (!nmap_put(&seen, x, 1)) { n = AV_NONE; break; }
        n++;
        if (av_tag(a, x) == AV_JET) continue;       /* its term is shared */
        if (top + 2 > cap) {
            uint32_t *q = realloc(stk, (cap *= 2) * sizeof *q);
            if (!q) { n = AV_NONE; break; }
            stk = q;
        }
        stk[top++] = av_left(a, x);
        stk[top++] = av_right(a, x);
    }
    free(stk);
    nmap_free(&seen);
    return n;
}

/*  ------------------------------------------------- compiled templates */

#define OP_CONST 0u
#define OP_ARG   1u
#define OP_RES   2u
#define OPND(kind, i) ((kind) << 30 | (i))
#define OP_JET   UINT32_MAX          /* first operand: copy a jet node */

/*  Compile jet id's residual: a post-order walk, each distinct application
 *  or jet node one instruction, markers arguments, leaves constants. */
static bool compile_template(av_arena *a, uint32_t id) {
    av_jet *j = &a->jets[id];
    free(j->ops);
    free(j->consts);
    j->ops = j->consts = NULL;
    j->nops = j->nconsts = 0;
    uint32_t opcap = 16, ccap = 16;
    j->ops = malloc(2 * opcap * sizeof *j->ops);
    j->consts = malloc(ccap * sizeof *j->consts);
    nmap m = { 0 };
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 64, top = 0;
    item *todo = malloc(cap * sizeof *todo);
    bool ok = j->ops && j->consts && todo;
    if (ok) todo[top++] = (item){ j->residual, false };
    while (ok && top) {
        item it = todo[--top];
        uint32_t x = av_res(a, it.node);
        uint64_t v;
        if (!it.done && nmap_get(&m, x, &v)) continue;
        uint32_t opnd = UINT32_MAX;
        uint32_t tag = av_tag(a, x);
        if (tag == AV_LEAF) {
            for (unsigned i = 0; i < j->arity; i++)
                if (x == a->jet_mark[i]) opnd = OPND(OP_ARG, i);
        }
        if (tag == AV_APP && !it.done) {
            if (top + 3 > cap) {
                item *q = realloc(todo, (cap *= 2) * sizeof *q);
                if (!q) { ok = false; break; }
                todo = q;
            }
            todo[top++] = (item){ x, true };
            todo[top++] = (item){ av_right(a, x), false };
            todo[top++] = (item){ av_left(a, x), false };
            continue;
        }
        if (opnd == UINT32_MAX && (tag == AV_LEAF || tag == AV_JET)) {
            if (j->nconsts == ccap) {
                uint32_t *c = realloc(j->consts, (ccap *= 2) * sizeof *c);
                if (!c) { ok = false; break; }
                j->consts = c;
            }
            j->consts[j->nconsts] = x;
            opnd = OPND(OP_CONST, j->nconsts++);
        }
        if (tag == AV_APP || tag == AV_JET) {
            if (j->nops == opcap) {
                uint32_t *o = realloc(j->ops, 2 * (opcap *= 2) * sizeof *o);
                if (!o) { ok = false; break; }
                j->ops = o;
            }
            if (tag == AV_JET) {             /* shared, or copied in share mode */
                j->ops[2 * j->nops] = OP_JET;
                j->ops[2 * j->nops + 1] = opnd;
            } else {
                uint64_t l, r;
                nmap_get(&m, av_res(a, av_left(a, x)), &l);
                nmap_get(&m, av_res(a, av_right(a, x)), &r);
                j->ops[2 * j->nops] = (uint32_t)l;
                j->ops[2 * j->nops + 1] = (uint32_t)r;
            }
            opnd = OPND(OP_RES, j->nops++);
        }
        if (!nmap_put(&m, x, opnd)) { ok = false; break; }
    }
    uint64_t root;
    if (ok && nmap_get(&m, av_res(a, j->residual), &root)) j->root = (uint32_t)root;
    else ok = false;
    j->nodes = j->nops;
    free(todo);
    nmap_free(&m);
    return ok;
}

#define CTOR_NF_STEPS 4096u

/*  The least k in 1..AV_JET_ARITY_MAX at which *tp applied to k markers
 *  reaches an atom at the head, in copy mode, jets off: the state reached
 *  and its contractions.  *tp must be rooted, and is read again after each
 *  run: the runs may collect. */
static bool arity_by_running(av_arena *a, const uint32_t *tp, uint64_t max_steps,
                             unsigned *kout, uint32_t *res, uint64_t *steps,
                             const char **msg) {
    if (!a->jet_mark[0] && !marks(a)) { *msg = "out of memory"; return false; }
    for (unsigned k = 1; k <= AV_JET_ARITY_MAX; k++) {
        uint32_t run = *tp;
        for (unsigned i = 0; i < k && run != AV_NONE; i++) run = av_app(a, run, a->jet_mark[i]);
        if (run == AV_NONE) { *msg = "out of memory"; return false; }
        av_opts o = av_opts_default();
        o.strategy = AV_COPY;
        o.whnf_only = true;
        o.max_steps = max_steps;
        o.jets = false;
        av_result r = av_reduce(a, run, &o);
        if (r.status != AV_WHNF) { *msg = "does not halt within the bound"; return false; }
        uint32_t hd = av_view(a, r.term);
        while (av_tag(a, hd) == AV_APP) hd = av_view(a, av_left(a, hd));
        for (unsigned i = 0; i < k; i++)
            if (hd == a->jet_mark[i]) {
                *kout = k;
                *res = r.term;
                *steps = r.steps;
                return true;
            }
        /* a combinator short of arguments: one more */
    }
    *msg = "no arity up to 32 exposes an argument";
    return false;
}

/*  A residual over k markers is a constructor's when its normal form is
 *  @x_h @x_0 .. @x_(f-1), h >= f: f fields, then k - f continuations, of
 *  which the (h - f)th is applied (§6.8).  res must be rooted. */
static av_ctor classify(av_arena *a, uint32_t res, unsigned k, uint64_t max_steps) {
    av_ctor none = { 0, 0, 0 };
    av_opts o = av_opts_default();
    o.strategy = AV_COPY;
    /* a constructor's fields normalize in a few steps; Y's residual never */
    o.max_steps = max_steps < CTOR_NF_STEPS ? max_steps : CTOR_NF_STEPS;
    o.jets = false;
    av_result r = av_reduce(a, res, &o);
    if (r.status != AV_NORMAL) return none;
    uint32_t spine[AV_JET_ARITY_MAX];
    unsigned n = 0;
    uint32_t x = av_view(a, r.term);
    while (av_tag(a, x) == AV_APP) {
        if (n == AV_JET_ARITY_MAX) return none;
        spine[n++] = av_view(a, av_right(a, x));
        x = av_view(a, av_left(a, x));
    }
    unsigned h = k;
    for (unsigned i = 0; i < k; i++)
        if (x == a->jet_mark[i]) h = i;
    if (h == k || h < n) return none;           /* no marker; or a field */
    for (unsigned i = 0; i < n; i++)            /* spine[n-1] is the first */
        if (spine[n - 1 - i] != a->jet_mark[i]) return none;
    return (av_ctor){ n, h - n, k - n };
}

av_ctor av_ctor_of(av_arena *a, uint32_t t, uint64_t max_steps) {
    av_ctor none = { 0, 0, 0 };
    unsigned k;
    uint32_t res;
    uint64_t steps;
    const char *msg;
    t = av_view(a, t);
    av_root_push(a, &t);
    bool found = arity_by_running(a, &t, max_steps, &k, &res, &steps, &msg);
    av_root_pop(a);
    if (!found) return none;
    av_root_push(a, &res);
    av_ctor c = classify(a, res, k, max_steps);
    av_root_pop(a);
    return c;
}

/*  Register t, deriving its arity, residual, cost and shape once; with
 *  ctors_only, only if the shape is a constructor's (the scan's filter). */
static uint32_t register_term(av_arena *a, uint32_t t, size_t min_atoms,
                              uint64_t max_steps, bool ctors_only, const char **why) {
    const char *msg = NULL;
    t = av_view(a, t);
    size_t atoms = tree_atoms(a, t);
    char h[27];
    uint64_t digest;
    if (atoms < min_atoms) { msg = "below the size floor"; goto done; }
    if (!av_structural_hash(a, t, h) || !av_hash_parse(h, &digest)) { msg = "out of memory"; goto done; }
    uint32_t have = jet_find(a, digest);
    if (have != AV_NONE) return have;

    unsigned k;
    uint32_t res;
    uint64_t steps;
    av_root_push(a, &t);            /* the runs below may collect */
    bool found = arity_by_running(a, &t, max_steps, &k, &res, &steps, &msg);
    av_root_pop(a);
    if (!found) goto done;
    if (steps == 0) { msg = "a residual of cost 0"; goto done; }
    av_root_push(a, &t);
    av_root_push(a, &res);
    av_ctor shape = classify(a, res, k, max_steps);
    av_root_pop(a);
    av_root_pop(a);
    if (ctors_only && !av_ctor_is(shape)) { msg = "not a constructor"; goto done; }

    if (a->njets == a->jetcap) {
        uint32_t cap = a->jetcap ? a->jetcap * 2 : 64;
        av_jet *j = realloc(a->jets, cap * sizeof *j);
        if (!j) { msg = "out of memory"; goto done; }
        a->jets = j;
        a->jetcap = cap;
    }
    uint32_t id = a->njets;
    a->jets[id] = (av_jet){ .digest = digest, .fallback = t, .residual = res,
                            .arity = k, .cost = steps, .term_nodes = template_nodes(a, t),
                            .atoms = atoms, .residual_ok = true, .interp = -1,
                            .ctor = shape };
    a->njets++;
    if (a->jets[id].term_nodes == AV_NONE || !compile_template(a, id) ||
        !index_put(a, id)) {
        free(a->jets[id].ops);
        free(a->jets[id].consts);
        a->njets--;
        msg = "out of memory";
        goto done;
    }
    return id;
done:
    if (why) *why = msg;
    return AV_NONE;
}

uint32_t av_jet_register(av_arena *a, uint32_t t, size_t min_atoms,
                         uint64_t max_steps, const char **why) {
    return register_term(a, t, min_atoms, max_steps, false, why);
}

uint32_t jet_entry_for(av_arena *a, uint64_t digest, uint32_t t) {
    uint32_t have = jet_find(a, digest);
    if (have != AV_NONE) return have;
    if (a->njets == a->jetcap) {
        uint32_t cap = a->jetcap ? a->jetcap * 2 : 64;
        av_jet *j = realloc(a->jets, cap * sizeof *j);
        if (!j) return AV_NONE;
        a->jets = j;
        a->jetcap = cap;
    }
    uint32_t id = a->njets;
    uint32_t tn = template_nodes(a, t);
    if (tn == AV_NONE) return AV_NONE;
    a->jets[id] = (av_jet){ .digest = digest, .fallback = t, .residual = t,
                            .term_nodes = tn, .atoms = tree_atoms(a, t),
                            .residual_ok = false, .interp = -1 };
    a->njets++;
    if (!index_put(a, id)) { a->njets--; return AV_NONE; }
    return id;
}

/*  ------------------------------------------------------------- matching */

static uint32_t jet_node(av_arena *a, uint32_t idbits, uint32_t inner) {
    uint32_t n = av_app(a, inner, inner);
    if (n == AV_NONE) return AV_NONE;
    arena_set(a, n, (av_node){ (AV_JET << AV_TAG_SHIFT) | idbits, inner });
    return n;
}

/*  A fresh copy of t with jets wrapped; the root itself is not wrapped
 *  when skip_root, which is how a jet's own term is matched for its
 *  insides.  shared marks the jet nodes' terms as the dashboard's. */
static uint32_t match(av_arena *a, uint32_t t, bool skip_root, bool shared) {
    nmap dig = { 0 }, out = { 0 };
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 256, top = 0;
    item *todo = malloc(cap * sizeof *todo);
    uint32_t root = av_view(a, t), result = AV_NONE;
    if (!todo || !hash_all(a, root, &dig)) goto done;
    todo[top++] = (item){ root, false };
    while (top) {
        item it = todo[--top];
        uint64_t v;
        if (!it.done && nmap_get(&out, it.node, &v)) continue;
        uint32_t built;
        if (av_tag(a, it.node) == AV_LEAF) {
            built = it.node;
        } else {
            uint32_t f = av_view(a, av_left(a, it.node)), x = av_view(a, av_right(a, it.node));
            if (!it.done) {
                if (top + 3 > cap) {
                    item *q = realloc(todo, (cap *= 2) * sizeof *q);
                    if (!q) goto done;
                    todo = q;
                }
                todo[top++] = (item){ it.node, true };
                todo[top++] = (item){ x, false };
                todo[top++] = (item){ f, false };
                continue;
            }
            uint64_t nf, nx;
            nmap_get(&out, f, &nf);
            nmap_get(&out, x, &nx);
            built = av_app(a, (uint32_t)nf, (uint32_t)nx);   /* never reused */
            if (built == AV_NONE) goto done;
        }
        uint64_t d;
        nmap_get(&dig, it.node, &d);
        uint32_t id = jet_find(a, d);
        if (id != AV_NONE && !(skip_root && it.node == root)) {
            built = jet_node(a, id | (shared ? AV_JET_SHARED : 0), built);
            if (built == AV_NONE) goto done;
        }
        if (!nmap_put(&out, it.node, built)) goto done;
    }
    uint64_t r;
    if (nmap_get(&out, root, &r)) result = (uint32_t)r;
done:
    free(todo);
    nmap_free(&dig);
    nmap_free(&out);
    return result;
}

uint32_t av_jets_match(av_arena *a, uint32_t t) {
    return match(a, t, false, false);
}

static bool wrap_insides(av_arena *a);

typedef struct { uint64_t digest; uint32_t node; } dnode;

static int by_digest(const void *x, const void *y) {
    uint64_t a = ((const dnode *)x)->digest, b = ((const dnode *)y)->digest;
    return (a > b) - (a < b);
}

long av_jets_ctors(av_arena *a, uint32_t t, size_t max_atoms) {
    /* the distinct subterms, by digest, and every node's size: one pass
     * each, since sizing each subterm apart is quadratic in the term */
    nmap dig = { 0 }, sizes = { 0 };
    dnode *all = NULL;
    uint32_t *cand = NULL;
    size_t n = 0, m = 0;
    long added = 0;
    bool ok = hash_all(a, av_view(a, t), &dig) && atoms_all(a, av_view(a, t), &sizes) &&
              (all = malloc((dig.n ? dig.n : 1) * sizeof *all)) != NULL;
    for (size_t i = 0; ok && i < dig.cap; i++)
        if (dig.key[i] != AV_NONE && av_tag(a, dig.key[i]) == AV_APP)
            all[m++] = (dnode){ dig.val[i], dig.key[i] };
    nmap_free(&dig);
    if (ok) qsort(all, m, sizeof *all, by_digest);
    ok = ok && (cand = malloc((m ? m : 1) * sizeof *cand)) != NULL;
    for (size_t i = 0; ok && i < m; i++) {
        if (i && all[i].digest == all[i - 1].digest) continue;
        if (jet_find(a, all[i].digest) != AV_NONE) continue;
        uint64_t atoms = 0;
        nmap_get(&sizes, all[i].node, &atoms);
        if (atoms >= 2 && atoms <= max_atoms) cand[n++] = all[i].node;
    }
    free(all);
    nmap_free(&sizes);
    /* rooted: the runs collect */
    for (size_t i = 0; ok && i < n; i++) av_root_push(a, &cand[i]);
    for (size_t i = 0; ok && i < n; i++) {
        uint32_t before = a->njets;
        if (register_term(a, cand[i], 0, 1000000, true, NULL) != AV_NONE &&
            a->njets > before) added++;
    }
    for (size_t i = 0; ok && i < n; i++) av_root_pop(a);
    free(cand);
    if (ok && added && !wrap_insides(a)) ok = false;
    return ok ? added : -1;
}

/*  After a dictionary is registered: wrap each jet's inner jets, in its
 *  term and in its residual, so a fire or an unwrap keeps them. */
static bool wrap_insides(av_arena *a) {
    for (uint32_t id = 0; id < a->njets; id++) {
        if (!a->jets[id].residual_ok) continue;
        uint32_t f = match(a, a->jets[id].fallback, true, true);
        uint32_t r = match(a, a->jets[id].residual, true, true);
        if (f == AV_NONE || r == AV_NONE) return false;
        a->jets[id].fallback = f;
        a->jets[id].residual = r;
        a->jets[id].term_nodes = template_nodes(a, f);
        if (a->jets[id].term_nodes == AV_NONE || !compile_template(a, id))
            return false;
    }
    return true;
}

long av_jets_load(av_arena *a, const char *path, size_t min_atoms,
                  const char **err) {
    FILE *f = fopen(path, "rb");
    if (!f) { if (err) *err = "cannot open the dictionary"; return -1; }
    char *line = NULL;
    size_t cap = 0;
    ssize_t n;
    long registered = 0;
    const char *msg = NULL;
    while ((n = getline(&line, &cap, f)) > 0) {
        char *h = line, *t1 = strchr(line, '\t');
        char *t2 = t1 ? strchr(t1 + 1, '\t') : NULL;
        if (!t2) { msg = "malformed dictionary line"; break; }
        *t1 = '\0';
        char *term = t2 + 1;
        size_t len = strcspn(term, "\n");
        uint64_t want;
        if (!av_hash_parse(h, &want)) { msg = "malformed hash"; break; }
        av_parse_error pe;
        uint32_t t = av_parse(a, term, len, &pe);
        if (t == AV_NONE) { msg = "unparsable dictionary term"; break; }
        char got[27];
        uint64_t d;
        if (!av_structural_hash(a, t, got) || !av_hash_parse(got, &d)) { msg = "out of memory"; break; }
        if (d != want) { msg = "a dictionary hash does not match its term"; break; }
        if (av_jet_register(a, t, min_atoms, 1000000, NULL) != AV_NONE) registered++;
    }
    free(line);
    fclose(f);
    if (!msg && !wrap_insides(a)) msg = "out of memory";
    if (!msg && !av_collect(a, 0, NULL, NULL, NULL)) msg = "out of memory";
    if (msg) { if (err) *err = msg; return -1; }
    return registered;
}

/*  --------------------------------------------------------- instances */

/*  Copy a template: application nodes always fresh, markers replaced by
 *  args, leaves shared, jet nodes shared or, with fresh_jets, copied (a
 *  copy's term is the dashboard's, so it is marked shared). */
static uint32_t copy_template(av_arena *a, uint32_t root, const av_jet *j,
                              const uint32_t *args, bool fresh_jets) {
    nmap m = { 0 };
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 64, top = 0;
    item *todo = malloc(cap * sizeof *todo);
    uint32_t result = AV_NONE;
    if (!todo) goto done;
    todo[top++] = (item){ root, false };
    while (top) {
        item it = todo[--top];
        uint32_t x = av_res(a, it.node);
        uint64_t v;
        if (!it.done && nmap_get(&m, x, &v)) continue;
        uint32_t built;
        if (av_tag(a, x) == AV_LEAF) {
            built = x;
            for (unsigned i = 0; args && i < j->arity; i++)
                if (x == a->jet_mark[i]) built = args[i];
        } else if (av_tag(a, x) == AV_JET) {
            built = fresh_jets
                ? jet_node(a, AV_JET_ID(av_left(a, x)) | AV_JET_SHARED, av_right(a, x))
                : x;
            if (built == AV_NONE) goto done;
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
            nmap_get(&m, av_res(a, av_left(a, x)), &l);
            nmap_get(&m, av_res(a, av_right(a, x)), &r);
            built = av_app(a, (uint32_t)l, (uint32_t)r);
            if (built == AV_NONE) goto done;
        }
        if (!nmap_put(&m, x, built)) goto done;
    }
    uint64_t r;
    if (nmap_get(&m, av_res(a, root), &r)) result = (uint32_t)r;
done:
    free(todo);
    nmap_free(&m);
    return result;
}

uint32_t jet_instance(av_arena *a, uint32_t id, const uint32_t *args,
                      bool fresh_jets) {
    const av_jet *j = &a->jets[id];
    assert(!a->jet_scratch_busy && "jet instances do not nest");
    if (a->jet_scratch_cap < j->nops) {
        uint32_t *s = realloc(a->jet_scratch, j->nops * sizeof *s);
        if (!s) return AV_NONE;
        a->jet_scratch = s;
        a->jet_scratch_cap = j->nops;
    }
    uint32_t *out = a->jet_scratch;
    a->jet_scratch_busy = true;
#define OPERAND(x) ((x) >> 30 == OP_CONST ? j->consts[(x) & AV_PAYLOAD]  \
                  : (x) >> 30 == OP_ARG   ? args[(x) & AV_PAYLOAD]       \
                                          : out[(x) & AV_PAYLOAD])
    for (uint32_t i = 0; i < j->nops; i++) {
        uint32_t p = j->ops[2 * i], q = j->ops[2 * i + 1];
        uint32_t n;
        if (p == OP_JET) {
            uint32_t c = OPERAND(q);
            n = fresh_jets
                ? jet_node(a, AV_JET_ID(av_left(a, c)) | AV_JET_SHARED, av_right(a, c))
                : c;
        } else {
            n = av_app(a, OPERAND(p), OPERAND(q));
        }
        if (n == AV_NONE) { a->jet_scratch_busy = false; return AV_NONE; }
        out[i] = n;
    }
    a->jet_scratch_busy = false;
    return OPERAND(j->root);
#undef OPERAND
}

uint32_t jet_term_copy(av_arena *a, uint32_t id) {
    return copy_template(a, a->jets[id].fallback, &a->jets[id], NULL, true);
}

/*  --------------------------------------------------------------- equal */

int av_equal(const av_arena *a, uint32_t x, uint32_t y, size_t budget) {
    /* Pairs already compared are not compared again: tree equality is the
     * conjunction over every pair reachable from (x, y), so each distinct
     * pair needs one visit, and a shared graph costs its size, not its
     * unfolding's.  The budget bounds distinct pairs. */
    size_t cap = 256, top = 0, scap = 1024, sn = 0;
    uint32_t *stk = malloc(2 * cap * sizeof *stk);
    uint64_t *set = calloc(scap, sizeof *set);           /* 0 = empty */
    int out = 1;
    if (!stk || !set) { free(stk); free(set); return -1; }
    stk[0] = x;
    stk[1] = y;
    top = 1;
    while (top) {
        top--;
        uint32_t p = av_view(a, stk[2 * top]), q = av_view(a, stk[2 * top + 1]);
        if (p == q) continue;                  /* one node: one tree */
        uint64_t key = ((uint64_t)p << 32 | q) + 1;        /* never 0 */
        size_t i = (size_t)(key * 0x9e3779b97f4a7c15u >> 32) & (scap - 1);
        while (set[i] && set[i] != key) i = (i + 1) & (scap - 1);
        if (set[i]) continue;                  /* compared already */
        set[i] = key;
        if (++sn > budget) { out = -1; break; }
        if (2 * sn > scap) {                   /* grow the set */
            size_t ncap = scap * 2;
            uint64_t *ns = calloc(ncap, sizeof *ns);
            if (!ns) { out = -1; break; }
            for (size_t k = 0; k < scap; k++) {
                if (!set[k]) continue;
                size_t j = (size_t)(set[k] * 0x9e3779b97f4a7c15u >> 32) & (ncap - 1);
                while (ns[j]) j = (j + 1) & (ncap - 1);
                ns[j] = set[k];
            }
            free(set);
            set = ns;
            scap = ncap;
        }
        if (av_tag(a, p) != av_tag(a, q)) { out = 0; break; }
        if (av_tag(a, p) == AV_LEAF) {
            if (av_right(a, p) != av_right(a, q)) { out = 0; break; }
            continue;
        }
        if (top + 2 > cap) {
            uint32_t *s = realloc(stk, 2 * (cap *= 2) * sizeof *s);
            if (!s) { out = -1; break; }
            stk = s;
        }
        stk[2 * top] = av_left(a, p);
        stk[2 * top + 1] = av_left(a, q);
        top++;
        stk[2 * top] = av_right(a, p);
        stk[2 * top + 1] = av_right(a, q);
        top++;
    }
    free(stk);
    free(set);
    return out;
}
