/**  jets.c
 *
 *  The structural hash, the dashboard, residual jets, and the loader's
 *  match.  The hash is skijack's (dictionary.py):
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

/*  ---------------------------------------------------------- digest maps */

void dmap_free(dmap *m) {
    free(m->key);
    free(m->val);
    memset(m, 0, sizeof *m);
}

bool dmap_get(const dmap *m, uint32_t k, av_digest *v) {
    if (!m->cap) return false;
    for (size_t i = slot(k, m->cap);; i = (i + 1) & (m->cap - 1)) {
        if (m->key[i] == AV_NONE) return false;
        if (m->key[i] == k) { *v = m->val[i]; return true; }
    }
}

bool dmap_put(dmap *m, uint32_t k, av_digest v) {
    if (2 * (m->n + 1) > m->cap) {
        dmap g = { NULL, NULL, m->cap ? m->cap * 2 : 256, 0 };
        g.key = malloc(g.cap * sizeof *g.key);
        g.val = malloc(g.cap * sizeof *g.val);
        if (!g.key || !g.val) { free(g.key); free(g.val); return false; }
        for (size_t i = 0; i < g.cap; i++) g.key[i] = AV_NONE;
        for (size_t i = 0; i < m->cap; i++)
            if (m->key[i] != AV_NONE) dmap_put(&g, m->key[i], m->val[i]);
        dmap_free(m);
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

/*  A digest is SHA-256's first 16 bytes. */
static av_digest digest_of(const void *text, size_t n) {
    uint8_t d[32];
    av_sha256(text, n, d);
    av_digest v = { 0, 0 };
    for (int i = 0; i < 8; i++) v.hi = v.hi << 8 | d[i];
    for (int i = 8; i < 16; i++) v.lo = v.lo << 8 | d[i];
    return v;
}

static void hex16(uint64_t v, char out[16]) {
    static const char hx[] = "0123456789abcdef";
    for (int i = 15; i >= 0; i--) { out[i] = hx[v & 15]; v >>= 4; }
}

/*  A digest's 32 hex digits, as the Python spells them. */
static void hex32(av_digest v, char out[32]) {
    hex16(v.hi, out);
    hex16(v.lo, out + 16);
}

av_digest digest_leaf(const char *name) { return digest_of(name, strlen(name)); }

av_digest digest_app(av_digest f, av_digest x) {
    char text[67];
    text[0] = '(';
    hex32(f, text + 1);
    text[33] = ' ';
    hex32(x, text + 34);
    text[66] = ')';
    return digest_of(text, sizeof text);
}

/*  Every node's digest below t, into m keyed by viewed node. */
bool hash_all(const av_arena *a, uint32_t t, dmap *m) {
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 256, top = 0;
    item *todo = malloc(cap * sizeof *todo);
    bool ok = todo != NULL;
    if (ok) todo[top++] = (item){ av_view(a, t), false };
    while (ok && top) {
        item it = todo[--top];
        av_digest v;
        if (dmap_get(m, it.node, &v)) continue;
        if (av_tag(a, it.node) == AV_LEAF) {
            const char *nm = av_leaf_name(a, av_right(a, it.node));
            ok = dmap_put(m, it.node, digest_of(nm, strlen(nm)));
            continue;
        }
        uint32_t f = av_view(a, av_left(a, it.node));
        uint32_t x = av_view(a, av_right(a, it.node));
        if (it.done) {
            av_digest hf, hx;
            dmap_get(m, f, &hf);
            dmap_get(m, x, &hx);
            ok = dmap_put(m, it.node, digest_app(hf, hx));
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

bool av_structural_hash(const av_arena *a, uint32_t t, char out[AV_HASH_LEN + 1]) {
    dmap m = { 0 };
    av_digest v;
    bool ok = hash_all(a, t, &m) && dmap_get(&m, av_view(a, t), &v);
    dmap_free(&m);
    if (!ok) return false;
    memcpy(out, AV_HASH_VERSION ":", 10);
    hex32(v, out + 10);
    out[AV_HASH_LEN] = '\0';
    return true;
}

bool av_hash_parse(const char *s, av_digest *digest) {
    if (strncmp(s, AV_HASH_VERSION ":", 10) != 0) return false;
    av_digest v = { 0, 0 };
    for (int i = 0; i < 32; i++) {
        char c = s[10 + i];
        unsigned d = c >= '0' && c <= '9' ? (unsigned)(c - '0')
                   : c >= 'a' && c <= 'f' ? (unsigned)(c - 'a' + 10) : 16;
        if (d == 16) return false;
        if (i < 16) v.hi = v.hi << 4 | d;
        else v.lo = v.lo << 4 | d;
    }
    char end = s[AV_HASH_LEN];
    if (end != '\0' && end != '\t' && end != '\n') return false;
    *digest = v;
    return true;
}

/*  ----------------------------------------------------------- dashboard */

/*  The index probes by a digest's first word; an entry is found by all of it. */
static size_t index_slot(av_digest d, size_t cap) {
    return (size_t)(d.hi * 0x9e3779b97f4a7c15u >> 32) & (cap - 1);
}

uint32_t jet_find(const av_arena *a, av_digest digest) {
    if (!a->jet_index_cap) return AV_NONE;
    size_t cap = a->jet_index_cap;
    for (size_t i = index_slot(digest, cap);; i = (i + 1) & (cap - 1)) {
        uint32_t id = a->jet_index[i];
        if (id == AV_NONE) return AV_NONE;
        if (av_digest_eq(a->jets[id].digest, digest)) return id;
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
    size_t cap = a->jet_index_cap;
    size_t i = index_slot(a->jets[id].digest, cap);
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

bool jet_marks(av_arena *a) { return a->jet_mark[0] || marks(a); }

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
 *  which the (h - f)th is applied.  res must be rooted. */
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

/*  Whether the jet under a digest is t's: the digest names a term, and two
 *  terms may share one.  The budget is the one a full comparison is given
 *  elsewhere (reduce.c, interp.c): it counts distinct pairs, so it bounds
 *  a shared graph by its size, never its unfolding. */
static bool jet_is(const av_arena *a, uint32_t id, uint32_t t) {
    return av_equal(a, a->jets[id].fallback, t, 100000000) == 1;
}

const char jet_collision[] = "a different term under the same digest";

/*  Register t, deriving its arity, residual, cost and shape once; with
 *  ctors_only, only if the shape is a constructor's (the scan's filter). */
static uint32_t register_term(av_arena *a, uint32_t t, size_t min_atoms,
                              uint64_t max_steps, bool ctors_only, const char **why) {
    const char *msg = NULL;
    t = av_view(a, t);
    size_t atoms = tree_atoms(a, t);
    char h[AV_HASH_LEN + 1];
    av_digest digest;
    if (atoms < min_atoms) { msg = "below the size floor"; goto done; }
    if (!av_structural_hash(a, t, h) || !av_hash_parse(h, &digest)) { msg = "out of memory"; goto done; }
    uint32_t have = jet_find(a, digest);
    if (have != AV_NONE) {
        if (jet_is(a, have, t)) return have;
        msg = jet_collision;
        goto done;
    }

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
    if (a->njets >= AV_JET_WORD) { msg = "too many jets"; goto done; }  /* ids below the word flag */

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

uint32_t jet_entry_for(av_arena *a, av_digest digest, uint32_t t, const char **why) {
    /* *why is written only when the entry is refused: a caller may pass
     * the message it reports on failure */
    uint32_t have = jet_find(a, digest);
    if (have != AV_NONE) {
        if (jet_is(a, have, t)) return have;
        if (why) *why = jet_collision;
        return AV_NONE;
    }
    if (a->njets >= AV_JET_WORD) { if (why) *why = "too many jets"; return AV_NONE; }
    if (a->njets == a->jetcap) {
        uint32_t cap = a->jetcap ? a->jetcap * 2 : 64;
        av_jet *j = realloc(a->jets, cap * sizeof *j);
        if (!j) { if (why) *why = "out of memory"; return AV_NONE; }
        a->jets = j;
        a->jetcap = cap;
    }
    uint32_t id = a->njets;
    uint32_t tn = template_nodes(a, t);
    if (tn == AV_NONE) { if (why) *why = "out of memory"; return AV_NONE; }
    a->jets[id] = (av_jet){ .digest = digest, .fallback = t, .residual = t,
                            .term_nodes = tn, .atoms = tree_atoms(a, t),
                            .residual_ok = false, .interp = -1 };
    a->njets++;
    if (!index_put(a, id)) { a->njets--; if (why) *why = "out of memory"; return AV_NONE; }
    return id;
}

/*  ------------------------------------------------------------- matching */

static uint32_t jet_node(av_arena *a, uint32_t idbits, uint32_t inner) {
    uint32_t n = av_app(a, inner, inner);
    if (n == AV_NONE) return AV_NONE;
    arena_set(a, n, (av_node){ (AV_JET << AV_TAG_SHIFT) | idbits, inner });
    return n;
}

uint32_t jet_wrap(av_arena *a, uint32_t id, uint32_t inner) {
    return jet_node(a, id, inner);
}

/*  Trees by identity, for the matcher: each node, seen through views, gets
 *  a canonical id, a leaf its interned node and an application the pair of
 *  its children's ids, so two nodes are the same tree exactly when their
 *  ids are equal.  The memo and the pair table last a whole match, so
 *  canonicalizing the program and the jets' terms costs their nodes once,
 *  with no budget to run past: an av_equal with a budget on the jet's size
 *  refused a program whose copy of the term shared less, 92 templates on
 *  front1's own source. */
typedef struct {
    nmap memo;                  /* viewed node -> canonical id */
    uint64_t *key;              /* (left id, right id) + 1, 0 empty */
    uint32_t *val;
    size_t cap, n;
    uint32_t next;              /* the next application's id */
} canon_tab;

static void canon_free(canon_tab *c) {
    nmap_free(&c->memo);
    free(c->key);
    free(c->val);
}

static uint32_t canon_pair(canon_tab *c, uint32_t l, uint32_t r) {
    if (2 * (c->n + 1) > c->cap) {
        size_t ncap = c->cap ? 2 * c->cap : 1024;
        uint64_t *nk = calloc(ncap, sizeof *nk);
        uint32_t *nv = malloc(ncap * sizeof *nv);
        if (!nk || !nv) { free(nk); free(nv); return AV_NONE; }
        for (size_t k = 0; k < c->cap; k++) {
            if (!c->key[k]) continue;
            size_t j = (size_t)(c->key[k] * 0x9e3779b97f4a7c15u >> 32) & (ncap - 1);
            while (nk[j]) j = (j + 1) & (ncap - 1);
            nk[j] = c->key[k];
            nv[j] = c->val[k];
        }
        free(c->key);
        free(c->val);
        c->key = nk;
        c->val = nv;
        c->cap = ncap;
    }
    uint64_t key = ((uint64_t)l << 32 | r) + 1;
    size_t i = (size_t)(key * 0x9e3779b97f4a7c15u >> 32) & (c->cap - 1);
    while (c->key[i] && c->key[i] != key) i = (i + 1) & (c->cap - 1);
    if (!c->key[i]) {
        if (c->next == UINT32_MAX) return AV_NONE;
        c->key[i] = key;
        c->val[i] = c->next++;
        c->n++;
    }
    return c->val[i];
}

/*  t's canonical id, AV_NONE when out of memory.  Leaves keep their
 *  interned node, below AV_MAX_NODES; applications count up from it. */
static uint32_t canon_of(const av_arena *a, canon_tab *c, uint32_t t) {
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 64, top = 0;
    item *todo = malloc(cap * sizeof *todo);
    uint32_t out = AV_NONE;
    if (!todo) return AV_NONE;
    if (c->next < AV_MAX_NODES) c->next = AV_MAX_NODES;
    todo[top++] = (item){ av_view(a, t), false };
    while (top) {
        item it = todo[--top];
        uint64_t v;
        if (!it.done && nmap_get(&c->memo, it.node, &v)) continue;
        uint32_t id;
        if (av_tag(a, it.node) != AV_APP) {
            id = it.node;                       /* a leaf: interned */
        } else if (!it.done) {
            if (top + 3 > cap) {
                item *q = realloc(todo, (cap *= 2) * sizeof *q);
                if (!q) goto done;
                todo = q;
            }
            todo[top++] = (item){ it.node, true };
            todo[top++] = (item){ av_view(a, av_right(a, it.node)), false };
            todo[top++] = (item){ av_view(a, av_left(a, it.node)), false };
            continue;
        } else {
            uint64_t l, r;
            nmap_get(&c->memo, av_view(a, av_left(a, it.node)), &l);
            nmap_get(&c->memo, av_view(a, av_right(a, it.node)), &r);
            id = canon_pair(c, (uint32_t)l, (uint32_t)r);
            if (id == AV_NONE) goto done;
        }
        if (!nmap_put(&c->memo, it.node, id)) goto done;
    }
    uint64_t r;
    if (nmap_get(&c->memo, av_view(a, t), &r)) out = (uint32_t)r;
done:
    free(todo);
    return out;
}

/*  A fresh copy of t with jets wrapped; the root itself is not wrapped
 *  when skip_root, which is how a jet's own term is matched for its
 *  insides.  shared marks the jet nodes' terms as the dashboard's. */
static uint32_t match(av_arena *a, uint32_t t, bool skip_root, bool shared) {
    dmap dig = { 0 };
    nmap out = { 0 };
    canon_tab canon = { 0 };
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
        av_digest d;
        dmap_get(&dig, it.node, &d);
        uint32_t id = jet_find(a, d);
        /* a digest names a term: the node is the jet's only if it is the
         * jet's term, tree for tree */
        if (id != AV_NONE) {
            uint32_t cn = canon_of(a, &canon, it.node), cj = canon_of(a, &canon, a->jets[id].fallback);
            if (cn == AV_NONE || cj == AV_NONE) goto done;
            if (cn != cj) id = AV_NONE;
        }
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
    dmap_free(&dig);
    nmap_free(&out);
    canon_free(&canon);
    return result;
}

uint32_t av_jets_match(av_arena *a, uint32_t t) {
    return match(a, t, false, false);
}

static bool wrap_insides(av_arena *a);

typedef struct { av_digest digest; uint32_t node; } dnode;

static int by_digest(const void *x, const void *y) {
    return av_digest_cmp(((const dnode *)x)->digest, ((const dnode *)y)->digest);
}

long av_jets_ctors(av_arena *a, uint32_t t, size_t max_atoms) {
    /* the distinct subterms, by digest, and every node's size: one pass
     * each, since sizing each subterm apart is quadratic in the term */
    dmap dig = { 0 };
    nmap sizes = { 0 };
    dnode *all = NULL;
    uint32_t *cand = NULL;
    size_t n = 0, m = 0;
    long added = 0;
    bool ok = hash_all(a, av_view(a, t), &dig) && atoms_all(a, av_view(a, t), &sizes) &&
              (all = malloc((dig.n ? dig.n : 1) * sizeof *all)) != NULL;
    for (size_t i = 0; ok && i < dig.cap; i++)
        if (dig.key[i] != AV_NONE && av_tag(a, dig.key[i]) == AV_APP)
            all[m++] = (dnode){ dig.val[i], dig.key[i] };
    dmap_free(&dig);
    if (ok) qsort(all, m, sizeof *all, by_digest);
    ok = ok && (cand = malloc((m ? m : 1) * sizeof *cand)) != NULL;
    for (size_t i = 0; ok && i < m; i++) {
        if (i && av_digest_eq(all[i].digest, all[i - 1].digest)) continue;
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

static long load(av_arena *a, const char *path, size_t min_atoms, bool filter,
                 av_digest only, const char **err);

long av_jets_load(av_arena *a, const char *path, size_t min_atoms,
                  const char **err) {
    return load(a, path, min_atoms, false, (av_digest){ 0, 0 }, err);
}

long av_jets_load_only(av_arena *a, const char *path, size_t min_atoms,
                       av_digest only, const char **err) {
    return load(a, path, min_atoms, true, only, err);
}

static long load(av_arena *a, const char *path, size_t min_atoms, bool filter,
                 av_digest only, const char **err) {
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
        av_digest want;
        if (!av_hash_parse(h, &want)) { msg = "malformed hash"; break; }
        if (filter && !av_digest_eq(want, only)) continue;
        av_parse_error pe;
        uint32_t t = av_parse(a, term, len, &pe);
        if (t == AV_NONE) { msg = "unparsable dictionary term"; break; }
        char got[AV_HASH_LEN + 1];
        av_digest d;
        if (!av_structural_hash(a, t, got) || !av_hash_parse(got, &d)) { msg = "out of memory"; break; }
        if (!av_digest_eq(d, want)) { msg = "a dictionary hash does not match its term"; break; }
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
            if (fresh_jets && a->jetstats)          /* a copy of j's term */
                jetstats_made(a->jetstats, built, (uint32_t)(j - a->jets), AV_FROM_TERM);
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
            if (fresh_jets && n != AV_NONE && a->jetstats)   /* of id's residual */
                jetstats_made(a->jetstats, n, id, AV_FROM_RESIDUAL);
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
     * unfolding's.  The budget bounds distinct pairs.  The stack and the
     * set start on the C stack and move to the heap only when they grow:
     * most calls, a decoder's probe of a node against a constructor,
     * finish within a few pairs. */
    uint32_t stk0[2 * 32];
    uint64_t set0[64] = { 0 };                            /* 0 = empty */
    size_t cap = 32, top = 0, scap = 64, sn = 0;
    uint32_t *stk = stk0;
    uint64_t *set = set0;
    int out = 1;
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
            if (set != set0) free(set);
            set = ns;
            scap = ncap;
        }
        if (av_tag(a, p) != av_tag(a, q)) { out = 0; break; }
        if (av_tag(a, p) == AV_LEAF) {
            if (av_right(a, p) != av_right(a, q)) { out = 0; break; }
            continue;
        }
        if (top + 2 > cap) {
            uint32_t *s = stk == stk0 ? malloc(2 * 2 * cap * sizeof *s)
                                      : realloc(stk, 2 * 2 * cap * sizeof *s);
            if (!s) { out = -1; break; }
            if (stk == stk0) memcpy(s, stk0, sizeof stk0);
            stk = s;
            cap *= 2;
        }
        stk[2 * top] = av_left(a, p);
        stk[2 * top + 1] = av_left(a, q);
        top++;
        stk[2 * top] = av_right(a, p);
        stk[2 * top + 1] = av_right(a, q);
        top++;
    }
    if (stk != stk0) free(stk);
    if (set != set0) free(set);
    return out;
}
