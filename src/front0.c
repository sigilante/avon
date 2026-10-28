/**  front0.c
 *
 *  Running the SKIjack-0 front end.  The front end consists of one term,
 *  `front`, that takes a program as a list of 7-bit character codes and
 *  reduces to every name's closed term: ROk (OCons name tm ..) or RErr.
 *  A refusal may carry its class, a numeral (`RErr n`, the full language's
 *  front end), printed after it; SKIjack-0's `RErr` carries none.
 *  The input is built in the arena, each code's datum once and shared,
 *  and the result is read by probing---a Scott datum applied to one marker
 *  per constructor returns its own marker applied to its fields---into
 *  lines of a name and its term's hash.  No term is rebuilt.
 *
 *  The front end's work happens inside the probes, lazily, so unlike
 *  av_peel's these collect.  Every node the reader holds sits on one stack
 *  that a registered reduction record evacuates, and the memo of hashed
 *  nodes follows each collection.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "jets.h"

/*  The reader's stack entry: a node to read, or a node whose two fields'
 *  digests are on the digest stack and are to be joined into its own. */
enum { READ, JOIN };

typedef struct {
    av_arena *a;
    uint32_t *node;             /* rooted: the collector moves these      */
    uint8_t  *kind;
    size_t    n, cap;
    av_digest *dig;             /* digests of the terms read so far       */
    size_t    nd, dcap;
    dmap      memo;             /* node -> digest, remapped on collection */
    nmap      xmemo;            /* node -> emitted term's id, likewise    */
    ski_leaf  mark[5];          /* the markers' leaf ids                  */
    uint32_t  marknode[5];      /* rooted too: a collection moves leaves */
    uint64_t  steps, tmpl_calls, dispatches, fused, word_ops, bit_ops, fix_calls, joins;
    unsigned  k;                /* the last probe's field count           */
    bool      lost;             /* a remap ran out of memory              */
} reader;

static void roots(av_gc *g, void *ctx) {
    reader *r = ctx;
    for (size_t i = 0; i < r->n; i++) r->node[i] = av_gc_evac(g, r->node[i]);
    for (unsigned i = 0; i < 5; i++) r->marknode[i] = av_gc_evac(g, r->marknode[i]);
}

static void after(av_gc *g, void *ctx) {
    reader *r = ctx;
    dmap old = r->memo, fresh = { 0 };
    for (size_t i = 0; i < old.cap; i++) {
        if (old.key[i] == AV_NONE) continue;
        uint32_t j = av_gc_forwarded(g, old.key[i]);
        if (j != AV_NONE && !dmap_put(&fresh, j, old.val[i])) r->lost = true;
    }
    dmap_free(&old);
    r->memo = fresh;
    nmap xold = r->xmemo, xfresh = { 0 };
    for (size_t i = 0; i < xold.cap; i++) {
        if (xold.key[i] == AV_NONE) continue;
        uint32_t j = av_gc_forwarded(g, xold.key[i]);
        if (j != AV_NONE && !nmap_put(&xfresh, j, xold.val[i])) r->lost = true;
    }
    nmap_free(&xold);
    r->xmemo = xfresh;
}

static bool push(reader *r, uint32_t node, uint8_t kind) {
    if (r->n == r->cap) {
        size_t cap = r->cap ? 2 * r->cap : 1024;
        uint32_t *nd = realloc(r->node, cap * sizeof *nd);
        if (!nd) return false;
        r->node = nd;
        uint8_t *kd = realloc(r->kind, cap * sizeof *kd);
        if (!kd) return false;
        r->kind = kd;
        r->cap = cap;
    }
    r->node[r->n] = node;
    r->kind[r->n++] = kind;
    return true;
}

static bool push_digest(reader *r, av_digest d) {
    if (r->nd == r->dcap) {
        size_t cap = r->dcap ? 2 * r->dcap : 1024;
        av_digest *q = realloc(r->dig, cap * sizeof *q);
        if (!q) return false;
        r->dig = q;
        r->dcap = cap;
    }
    r->dig[r->nd++] = d;
    return true;
}

/*  A constructor that may carry no field or one: RErr, with or without
 *  its class; or one field or two: ROk, with or without the templates. */
#define ZERO_OR_ONE 9u
#define ONE_OR_TWO  10u

/*  Probe the node on top of the stack, which is popped, as a datum of a
 *  type whose constructor i has fields[i] fields, or no field or one where
 *  fields[i] is ZERO_OR_ONE; they are pushed, the last first, so the first
 *  is on top, and r->k is their count.  Returns the constructor, or -1. */
static int probe(reader *r, unsigned nctors, const unsigned *fields, const av_opts *o,
                 const char **err) {
    av_arena *a = r->a;
    uint32_t t = r->node[--r->n];
    for (unsigned i = 0; i < nctors; i++) {
        t = av_app(a, t, r->marknode[i]);
        if (t == AV_NONE) { *err = "out of memory"; return -1; }
    }
    av_opts po = *o;
    po.whnf_only = true;
    /* the probes share the run's fuel: --fuel bounds the read, not each
     * probe of it */
    if (o->max_steps != UINT64_MAX)
        po.max_steps = r->steps < o->max_steps ? o->max_steps - r->steps : 0;
    av_result res = av_reduce(a, t, &po);
    r->steps += res.steps;
    r->tmpl_calls += res.tmpl_calls;
    r->dispatches += res.dispatches;
    r->fused += res.fused;
    r->word_ops += res.word_ops;
    r->bit_ops += res.bit_ops;
    r->fix_calls += res.fix_calls;
    r->joins += res.joins;
    if (res.status != AV_WHNF && res.status != AV_NORMAL) {
        *err = av_status_name(res.status);
        return -1;
    }
    uint32_t spine[8];
    unsigned k = 0;
    uint32_t h = av_view(a, res.term);
    while (av_tag(a, h) == AV_APP) {
        if (k == 8) { *err = "a constructor carried too many fields"; return -1; }
        spine[k++] = av_right(a, h);
        h = av_view(a, av_left(a, h));
    }
    ski_leaf id = av_tag(a, h) == AV_LEAF ? av_right(a, h) : AV_NONE;
    unsigned w = 0;
    while (w < nctors && r->mark[w] != id) w++;
    if (w == nctors) { *err = "the head is not a marker: not a value of this type"; return -1; }
    if (fields[w] == ZERO_OR_ONE ? k > 1 : fields[w] == ONE_OR_TWO ? k < 1 || k > 2 : k != fields[w]) {
        *err = "a constructor with the wrong number of fields";
        return -1;
    }
    r->k = k;
    for (unsigned i = 0; i < k; i++)            /* spine[0] is the last field */
        if (!push(r, spine[i], READ)) { *err = "out of memory"; return -1; }
    return (int)w;
}

static const unsigned F_RESULT[2] = { ONE_OR_TWO, ZERO_OR_ONE }; /* ROk outs [tpls] | RErr [nat] */
static const unsigned F_TPLS[2]   = { 0, 2 };           /* TpNil | TpCons tpl .   */
static const unsigned F_TPL[1]    = { 4 };              /* Tpl tm nat tm tms      */
static const unsigned F_TMS[2]    = { 0, 2 };           /* TmNil | TmCons tm tms  */
static const unsigned F_NAT[2]    = { 0, 1 };           /* Zero | Suc nat         */
static const unsigned F_OUTS[2]   = { 0, 3 };           /* ONil | OCons name tm . */
static const unsigned F_NAME[2]   = { 0, 2 };           /* NNil | NCons code name */
static const unsigned F_CODE[1]   = { 7 };              /* Code b6 .. b0          */
static const unsigned F_BIT[2]    = { 0, 0 };           /* Lo | Hi                */
static const unsigned F_TM[5]     = { 0, 0, 0, 1, 1 };  /* TS TK TI TV nat, TA ap */
static const unsigned F_AP[1]     = { 2 };              /* Ap tm tm               */

/*  The name on top of the stack, into buf (NUL-terminated): at most
 *  NAME_MAX_LEN characters, none of them a control character or a space, as
 *  the output is a line per name and a tab before its hash. */
#define NAME_MAX_LEN 65536
static bool read_name(reader *r, const av_opts *o, char **buf, size_t *cap,
                      const char **err) {
    size_t len = 0;
    for (;;) {
        int c = probe(r, 2, F_NAME, o, err);
        if (c < 0) return false;
        if (len + 1 >= *cap) {
            size_t ncap = *cap ? 2 * *cap : 64;
            char *q = realloc(*buf, ncap);
            if (!q) { *err = "out of memory"; return false; }
            *buf = q;
            *cap = ncap;
        }
        if (c == 0) { (*buf)[len] = '\0'; return true; }
        if (len == NAME_MAX_LEN) { *err = "a name longer than 65536 characters"; return false; }
        if (probe(r, 1, F_CODE, o, err) < 0) return false;  /* its bits; the rest below */
        unsigned ch = 0;
        for (int i = 0; i < 7; i++) {
            int b = probe(r, 2, F_BIT, o, err);
            if (b < 0) return false;
            ch = ch << 1 | (unsigned)b;
        }
        if (ch <= ' ' || ch == 0x7f) { *err = "a name holding a control character or a space"; return false; }
        (*buf)[len++] = (char)ch;
    }
}

/*  The term on top of the stack to its digest, each node read once:
 *  a node is replaced by a JOIN of itself, then read; an atom's digest is
 *  its name's, an application's joins its two fields' digests. */
static bool read_term(reader *r, const av_opts *o, av_digest *digest, const char **err) {
    av_arena *a = r->a;
    const av_digest atom[3] = { digest_leaf("S"), digest_leaf("K"), digest_leaf("I") };
    size_t base = r->n - 1, dbase = r->nd;
    while (r->n > base) {
        size_t top = r->n - 1;
        uint32_t node = av_res(a, r->node[top]);
        av_digest d;
        if (r->kind[top] == JOIN) {
            r->n--;
            av_digest x = r->dig[--r->nd], f = r->dig[--r->nd];
            d = digest_app(f, x);
        } else if (dmap_get(&r->memo, node, &d)) {
            r->n--;
            if (!push_digest(r, d)) { *err = "out of memory"; return false; }
            continue;
        } else {
            r->node[top] = node;
            r->kind[top] = JOIN;
            if (!push(r, node, READ)) { *err = "out of memory"; return false; }
            int c = probe(r, 5, F_TM, o, err);
            if (c < 0) return false;
            if (c == 3) { *err = "a variable in a closed term"; return false; }
            if (c == 4) {                       /* TA ap: read Ap e f's two */
                if (probe(r, 1, F_AP, o, err) < 0) return false;
                continue;
            }
            node = av_res(a, r->node[--r->n]);  /* an atom: its JOIN is done */
            d = atom[c];
        }
        if (!dmap_put(&r->memo, node, d) || !push_digest(r, d)) {
            *err = "out of memory";
            return false;
        }
    }
    if (r->nd != dbase + 1) { *err = "the reader lost its place"; return false; }
    *digest = r->dig[--r->nd];
    return true;
}

/*  ------------------------------------------------------------ emitting
 *
 *  With --emit, the terms a front end gives are kept, not only hashed: in
 *  a table of their own, hash-consed, outside the arena, since the probes
 *  that read them collect.  A leaf is S, K, I or a variable; a closed
 *  node carries its digest. */
enum { X_S, X_K, X_I, X_VAR };          /* a leaf's code; X_VAR + n: TV n */
#define X_LEAF UINT32_MAX

typedef struct {
    uint32_t *l, *r;                    /* a leaf: l is X_LEAF, r its code */
    av_digest *d;                       /* closed nodes' digests */
    uint8_t  *open;
    size_t    n, cap;
    uint64_t *hk;                       /* (l, r) + 1 -> id, 0 empty */
    uint32_t *hv;
    size_t    hn, hcap;
} xtab;

static void xtab_free(xtab *x) {
    free(x->l); free(x->r); free(x->d); free(x->open); free(x->hk); free(x->hv);
    memset(x, 0, sizeof *x);
}

static size_t xslot(uint64_t k, size_t cap) { return (size_t)(k * 0x9e3779b97f4a7c15u >> 20) & (cap - 1); }

/*  The node (l, r), made once: AV_NONE out of memory. */
static uint32_t xcons(xtab *x, uint32_t l, uint32_t r) {
    if (2 * (x->hn + 1) > x->hcap) {
        size_t cap = x->hcap ? 2 * x->hcap : 1024;
        uint64_t *k = calloc(cap, sizeof *k);
        uint32_t *v = malloc(cap * sizeof *v);
        if (!k || !v) { free(k); free(v); return AV_NONE; }
        for (size_t i = 0; i < x->hcap; i++) {
            if (!x->hk[i]) continue;
            size_t s = xslot(x->hk[i], cap);
            while (k[s]) s = (s + 1) & (cap - 1);
            k[s] = x->hk[i];
            v[s] = x->hv[i];
        }
        free(x->hk); free(x->hv);
        x->hk = k; x->hv = v; x->hcap = cap;
    }
    uint64_t key = ((uint64_t)l << 32 | r) + 1;
    size_t s = xslot(key, x->hcap);
    while (x->hk[s] && x->hk[s] != key) s = (s + 1) & (x->hcap - 1);
    if (x->hk[s]) return x->hv[s];
    if (x->n == x->cap) {
        size_t cap = x->cap ? 2 * x->cap : 1024;
        uint32_t *nl = realloc(x->l, cap * sizeof *nl);
        if (nl) x->l = nl;
        uint32_t *nr = realloc(x->r, cap * sizeof *nr);
        if (nr) x->r = nr;
        av_digest *nd = realloc(x->d, cap * sizeof *nd);
        if (nd) x->d = nd;
        uint8_t *no = realloc(x->open, cap);
        if (no) x->open = no;
        if (!nl || !nr || !nd || !no) return AV_NONE;
        x->cap = cap;
    }
    uint32_t id = (uint32_t)x->n++;
    x->l[id] = l;
    x->r[id] = r;
    if (l == X_LEAF) {
        static const char *const ski[3] = { "S", "K", "I" };
        x->open[id] = r >= X_VAR;
        if (r < X_VAR) x->d[id] = digest_leaf(ski[r]);
    } else {
        x->open[id] = x->open[l] | x->open[r];
        if (!x->open[id]) x->d[id] = digest_app(x->d[l], x->d[r]);
    }
    x->hk[s] = key;
    x->hv[s] = id;
    x->hn++;
    return id;
}

/*  The numeral on top of the stack, popped. */
static bool read_nat(reader *r, const av_opts *o, unsigned long *v, const char **err) {
    for (*v = 0;; ++*v) {
        int c = probe(r, 2, F_NAT, o, err);
        if (c < 0) return false;
        if (c == 0) return true;
        if (*v == 1u << 24) { *err = "a numeral past 2^24 in a template"; return false; }
    }
}

/*  The term on top of the stack, popped, into x: its id.  A variable is
 *  refused unless open_ok.  Each node read once, as read_term reads. */
static bool read_x(reader *r, const av_opts *o, xtab *x, bool open_ok, uint32_t *idp,
                   const char **err) {
    av_arena *a = r->a;
    size_t base = r->n - 1, vcap = 64, nv = 0;
    uint32_t *val = malloc(vcap * sizeof *val);
    if (!val) { *err = "out of memory"; return false; }
    bool ok = false;
    while (r->n > base) {
        size_t top = r->n - 1;
        uint32_t node = av_res(a, r->node[top]), id;
        uint64_t v;
        if (r->kind[top] == JOIN) {
            r->n--;
            uint32_t f = val[nv - 2], y = val[nv - 1];
            nv -= 2;
            id = xcons(x, f, y);
        } else if (nmap_get(&r->xmemo, node, &v)) {
            r->n--;
            id = (uint32_t)v;
            node = AV_NONE;                     /* known: not put again */
        } else {
            r->node[top] = node;
            r->kind[top] = JOIN;
            if (!push(r, node, READ)) { *err = "out of memory"; goto done; }
            int c = probe(r, 5, F_TM, o, err);
            if (c < 0) goto done;
            if (c == 4) {                       /* TA ap: read Ap e f's two */
                if (probe(r, 1, F_AP, o, err) < 0) goto done;
                continue;
            }
            unsigned long n = 0;
            if (c == 3) {                       /* TV n: its numeral is on top */
                if (!open_ok) { *err = "a variable in a closed term"; goto done; }
                if (!read_nat(r, o, &n, err)) goto done;
            }
            node = av_res(a, r->node[--r->n]);  /* the leaf's JOIN is done */
            id = xcons(x, X_LEAF, c == 3 ? X_VAR + (uint32_t)n : (uint32_t)c);
        }
        if (id == AV_NONE) { *err = "out of memory"; goto done; }
        if (node != AV_NONE && !nmap_put(&r->xmemo, node, id)) {
            *err = "out of memory";
            goto done;
        }
        if (nv == vcap) {
            uint32_t *q = realloc(val, (vcap *= 2) * sizeof *q);
            if (!q) { *err = "out of memory"; goto done; }
            val = q;
        }
        val[nv++] = id;
    }
    if (nv != 1) { *err = "the reader lost its place"; goto done; }
    *idp = val[0];
    ok = true;
done:
    free(val);
    return ok;
}

static void xhash(const xtab *x, uint32_t id, char out[AV_HASH_LEN + 1]) {
    snprintf(out, AV_HASH_LEN + 1, AV_HASH_VERSION ":%016llx%016llx",
             (unsigned long long)x->d[id].hi, (unsigned long long)x->d[id].lo);
}

/*  A closed term's leaves, counted as a tree, saturating. */
static bool xatoms(const xtab *x, uint32_t root, uint64_t *atoms) {
    uint64_t *at = malloc(x->n * sizeof *at);
    uint8_t *seen = calloc(x->n, 1);
    uint32_t *todo = malloc(64 * sizeof *todo);
    size_t cap = 64, top = 0;
    bool ok = at && seen && todo;
    if (ok) todo[top++] = root;
    while (ok && top) {
        uint32_t id = todo[top - 1];
        if (seen[id]) { top--; continue; }
        if (x->l[id] == X_LEAF) {
            at[id] = 1;
        } else if (!seen[x->l[id]] || !seen[x->r[id]]) {
            if (top + 2 > cap) {
                uint32_t *q = realloc(todo, (cap *= 2) * sizeof *q);
                if (!q) { ok = false; break; }
                todo = q;
            }
            todo[top++] = x->r[id];
            todo[top++] = x->l[id];
            continue;
        } else {
            uint64_t s = at[x->l[id]] + at[x->r[id]];
            at[id] = s < at[x->l[id]] ? UINT64_MAX : s;
        }
        seen[id] = 1;
        top--;
    }
    if (ok) *atoms = at[root];
    free(at);
    free(seen);
    free(todo);
    return ok;
}

/*  A closed term in the DAG form, each node once, children first. */
static bool xdag(const xtab *x, uint32_t root, FILE *f) {
    uint32_t *local = malloc(x->n * sizeof *local);
    uint32_t *todo = malloc(64 * sizeof *todo);
    size_t cap = 64, top = 0;
    uint32_t next = 0;
    bool ok = local && todo;
    if (ok) {
        for (size_t i = 0; i < x->n; i++) local[i] = UINT32_MAX;
        fputs("dag", f);
        todo[top++] = root;
    }
    while (ok && top) {
        uint32_t id = todo[top - 1];
        if (local[id] != UINT32_MAX) { top--; continue; }
        if (x->l[id] == X_LEAF) {
            static const char ski[3] = { 'S', 'K', 'I' };
            fprintf(f, " %u=%c", next, ski[x->r[id]]);
        } else if (local[x->l[id]] == UINT32_MAX || local[x->r[id]] == UINT32_MAX) {
            if (top + 2 > cap) {
                uint32_t *q = realloc(todo, (cap *= 2) * sizeof *q);
                if (!q) { ok = false; break; }
                todo = q;
            }
            todo[top++] = x->r[id];
            todo[top++] = x->l[id];
            continue;
        } else {
            fprintf(f, " %u=%u.%u", next, local[x->l[id]], local[x->r[id]]);
        }
        local[id] = next++;
        top--;
    }
    if (ok) fprintf(f, " @%u", local[root]);
    free(local);
    free(todo);
    return ok;
}

/*  A body in the loader's prefix form: ` before an application, v<n> a
 *  formal, #<hash> a reference, refs[n - nf] for TV n past the formals. */
static bool xbody(const xtab *x, uint32_t id, unsigned long nf, const uint32_t *refs, size_t nrefs,
                  FILE *f, size_t limit) {
    uint32_t *todo = malloc(64 * sizeof *todo);
    size_t cap = 64, top = 0, written = 0;
    bool ok = todo != NULL;
    if (ok) todo[top++] = id;
    while (ok && top) {
        uint32_t n = todo[--top];
        if (++written > limit) { ok = false; break; }
        if (x->l[n] != X_LEAF) {
            fputc('`', f);
            if (top + 2 > cap) {
                uint32_t *q = realloc(todo, (cap *= 2) * sizeof *q);
                if (!q) { ok = false; break; }
                todo = q;
            }
            todo[top++] = x->r[n];
            todo[top++] = x->l[n];
            continue;
        }
        if (x->r[n] < X_VAR) {
            static const char ski[3] = { 'S', 'K', 'I' };
            fputc(ski[x->r[n]], f);
        } else if (x->r[n] - X_VAR < nf) {
            fprintf(f, "v%lu", (unsigned long)(x->r[n] - X_VAR));
        } else if (x->r[n] - X_VAR - nf < nrefs) {
            uint32_t ref = refs[x->r[n] - X_VAR - nf];
            fprintf(f, "#%016llx%016llx", (unsigned long long)x->d[ref].hi,
                    (unsigned long long)x->d[ref].lo);
        } else {
            ok = false;                         /* a reference past the list */
            break;
        }
        if (top) fputc(' ', f);
    }
    free(todo);
    return ok;
}

/*  Whether a body names a formal, TV n with n < nf; true out of memory,
 *  so the body is kept. */
static bool xformal(const xtab *x, uint32_t id, unsigned long nf) {
    size_t cap = 64, top = 0;
    uint32_t *todo = malloc(cap * sizeof *todo);
    bool found = todo == NULL;
    if (todo) todo[top++] = id;
    while (!found && top) {
        uint32_t n = todo[--top];
        if (!x->open[n]) continue;
        if (x->l[n] == X_LEAF) { found = x->r[n] - X_VAR < nf; continue; }
        if (top + 2 > cap) {
            uint32_t *q = realloc(todo, (cap *= 2) * sizeof *q);
            if (!q) { found = true; break; }
            todo = q;
        }
        todo[top++] = x->r[n];
        todo[top++] = x->l[n];
    }
    free(todo);
    return found;
}

/*  An η-template, H v0 .. v(nf-1) with H naming no formal, instantiates
 *  H xs to H xs forever: the loader skips it, and Python's templates leave
 *  it out, so a key two rules share keeps its other rule's body. */
static bool xeta(const xtab *x, uint32_t body, unsigned long nf) {
    uint32_t id = body;
    for (unsigned long i = nf; i-- > 0;) {
        if (x->l[id] == X_LEAF || x->l[x->r[id]] != X_LEAF || x->r[x->r[id]] != X_VAR + i)
            return false;
        id = x->l[id];
    }
    return !xformal(x, id, nf);
}

/*  ROk's templates, on top of the stack, popped: DIR/templates.tsv and
 *  DIR/template_terms.tsv, each key and each reference once. */
static bool emit_templates(reader *r, const av_opts *o, xtab *x, FILE *tf, FILE *rf,
                           long *count, const char **err) {
    uint8_t *done = NULL;                       /* per id: 1 key, 2 reference */
    size_t dcap = 0;
    uint32_t *refs = NULL;
    size_t rcap = 0;
    bool ok = false;
    for (;;) {
        int c = probe(r, 2, F_TPLS, o, err);
        if (c < 0) goto out;
        if (c == 0) break;
        if (probe(r, 1, F_TPL, o, err) < 0) goto out;      /* key nf body refs; the rest below */
        uint32_t key, body;
        unsigned long nf;
        if (!read_x(r, o, x, false, &key, err) || !read_nat(r, o, &nf, err) ||
            !read_x(r, o, x, true, &body, err))
            goto out;
        size_t nrefs = 0;
        for (;;) {
            int t = probe(r, 2, F_TMS, o, err);
            if (t < 0) goto out;
            if (t == 0) break;
            if (nrefs == rcap) {
                uint32_t *q = realloc(refs, (rcap = rcap ? 2 * rcap : 64) * sizeof *q);
                if (!q) { *err = "out of memory"; goto out; }
                refs = q;
            }
            if (!read_x(r, o, x, false, &refs[nrefs++], err)) goto out;
        }
        if (dcap < x->n) {
            size_t ncap = 2 * x->n;
            uint8_t *q = realloc(done, ncap);
            if (!q) { *err = "out of memory"; goto out; }
            memset(q + dcap, 0, ncap - dcap);
            done = q;
            dcap = ncap;
        }
        if (!nf || (done[key] & 1) || xeta(x, body, nf)) continue;    /* no formals: none */
        done[key] |= 1;
        char h[AV_HASH_LEN + 1];
        xhash(x, key, h);
        fprintf(tf, "%s\tfront1\t-\t%lu\t", h, nf);
        for (unsigned long i = 0; i < nf; i++) fprintf(tf, i ? ",%lu" : "%lu", i);
        fputc('\t', tf);
        if (!xbody(x, body, nf, refs, nrefs, tf, (size_t)1 << 24)) {
            *err = "a template's body past its references or too large";
            goto out;
        }
        fputc('\n', tf);
        (*count)++;
        for (size_t i = 0; i < nrefs; i++) {
            if (done[refs[i]] & 2) continue;
            done[refs[i]] |= 2;
            uint64_t atoms = 0;
            xhash(x, refs[i], h);
            if (!xatoms(x, refs[i], &atoms)) { *err = "out of memory"; goto out; }
            fprintf(rf, "%s\t%llu\t", h, (unsigned long long)atoms);
            if (!xdag(x, refs[i], rf)) { *err = "out of memory"; goto out; }
            fputc('\n', rf);
        }
    }
    ok = true;
out:
    free(done);
    free(refs);
    return ok;
}

uint32_t av_front0_input(av_arena *a, const av_front0 *f, const char *src, size_t len) {
    uint32_t codes[128] = { 0 };
    for (int i = 0; i < 128; i++) codes[i] = AV_NONE;
    uint32_t list = f->snil;
    for (size_t i = len; i-- > 0;) {
        unsigned ch = (unsigned char)src[i];
        if (ch > 127) return AV_NONE;
        if (codes[ch] == AV_NONE) {
            uint32_t c = f->code;
            for (int b = 6; b >= 0 && c != AV_NONE; b--)
                c = av_app(a, c, (ch >> b & 1) ? f->hi : f->lo);
            codes[ch] = c;
        }
        list = codes[ch] == AV_NONE ? AV_NONE : av_app(a, av_app(a, f->scons, codes[ch]), list);
        if (list == AV_NONE) return AV_NONE;
    }
    return av_app(a, f->front, list);
}

int av_front0_read(av_arena *a, uint32_t t, const av_opts *o, FILE *out,
                   uint64_t *steps, av_result *tally, const char **err) {
    return av_front0_read_emit(a, t, o, out, NULL, NULL, steps, tally, err);
}

static FILE *emit_open(const char *dir, const char *file) {
    char path[4096];
    snprintf(path, sizeof path, "%s/%s", dir, file);
    return fopen(path, "w");
}

int av_front0_read_emit(av_arena *a, uint32_t t, const av_opts *o, FILE *out,
                        const char *emit, long *ntemplates, uint64_t *steps, av_result *tally,
                        const char **err) {
    reader r = { .a = a };
    av_active me = { roots, after, &r, a->active };
    int rc = -1;
    char *name = NULL;
    size_t ncap = 0;
    xtab x = { 0 };
    FILE *tf = NULL, *rf = NULL, *nf = NULL;
    if (ntemplates) *ntemplates = 0;
    if (emit && (!(tf = emit_open(emit, "templates.tsv")) ||
                 !(rf = emit_open(emit, "template_terms.tsv")) ||
                 !(nf = emit_open(emit, "terms.tsv")))) {
        *err = "cannot write the --emit directory's files";
        goto done;
    }
    for (unsigned i = 0; i < 5; i++) {
        char nm[8];
        int n = snprintf(nm, sizeof nm, "@%u", i);
        r.marknode[i] = av_leaf(a, nm, (size_t)n);
        if (r.marknode[i] == AV_NONE) { *err = "out of memory"; return -1; }
        r.mark[i] = av_right(a, r.marknode[i]);
    }
    a->active = &me;
    if (!push(&r, t, READ)) { *err = "out of memory"; goto done; }
    int c = probe(&r, 2, F_RESULT, o, err);
    if (c < 0) goto done;
    unsigned okfields = r.k;                    /* ROk outs, or ROk outs tpls */
    if (c == 0 && emit && okfields != 2) {
        *err = "this front end's ROk carries no templates to emit";
        goto done;
    }
    if (c == 1) {
        if (r.k == 0) { fputs("RErr\n", out); rc = 1; goto done; }
        unsigned long cls = 0;                  /* the class, a numeral    */
        for (;;) {
            int s = probe(&r, 2, F_NAT, o, err);
            if (s < 0) goto done;
            if (s == 0) break;
            if (cls == 255) { *err = "a refusal's class past 255"; goto done; }
            cls++;
        }
        fprintf(out, "RErr %lu\n", cls);
        rc = 1;
        goto done;
    }
    for (;;) {
        c = probe(&r, 2, F_OUTS, o, err);
        if (c < 0) goto done;
        if (c == 0) break;
        if (!read_name(&r, o, &name, &ncap, err)) goto done;   /* the tm, rest below */
        av_digest d;
        if (emit) {                             /* kept, for terms.tsv */
            uint32_t id;
            if (!read_x(&r, o, &x, false, &id, err)) goto done;
            d = x.d[id];
            fprintf(nf, "%s\t" AV_HASH_VERSION ":%016llx%016llx\t", name,
                    (unsigned long long)d.hi, (unsigned long long)d.lo);
            if (!xdag(&x, id, nf)) { *err = "out of memory"; goto done; }
            fputc('\n', nf);
        } else if (!read_term(&r, o, &d, err)) {
            goto done;                          /* the rest below */
        }
        fprintf(out, "%s\t" AV_HASH_VERSION ":%016llx%016llx\n", name,
                (unsigned long long)d.hi, (unsigned long long)d.lo);
    }
    if (okfields == 2) {                        /* the templates, below outs */
        if (emit) {
            long count = 0;
            if (!emit_templates(&r, o, &x, tf, rf, &count, err)) goto done;
            if (ntemplates) *ntemplates = count;
        } else {
            r.n--;                              /* never read, never made */
        }
    }
    rc = r.lost ? -1 : 0;
    if (r.lost) *err = "out of memory remapping the reader's memo";
done:
    a->active = me.next;
    *steps = r.steps;
    if (tally) {
        tally->steps = r.steps;
        tally->tmpl_calls = r.tmpl_calls;
        tally->dispatches = r.dispatches;
        tally->fused = r.fused;
        tally->word_ops = r.word_ops;
        tally->bit_ops = r.bit_ops;
        tally->fix_calls = r.fix_calls;
        tally->joins = r.joins;
    }
    free(r.node);
    free(r.kind);
    free(r.dig);
    dmap_free(&r.memo);
    nmap_free(&r.xmemo);
    xtab_free(&x);
    if (tf && fclose(tf) && rc == 0) { *err = "cannot write templates.tsv"; rc = -1; }
    if (rf && fclose(rf) && rc == 0) { *err = "cannot write template_terms.tsv"; rc = -1; }
    if (nf && fclose(nf) && rc == 0) { *err = "cannot write terms.tsv"; rc = -1; }
    free(name);
    return rc;
}
