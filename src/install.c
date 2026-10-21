/**  install.c
 *
 *  Install: an encoded term---a Scott datum of S | K | I | App t u---becomes
 *  the live term it encodes, read by probing as run.decode reads it, with
 *  jets matched.  Also the unquoter's jet: UQ m = m S K I (UQA UQ),
 *  UQA f t u = f t (f u), which defines what install does; the native install
 *  is checked against it.
 */

#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "jets.h"

static const char *const TERM_CTORS[4] = { "S", "K", "I", "App" };

uint32_t av_install(av_arena *a, uint32_t datum, const av_opts *o, const char **err) {
    av_opts po = *o;
    po.strategy = AV_COPY;
    po.whnf_only = true;
    po.interp_jets = false;
    po.install_jets = false;
    po.no_collect = true;
    const char *msg = NULL;
    uint32_t t = av_decode(a, datum, 4, TERM_CTORS, 3, 50000000, &po, &msg);
    if (t == AV_NONE) { if (err) *err = msg ? msg : "the datum does not decode"; return AV_NONE; }
    /* S, K and I decode to the combinators; anything else is no term */
    for (size_t top = 1, cap = 64;;) {
        uint32_t *st = malloc(cap * sizeof *st);
        if (!st) { if (err) *err = "out of memory"; return AV_NONE; }
        st[0] = t;
        bool ok = true;
        while (ok && top) {
            uint32_t x = av_view(a, st[--top]);
            if (av_tag(a, x) == AV_APP) {
                if (top + 2 > cap) {
                    uint32_t *q = realloc(st, (cap *= 2) * sizeof *q);
                    if (!q) { ok = false; break; }
                    st = q;
                }
                st[top++] = av_left(a, x);
                st[top++] = av_right(a, x);
            } else {
                ok = ski_is_comb(av_right(a, x));
            }
        }
        free(st);
        if (!ok) { if (err) *err = "the datum encodes no S, K, I term"; return AV_NONE; }
        break;
    }
    uint32_t live = av_jets_match(a, t);
    if (live == AV_NONE && err) *err = "out of memory";
    return live;
}

/*  λs k i a. v_j, j the constructor's index; App: λt u s k i a. a t u. */
static uint32_t ctor(av_arena *a, unsigned j) {
    uint32_t v[6];
    static const char *const nm[6] = { "@ct", "@cu", "@cs", "@ck", "@ci", "@ca" };
    for (unsigned i = 0; i < 6; i++) v[i] = av_leaf(a, nm[i], 3);
    uint32_t body = j < 3 ? v[2 + j] : av_app(a, av_app(a, v[5], v[0]), v[1]);
    for (unsigned i = 6; i-- > 2 && body != AV_NONE;) body = av_abstract(a, v[i], body);
    if (j == 3) {
        body = av_abstract(a, v[1], body);
        if (body != AV_NONE) body = av_abstract(a, v[0], body);
    }
    return body;
}

uint32_t av_encode(av_arena *a, uint32_t t) {
    uint32_t c[4];
    for (unsigned j = 0; j < 4; j++)
        if ((c[j] = ctor(a, j)) == AV_NONE) return AV_NONE;
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 64, top = 0;
    item *todo = malloc(cap * sizeof *todo);
    nmap m = { 0 };
    uint32_t out = AV_NONE;
    if (!todo) goto done;
    todo[top++] = (item){ av_view(a, t), false };
    while (top) {
        item it = todo[--top];
        uint64_t v;
        if (!it.done && nmap_get(&m, it.node, &v)) continue;
        uint32_t built;
        if (av_tag(a, it.node) != AV_APP) {
            ski_leaf id = av_right(a, it.node);
            if (!ski_is_comb(id)) goto done;
            built = c[id == SKI_S ? 0 : id == SKI_K ? 1 : 2];
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
            if (!nmap_get(&m, av_view(a, av_left(a, it.node)), &l) ||
                !nmap_get(&m, av_view(a, av_right(a, it.node)), &r))
                goto done;
            built = av_app(a, c[3], (uint32_t)l);
            built = built == AV_NONE ? AV_NONE : av_app(a, built, (uint32_t)r);
        }
        if (built == AV_NONE || !nmap_put(&m, it.node, built)) goto done;
    }
    uint64_t r;
    if (nmap_get(&m, av_view(a, t), &r)) out = (uint32_t)r;
done:
    free(todo);
    nmap_free(&m);
    return out;
}

/*  The normal form of t, copy mode, jets off, without collecting; AV_NONE
 *  if there is none within the budget. */
static uint32_t normal(av_arena *a, uint32_t t, uint64_t budget) {
    av_opts o = av_opts_default();
    o.strategy = AV_COPY;
    o.jets = false;
    o.max_steps = budget;
    o.no_collect = true;
    av_result r = av_reduce(a, t, &o);
    return r.status == AV_NORMAL ? r.term : AV_NONE;
}

bool av_unquote_register(av_arena *a, uint32_t uq, const char **err) {
    static const char *const samples[] = {
        "S", "K", "I", "S K", "K I", "S (K S) K", "S I I", "S (K (S I)) K",
        "S (S (K S) (S (K K) (S (K S) (S (K (S I)) K)))) (K K)",
    };
    av_root_push(a, &uq);
    bool ok = true;
    for (size_t i = 0; ok && i < sizeof samples / sizeof *samples; i++) {
        uint32_t t = av_parse(a, samples[i], strlen(samples[i]), NULL);
        uint32_t d = t == AV_NONE ? AV_NONE : av_encode(a, t);
        uint32_t nf = d == AV_NONE ? AV_NONE : normal(a, av_app(a, uq, d), 1000000);
        ok = nf != AV_NONE && av_equal(a, nf, t, 1000000) == 1;
    }
    av_root_pop(a);
    if (!ok) { if (err) *err = "the term does not unquote the sample terms"; return false; }
    char h[AV_HASH_LEN + 1];
    av_digest digest;
    if (!av_structural_hash(a, uq, h) || !av_hash_parse(h, &digest)) {
        if (err) *err = "out of memory";
        return false;
    }
    const char *why = NULL;
    uint32_t id = jet_entry_for(a, digest, av_view(a, uq), &why);
    if (id == AV_NONE) { if (err) *err = why; return false; }
    a->jets[id].unquote = true;
    return true;
}

int install_fire(av_arena *a, uint32_t datum, const av_opts *o, uint64_t host_left,
                 uint32_t *out, uint64_t *charge) {
    uint64_t p0 = a->probe_steps;
    av_opts po = *o;
    po.max_steps = host_left;
    uint32_t t = av_install(a, datum, &po, NULL);
    uint64_t spent = a->probe_steps - p0;
    if (t == AV_NONE || spent > host_left) return 0;    /* decline: UQ runs */
    *out = t;
    *charge = spent;
    return 1;
}

bool install_check(av_arena *a, uint32_t node, uint32_t datum, uint32_t out) {
    uint32_t uq = av_right(a, node);
    uint32_t t = av_app(a, uq, datum);
    if (t == AV_NONE) return true;                      /* out of memory */
    uint32_t n1 = normal(a, t, 10000000), n2 = normal(a, out, 10000000);
    if (n1 == AV_NONE || n2 == AV_NONE) return true;    /* inconclusive */
    return av_equal(a, n1, n2, 100000000) == 1;
}
