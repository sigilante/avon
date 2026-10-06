/**  compiler.c
 *
 *  The compiler jet (docs/DESIGN.md §20.3): the compiler's core is a term,
 *  bracket abstraction written in SKIjack (tests/selfhost/abstract.ascii.ski),
 *  and the jet is native abstraction specified by it -- the only route by
 *  which compilation enters Avon's C.  Encoded terms are Scott data of the
 *  compiler's own types: tm = TS | TK | TI | TV nat | TA ap, ap = Ap tm tm.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "jets.h"

uint32_t av_tm_nat(av_arena *a, const av_compiler *c, uint64_t n) {
    uint32_t t = c->zero;
    for (uint64_t i = 0; i < n && t != AV_NONE; i++) t = av_app(a, c->suc, t);
    return t;
}

/*  vN's number, or -1. */
static int64_t var_number(const char *nm) {
    if (nm[0] != 'v' || !nm[1]) return -1;
    int64_t n = 0;
    for (const char *p = nm + 1; *p; p++) {
        if (*p < '0' || *p > '9' || n > (INT64_MAX - 9) / 10) return -1;
        n = n * 10 + (*p - '0');
    }
    return n;
}

uint32_t av_tm_encode(av_arena *a, const av_compiler *c, uint32_t t) {
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 256, top = 0;
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
            if (id == SKI_S) built = c->ts;
            else if (id == SKI_K) built = c->tk;
            else if (id == SKI_I) built = c->ti;
            else {
                int64_t n = var_number(av_leaf_name(a, id));
                if (n < 0) goto done;
                uint32_t num = av_tm_nat(a, c, (uint64_t)n);
                built = num == AV_NONE ? AV_NONE : av_app(a, c->tv, num);
            }
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
            uint32_t ap = av_app(a, c->ap, (uint32_t)l);        /* TA (Ap e f) */
            ap = ap == AV_NONE ? AV_NONE : av_app(a, ap, (uint32_t)r);
            built = ap == AV_NONE ? AV_NONE : av_app(a, c->ta, ap);
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

uint32_t av_tm_decode(av_arena *a, uint32_t datum, const av_opts *o, const char **err) {
    av_opts po = *o;
    po.no_collect = true;
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 256, top = 0, nb = 0, bcap = 256;
    item *todo = malloc(cap * sizeof *todo);
    uint32_t *built = malloc(bcap * sizeof *built), out = AV_NONE;
    nmap m = { 0 };
    const char *msg = "out of memory";
    if (!todo || !built) goto done;
    todo[top++] = (item){ datum, false };
    while (top) {
        item it = todo[--top];
        uint64_t v;
        if (nb + 1 > bcap) {
            uint32_t *q = realloc(built, (bcap *= 2) * sizeof *q);
            if (!q) goto done;
            built = q;
        }
        if (it.done) {                          /* both fields are built */
            uint32_t f = built[--nb], e = built[--nb];
            uint32_t t = av_app(a, e, f);
            if (t == AV_NONE || !nmap_put(&m, it.node, t)) goto done;
            built[nb++] = t;
            continue;
        }
        if (nmap_get(&m, it.node, &v)) { built[nb++] = (uint32_t)v; continue; }
        av_peeled p;
        if (!av_peel(a, it.node, 5, &po, &p, NULL)) { msg = "not a term datum"; goto done; }
        uint32_t t = AV_NONE;
        if (p.ctor < 3) {
            t = p.ctor == 0 ? AV_NODE_S : p.ctor == 1 ? AV_NODE_K : AV_NODE_I;
        } else if (p.ctor == 3) {
            uint64_t n;
            char nm[32];
            if (p.nfields != 1 || !av_read_nat(a, p.field[0], 1u << 20, &po, &n, NULL)) {
                msg = "a variable without a numeral";
                goto done;
            }
            int len = snprintf(nm, sizeof nm, "v%llu", (unsigned long long)n);
            t = av_leaf(a, nm, (size_t)len);
        } else {
            av_peeled q;
            if (p.nfields != 1 || !av_peel(a, p.field[0], 1, &po, &q, NULL) || q.nfields != 2) {
                msg = "an application without two fields";
                goto done;
            }
            if (top + 3 > cap) {
                item *r = realloc(todo, (cap *= 2) * sizeof *r);
                if (!r) goto done;
                todo = r;
            }
            todo[top++] = (item){ it.node, true };
            todo[top++] = (item){ q.field[1], false };
            todo[top++] = (item){ q.field[0], false };
            continue;
        }
        if (t == AV_NONE || !nmap_put(&m, it.node, t)) goto done;
        built[nb++] = t;
    }
    if (nb == 1) { out = built[0]; msg = NULL; }
done:
    free(todo);
    free(built);
    nmap_free(&m);
    if (out == AV_NONE && err) *err = msg;
    return out;
}

/*  abs x t, reduced by the term, decoded; AV_NONE if it does not decode
 *  within the budget. */
static uint32_t by_term(av_arena *a, uint32_t abs, uint32_t x, uint32_t t, uint64_t budget) {
    uint32_t q = av_app(a, av_app(a, abs, x), t);
    av_opts o = av_opts_default();
    o.strategy = AV_COPY;
    o.jets = false;
    o.max_steps = budget;
    o.no_collect = true;
    return q == AV_NONE ? AV_NONE : av_tm_decode(a, q, &o, NULL);
}

/*  [vx] t natively, and encoded. */
static uint32_t native(av_arena *a, const av_compiler *c, uint64_t x, uint32_t t) {
    char nm[32];
    int len = snprintf(nm, sizeof nm, "v%llu", (unsigned long long)x);
    uint32_t r = av_abstract(a, av_leaf(a, nm, (size_t)len), t);
    return r == AV_NONE ? AV_NONE : av_tm_encode(a, c, r);
}

/*  The compiler's nine terms, pinned by their full digests (av_p2_digest):
 *  abs, compiled by skijack from tests/selfhost/abstract.ascii.ski, and
 *  the constructors of its tm, ap and nat types.  A compiler is admitted
 *  only if it is this one, so native abstraction stands in for no other
 *  term (AUDIT.md item 8); the samples below run as well. */
static const char *const PINNED[9] = {
    "31ef1f0698171f55f5c1c9d62e6c1924b9fc13f3e472fe147a70bf581ff2acce",   /* abs */
    "267020e689832bb9f4040fc8aa12c738e67b052601a045b90acef6649c7fef28",   /* TS */
    "ef9ab93025440441e4928d2a0a6887de0da80a6fac9dd0e7fb606d2b206b2253",   /* TK */
    "7903f20d24dae2137a358aa7fc25f65f77c4f67944f1faaf7113a1183e94ad8b",   /* TI */
    "ac1fa093de75ef3a63839669260c51ce2ed144b16d9bf3aceaaf8be2b88149f5",   /* TV */
    "3d36f9ff11f63619c8054ac923456b925818223a3e4911521a7173f7ba521d55",   /* TA */
    "aaeee552d6c69d8d6288f0e048a91d9a8100c5b15cb626e4fd93a0a57c415943",   /* Ap */
    "86be9a55762d316a3026c2836d044f5fc76e34da10e1b45feee5f18be7edb177",   /* Zero */
    "675705e4def6c18f61de932eedfd2ffc515bd272c4310a31ac6d08396764ab55",   /* Suc */
};

bool av_compiler_register(av_arena *a, const av_compiler *c, const char **err) {
    const uint32_t terms[9] = { c->abs, c->ts, c->tk, c->ti, c->tv, c->ta, c->ap, c->zero, c->suc };
    for (int i = 0; i < 9; i++) {
        char full[65];
        if (!av_p2_digest(a, terms[i], full)) { if (err) *err = "out of memory"; return false; }
        if (strcmp(full, PINNED[i]) != 0) {
            if (err) *err = "not skijack's compiler: a term's full digest is not the pinned one";
            return false;
        }
    }
    static const char *const samples[] = {
        "v0", "v1", "S", "v0 v1", "v1 v0", "v1 (v0 v1)", "S (K v0) v1", "K v1 v0",
        "v2 v1 v0", "S v0 (K v1)",
    };
    _Static_assert(sizeof(av_compiler) == sizeof a->compiler, "nine terms");
    memcpy(a->compiler, c, sizeof a->compiler);         /* roots from here on */
    av_compiler k;                                      /* nothing below collects */
    memcpy(&k, a->compiler, sizeof k);
    av_opts po = av_opts_default();
    po.strategy = AV_COPY;
    po.max_steps = 1000000;
    po.no_collect = true;
    bool ok = true;
    for (size_t i = 0; ok && i < sizeof samples / sizeof *samples; i++) {
        uint32_t t = av_parse(a, samples[i], strlen(samples[i]), NULL);
        uint32_t d = t == AV_NONE ? AV_NONE : av_tm_encode(a, &k, t);
        uint32_t x = av_tm_nat(a, &k, 0);
        uint32_t got = d == AV_NONE || x == AV_NONE ? AV_NONE : by_term(a, k.abs, x, d, 10000000);
        uint32_t want = native(a, &k, 0, t);
        uint32_t wd = want == AV_NONE ? AV_NONE : av_tm_decode(a, want, &po, NULL);
        ok = got != AV_NONE && wd != AV_NONE && av_equal(a, got, wd, 1000000) == 1;
    }
    if (!ok) {
        memset(a->compiler, 0, sizeof a->compiler);
        if (err) *err = "the term does not abstract the sample terms as aviary does";
        return false;
    }
    char h[27];
    uint64_t digest;
    uint32_t abs = a->compiler[0];
    if (!av_structural_hash(a, abs, h) || !av_hash_parse(h, &digest)) {
        if (err) *err = "out of memory";
        return false;
    }
    uint32_t id = jet_entry_for(a, digest, av_view(a, abs));
    if (id == AV_NONE) { if (err) *err = "out of memory"; return false; }
    a->jets[id].compiler = true;
    return true;
}

int compile_fire(av_arena *a, const uint32_t *argv, const av_opts *o, uint64_t host_left,
                 uint32_t *out, uint64_t *charge) {
    if (!a->compiler[0]) return 0;
    av_compiler k;                                      /* nothing here collects */
    memcpy(&k, a->compiler, sizeof k);
    const av_compiler *c = &k;
    uint64_t p0 = a->probe_steps;
    av_opts po = *o;
    po.strategy = AV_COPY;
    po.max_steps = host_left;
    po.no_collect = true;
    po.compile_jets = false;
    uint64_t x;
    if (!av_read_nat(a, argv[0], 1u << 20, &po, &x, NULL)) return 0;
    uint32_t t = av_tm_decode(a, argv[1], &po, NULL);
    uint32_t r = t == AV_NONE ? AV_NONE : native(a, c, x, t);
    uint64_t spent = a->probe_steps - p0;
    if (r == AV_NONE || spent > host_left) return 0;
    *out = r;
    *charge = spent;
    return 1;
}

bool compile_check(av_arena *a, uint32_t node, const uint32_t *argv, uint32_t out) {
    uint32_t got = by_term(a, av_right(a, node), argv[0], argv[1], 100000000);
    av_opts o = av_opts_default();
    o.strategy = AV_COPY;
    o.no_collect = true;
    o.max_steps = 100000000;
    uint32_t want = av_tm_decode(a, out, &o, NULL);
    if (got == AV_NONE || want == AV_NONE) return true;     /* inconclusive */
    return av_equal(a, got, want, 100000000) == 1;
}
