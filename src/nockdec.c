/**  nockdec.c
 *
 *  The transported Nock decrements, skinock's terms pinned (pin.c), and the
 *  nouns they read and write in skinock's encoding (include/avon.h, "The
 *  transported Nock decrements").  jetT decF, the Λ word: skinock's
 *  dec_transport proves it implements decC's contract on every encoded
 *  noun, so av_nock_dec_read checks the whole argument, rest of the stack
 *  included, before the jet answers for it.  jetT hoonDecBodyF, Hoon's
 *  ++dec arm: skinock's licence covers a core whatever its battery and
 *  context hold, so av_hoon_dec_read reads only the core's two cells and
 *  its sample.
 */

#include <stdint.h>
#include <stdlib.h>

#include "avon.h"
#include "jets.h"

/*  ------------------------------------------------------------- reading */

static bool app(const av_arena *a, uint32_t t, uint32_t *f, uint32_t *x) {
    t = av_view(a, t);
    if (av_tag(a, t) != AV_APP) return false;
    *f = av_left(a, t);
    *x = av_right(a, t);
    return true;
}

static bool is(const av_arena *a, uint32_t t, uint32_t leaf) {
    return av_view(a, t) == leaf;
}

/*  f x, f the leaf `leaf`: x */
static bool leaf_app(const av_arena *a, uint32_t t, uint32_t leaf, uint32_t *x) {
    uint32_t f;
    return app(a, t, &f, x) && is(a, f, leaf);
}

/*  K K */
static bool is_kk(const av_arena *a, uint32_t t) {
    uint32_t x;
    return leaf_app(a, t, AV_NODE_K, &x) && is(a, x, AV_NODE_K);
}

/*  S (K K) x: x */
static bool skk_app(const av_arena *a, uint32_t t, uint32_t *x) {
    uint32_t f, g;
    return app(a, t, &f, x) && leaf_app(a, f, AV_NODE_S, &g) && is_kk(a, g);
}

/*  Atom b = S (K K) (S (K K) (S (K K) (S I (K b)))): b */
static bool atom_read(const av_arena *a, uint32_t t, uint32_t *b) {
    uint32_t x1, x2, x3, f, si, kb;
    if (!skk_app(a, t, &x1) || !skk_app(a, x1, &x2) || !skk_app(a, x2, &x3)) return false;
    if (!app(a, x3, &f, &kb) || !leaf_app(a, f, AV_NODE_S, &si) || !is(a, si, AV_NODE_I))
        return false;
    return leaf_app(a, kb, AV_NODE_K, b);
}

/*  Cell h t = K (S (K K) (S (K K) (pairT h t))): h and t */
static bool cell_read(const av_arena *a, uint32_t t, uint32_t *h, uint32_t *tl) {
    uint32_t y1, y2, p;
    return leaf_app(a, t, AV_NODE_K, &y1) && skk_app(a, y1, &y2) && skk_app(a, y2, &p) &&
           pin_pair_read(a, p, h, tl);
}

/*  Form h t k = K (K (S (K K) (S (pairT h t) (K k)))), a cell carrying
 *  code: h and t; k, the code, is not read */
static bool form_read(const av_arena *a, uint32_t t, uint32_t *h, uint32_t *tl) {
    uint32_t x1, x2, z, f, kk, p, k;
    return leaf_app(a, t, AV_NODE_K, &x1) && leaf_app(a, x1, AV_NODE_K, &x2) &&
           skk_app(a, x2, &z) && app(a, z, &f, &kk) && leaf_app(a, f, AV_NODE_S, &p) &&
           leaf_app(a, kk, AV_NODE_K, &k) && pin_pair_read(a, p, h, tl);
}

/*  A cell, with code or without: h and t */
static bool any_cell_read(const av_arena *a, uint32_t t, uint32_t *h, uint32_t *tl) {
    return cell_read(a, t, h, tl) || form_read(a, t, h, tl);
}

/*  A canonical bit list, least significant first: K, or K (pairT bit
 *  rest), a bit K (1) or K I (0), the last bit 1.  *len its bits, *n the
 *  value of the first 32. */
static bool bits_read(const av_arena *a, uint32_t t, uint32_t *n, size_t *len) {
    uint32_t v = 0, p, bit, x;
    size_t i = 0;
    bool last = true;
    while (!is(a, t, AV_NODE_K)) {
        if (!leaf_app(a, t, AV_NODE_K, &p) || !pin_pair_read(a, p, &bit, &t)) return false;
        if (is(a, bit, AV_NODE_K)) last = true;
        else if (leaf_app(a, bit, AV_NODE_K, &x) && is(a, x, AV_NODE_I)) last = false;
        else return false;
        if (last && i < 32) v |= 1u << i;
        i++;
    }
    *n = v;
    *len = i;
    return last;                            /* no trailing 0: canonical */
}

/*  Whether t is the encoding of a noun, every node of it: an Atom of a
 *  canonical bit list, or a Cell of two.  A node shared is checked once. */
static bool noun_ok(const av_arena *a, uint32_t t) {
    nmap seen = { 0 };
    size_t cap = 64, top = 0;
    uint32_t *todo = malloc(cap * sizeof *todo);
    bool ok = todo != NULL;
    if (ok) todo[top++] = t;
    while (ok && top) {
        uint32_t x = av_view(a, todo[--top]), b, h, tl, n;
        size_t len;
        uint64_t v;
        if (nmap_get(&seen, x, &v)) continue;
        if (!(ok = nmap_put(&seen, x, 1))) break;
        if (atom_read(a, x, &b)) {
            ok = bits_read(a, b, &n, &len);
            continue;
        }
        if (!(ok = cell_read(a, x, &h, &tl))) break;
        if (top + 2 > cap) {
            uint32_t *q = realloc(todo, (cap *= 2) * sizeof *q);
            if (!(ok = q != NULL)) break;
            todo = q;
        }
        todo[top++] = tl;
        todo[top++] = h;
    }
    free(todo);
    nmap_free(&seen);
    return ok;
}

int av_nock_dec_read(const av_arena *a, uint32_t t, uint32_t *k, uint32_t *rest) {
    uint32_t b, h, r, x, n;
    size_t len;
    if (!noun_ok(a, t)) return 0;
    if (atom_read(a, t, &b)) return 2;                  /* an atom: no stack */
    if (!cell_read(a, t, &h, &r)) return 0;
    if (cell_read(a, h, &x, &x)) return 2;              /* a cell at the head */
    if (!atom_read(a, h, &b) || !bits_read(a, b, &n, &len)) return 0;
    if (len > 32) return 0;                             /* past the jet: its term */
    if (n == 0) return 2;                               /* underflow */
    *k = n - 1;
    *rest = r;
    return 1;
}

/*  Hoon's ++dec reads the gate core [bat [sam ctx]] at axis 6, the
 *  sample.  Either cell may carry code, as a compiled core's do, and
 *  neither bat nor ctx is read. */
int av_hoon_dec_read(const av_arena *a, uint32_t t, uint32_t *k) {
    uint32_t b, bat, tl, sam, ctx, x, n;
    size_t len;
    if (atom_read(a, t, &b)) return bits_read(a, b, &n, &len) ? 2 : 0;   /* no sample */
    if (!any_cell_read(a, t, &bat, &tl)) return 0;
    if (atom_read(a, tl, &b)) return bits_read(a, b, &n, &len) ? 2 : 0;  /* [bat atom] */
    if (!any_cell_read(a, tl, &sam, &ctx)) return 0;
    if (any_cell_read(a, sam, &x, &x)) return 0;        /* off the domain: the arm diverges */
    if (!atom_read(a, sam, &b) || !bits_read(a, b, &n, &len)) return 0;
    if (len > 32) return 0;                             /* past the jet: its term */
    if (n == 0) return 2;                               /* underflow */
    *k = n - 1;
    return 1;
}

/*  ------------------------------------------------------------ building */

/*  Atom k, k below 2^32, si = S I, ki = K I, skk = S (K K) */
static uint32_t atom_build(av_arena *a, uint32_t si, uint32_t ki, uint32_t skk, uint32_t k) {
    int len = 0;
    while (len < 32 && k >> len) len++;
    uint32_t e = AV_NODE_K;
    for (int j = len - 1; j >= 0; j--)
        e = arena_app_reserved(a, AV_NODE_K,
                               pin_pair_build(a, si, k >> j & 1u ? AV_NODE_K : ki, e));
    uint32_t x = arena_app_reserved(a, si, arena_app_reserved(a, AV_NODE_K, e));
    for (int i = 0; i < 3; i++) x = arena_app_reserved(a, skk, x);
    return x;
}

uint32_t nock_dec_build(av_arena *a, uint32_t k, uint32_t rest) {
    uint32_t si = arena_app_reserved(a, AV_NODE_S, AV_NODE_I);
    uint32_t kk = arena_app_reserved(a, AV_NODE_K, AV_NODE_K);
    uint32_t ki = arena_app_reserved(a, AV_NODE_K, AV_NODE_I);
    uint32_t skk = arena_app_reserved(a, AV_NODE_S, kk);
    uint32_t c = pin_pair_build(a, si, atom_build(a, si, ki, skk, k), rest);
    for (int i = 0; i < 2; i++) c = arena_app_reserved(a, skk, c);
    return arena_app_reserved(a, AV_NODE_K, c);                     /* Cell (Atom k) rest */
}

uint32_t hoon_dec_build(av_arena *a, uint32_t k) {
    uint32_t si = arena_app_reserved(a, AV_NODE_S, AV_NODE_I);
    uint32_t kk = arena_app_reserved(a, AV_NODE_K, AV_NODE_K);
    uint32_t ki = arena_app_reserved(a, AV_NODE_K, AV_NODE_I);
    return atom_build(a, si, ki, arena_app_reserved(a, AV_NODE_S, kk), k);
}

uint32_t nock_dec_err(av_arena *a) {
    uint32_t ki = arena_app_reserved(a, AV_NODE_K, AV_NODE_I);
    return arena_app_reserved(a, AV_NODE_K, arena_app_reserved(a, AV_NODE_K, ki));
}

/*  ------------------------------------------------------------ the term */

uint32_t av_nock_dec_register(av_arena *a, uint32_t p, const char **err) {
    uint32_t id = pin_register(a, p, AV_NOCK_DEC_SHA256,
                               "not skinock's jetT decF: its full digest is not " AV_NOCK_DEC_SHA256,
                               err);
    if (id != AV_NONE && (a->jets[id].p2 || a->jets[id].hoon_dec)) {
        *err = "the term's digest is already another kind of jet";
        return AV_NONE;
    }
    if (id != AV_NONE) a->jets[id].nock_dec = true;
    return id;
}

uint32_t av_hoon_dec_register(av_arena *a, uint32_t p, const char **err) {
    uint32_t id = pin_register(a, p, AV_HOON_DEC_SHA256,
                               "not skinock's jetT hoonDecBodyF: its full digest is not "
                               AV_HOON_DEC_SHA256, err);
    if (id != AV_NONE && (a->jets[id].p2 || a->jets[id].nock_dec)) {
        *err = "the term's digest is already another kind of jet";
        return AV_NONE;
    }
    if (id != AV_NONE) a->jets[id].hoon_dec = true;
    return id;
}
