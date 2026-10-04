/**  p2.c
 *
 *  Poseidon2 over BabyBear, width 16, as lean-ski specifies it
 *  (Ski/ZK/Poseidon2.lean): the external layer first, four full rounds,
 *  thirteen partial rounds, four full rounds.  The constants are the
 *  specification's (src/p2_consts.h, printed by lean-ski's bench/P2C.lean),
 *  and av_p2_selftest checks the permutation against the specification's
 *  three test vectors, which the Lean kernel checks against Plonky3's.
 *
 *  The inputs may be any 31-bit values: the first layer reduces them, as
 *  the specification does.
 *
 *  And the Poseidon2 jet (docs/DESIGN.md §6.12): P's term registered and
 *  bound, and the states it reads and writes.
 */

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "jets.h"
#include "p2_consts.h"

static uint32_t md(uint64_t x) { return (uint32_t)(x % AV_P2_P); }

static uint32_t sbox(uint32_t x) {
    uint64_t a = x % AV_P2_P;
    uint64_t a2 = a * a % AV_P2_P, a3 = a2 * a % AV_P2_P, a6 = a3 * a3 % AV_P2_P;
    return (uint32_t)(a6 * a % AV_P2_P);
}

/*  Plonky3's M4 on each block of four, then each entry plus its column's
 *  sum (the entries at its position mod 4). */
static void ext_linear(uint32_t s[16]) {
    uint32_t m[16];
    for (int b = 0; b < 4; b++) {
        uint64_t x0 = s[4 * b], x1 = s[4 * b + 1], x2 = s[4 * b + 2], x3 = s[4 * b + 3];
        m[4 * b] = md(2 * x0 + 3 * x1 + x2 + x3);
        m[4 * b + 1] = md(x0 + 2 * x1 + 3 * x2 + x3);
        m[4 * b + 2] = md(x0 + x1 + 2 * x2 + 3 * x3);
        m[4 * b + 3] = md(3 * x0 + x1 + x2 + 2 * x3);
    }
    uint64_t col[4];
    for (int k = 0; k < 4; k++)
        col[k] = md((uint64_t)m[k] + m[k + 4] + m[k + 8] + m[k + 12]);
    for (int i = 0; i < 16; i++) s[i] = md((uint64_t)m[i] + col[i % 4]);
}

/*  The internal layer 1 + Diag(V): each entry the sum plus its own times
 *  its diagonal entry. */
static void int_linear(uint32_t s[16]) {
    uint64_t sum = 0;
    for (int i = 0; i < 16; i++) sum += s[i];
    sum %= AV_P2_P;
    for (int i = 0; i < 16; i++) s[i] = md(sum + (uint64_t)av_p2_diag[i] * s[i]);
}

static void ext_round(uint32_t s[16], const uint32_t rc[16]) {
    for (int i = 0; i < 16; i++) s[i] = sbox(md((uint64_t)s[i] + rc[i]));
    ext_linear(s);
}

void av_p2_permute(uint32_t s[16]) {
    ext_linear(s);
    for (int r = 0; r < 4; r++) ext_round(s, av_p2_rc_initial[r]);
    for (int r = 0; r < 13; r++) {
        s[0] = sbox(md((uint64_t)s[0] + av_p2_rc_internal[r]));
        int_linear(s);
    }
    for (int r = 0; r < 4; r++) ext_round(s, av_p2_rc_terminal[r]);
}

bool av_p2_selftest(void) {
    for (int v = 0; v < 3; v++) {
        uint32_t s[16];
        memcpy(s, av_p2_vectors[v][0], sizeof s);
        av_p2_permute(s);
        if (memcmp(s, av_p2_vectors[v][1], sizeof s) != 0) return false;
    }
    return true;
}

/*  ------------------------------------------------------------ the jet */

/*  P's full digest: §5's Merkle hash with every digest kept whole, 32
 *  bytes, over S, K and I only: an atom's, SHA-256 of its name; an
 *  application's, of "(" + hex(f) + " " + hex(x) + ")".  False on any other
 *  leaf, or out of memory. */
static bool merkle256(const av_arena *a, uint32_t t, uint8_t out[32]) {
    static const char hx[] = "0123456789abcdef";
    nmap at = { 0 };                        /* viewed node -> 1 + its slot */
    uint8_t (*d)[32] = NULL;
    size_t nd = 0, dcap = 0, cap = 256, top = 0;
    typedef struct { uint32_t node; bool done; } item;
    item *todo = malloc(cap * sizeof *todo);
    bool ok = todo != NULL;
    if (ok) todo[top++] = (item){ av_view(a, t), false };
    while (ok && top) {
        item it = todo[--top];
        uint64_t v;
        if (nmap_get(&at, it.node, &v)) continue;
        uint8_t h[32];
        if (av_tag(a, it.node) == AV_LEAF) {
            static const char *const name[3] = { "S", "K", "I" };
            if (it.node > AV_NODE_I) { ok = false; break; }
            av_sha256(name[it.node], 1, h);
        } else {
            uint32_t f = av_view(a, av_left(a, it.node)), x = av_view(a, av_right(a, it.node));
            uint64_t df, dx;
            if (!it.done) {
                if (top + 3 > cap) {
                    item *q = realloc(todo, (cap *= 2) * sizeof *q);
                    if (!q) { ok = false; break; }
                    todo = q;
                }
                todo[top++] = (item){ it.node, true };
                todo[top++] = (item){ x, false };
                todo[top++] = (item){ f, false };
                continue;
            }
            nmap_get(&at, f, &df);
            nmap_get(&at, x, &dx);
            char text[131];
            text[0] = '(';
            text[65] = ' ';
            text[130] = ')';
            for (int k = 0; k < 32; k++) {
                text[1 + 2 * k] = hx[d[df - 1][k] >> 4];
                text[2 + 2 * k] = hx[d[df - 1][k] & 15];
                text[66 + 2 * k] = hx[d[dx - 1][k] >> 4];
                text[67 + 2 * k] = hx[d[dx - 1][k] & 15];
            }
            av_sha256(text, sizeof text, h);
        }
        if (nd == dcap) {
            size_t c = dcap ? 2 * dcap : 1024;
            uint8_t (*q)[32] = realloc(d, c * sizeof *q);
            if (!q) { ok = false; break; }
            d = q;
            dcap = c;
        }
        memcpy(d[nd++], h, 32);
        if (!nmap_put(&at, it.node, nd)) { ok = false; break; }
    }
    uint64_t r;
    if (ok && nmap_get(&at, av_view(a, t), &r)) memcpy(out, d[r - 1], 32);
    else ok = false;
    free(todo);
    free(d);
    nmap_free(&at);
    return ok;
}

bool av_p2_digest(const av_arena *a, uint32_t t, char out[65]) {
    static const char hx[] = "0123456789abcdef";
    uint8_t h[32];
    if (!merkle256(a, t, h)) return false;
    for (int k = 0; k < 32; k++) {
        out[2 * k] = hx[h[k] >> 4];
        out[2 * k + 1] = hx[h[k] & 15];
    }
    out[64] = '\0';
    return true;
}

/*  P's distinct nodes, through views: the bound on a comparison with it. */
static uint32_t view_nodes(const av_arena *a, uint32_t t) {
    nmap seen = { 0 };
    size_t cap = 256, top = 0;
    uint32_t *todo = malloc(cap * sizeof *todo), n = 0;
    bool ok = todo != NULL;
    if (ok) todo[top++] = t;
    while (ok && top) {
        uint32_t x = av_view(a, todo[--top]);
        uint64_t v;
        if (nmap_get(&seen, x, &v)) continue;
        if (!(ok = nmap_put(&seen, x, 1))) break;
        n++;
        if (av_tag(a, x) != AV_APP) continue;
        if (top + 2 > cap) {
            uint32_t *q = realloc(todo, (cap *= 2) * sizeof *q);
            if (!(ok = q != NULL)) break;
            todo = q;
        }
        todo[top++] = av_left(a, x);
        todo[top++] = av_right(a, x);
    }
    free(todo);
    nmap_free(&seen);
    return ok ? n : 0;
}

bool p2_same(const av_arena *a, uint32_t x, uint32_t id) {
    return av_equal(a, x, a->jets[id].fallback, 8 * (size_t)a->jets[id].p2_nodes + 4096) == 1;
}

uint32_t p2_register(av_arena *a, uint32_t p, bool pin, const char **err) {
    char h[27];
    uint64_t d;
    if (!av_structural_hash(a, p, h) || !av_hash_parse(h, &d)) {
        *err = "cannot hash P's term";
        return AV_NONE;
    }
    char full[65];
    if (pin && (!av_p2_digest(a, p, full) || strcmp(full, AV_P2_SHA256) != 0)) {
        *err = "not lean-ski's Poseidon2 term P: its full digest is not " AV_P2_SHA256;
        return AV_NONE;
    }
    uint32_t nodes = view_nodes(a, p);
    if (!nodes) {
        *err = "out of memory";
        return AV_NONE;
    }
    uint32_t before = a->njets;
    uint32_t id = jet_entry_for(a, d, p);
    if (id == AV_NONE) {
        *err = "out of memory";
        return AV_NONE;
    }
    av_jet *j = &a->jets[id];
    if (j->tmpl || j->word_op || j->fix || j->interp >= 0) {
        *err = "P's digest is already another kind of jet";
        return AV_NONE;
    }
    if (id < before && av_equal(a, j->fallback, p, 8 * (size_t)nodes + 4096) != 1) {
        /* an entry under the same digest from elsewhere (a --jets
         * dictionary): its term must be P's, since the fires check
         * against it */
        *err = "another term already holds P's digest";
        return AV_NONE;
    }
    j->p2 = true;
    j->p2_nodes = nodes;
    return id;
}

uint32_t av_p2_register(av_arena *a, uint32_t p, const char **err) {
    return p2_register(a, p, true, err);
}

long av_p2_bind(av_arena *a, uint32_t t, uint32_t id) {
    nmap seen = { 0 };
    size_t cap = 256, top = 0;
    uint32_t *todo = malloc(cap * sizeof *todo);
    long kept = 0;
    if (!todo) return -1;
    todo[top++] = t;
    while (top) {
        uint32_t x = av_res(a, todo[--top]);
        uint64_t v;
        if (nmap_get(&seen, x, &v)) continue;
        if (!nmap_put(&seen, x, 1)) { kept = -1; break; }
        if (av_tag(a, x) == AV_JET && !(av_left(a, x) & AV_JET_WORD)) {
            uint32_t inner = av_right(a, x);
            if (AV_JET_ID(av_left(a, x)) == id) {
                if (p2_same(a, inner, id)) kept++;
                else arena_set(a, x, (av_node){ (AV_IND << AV_TAG_SHIFT) | inner, 0 });
            }
            x = inner;
        }
        if (av_tag(a, x) != AV_APP) continue;
        if (top + 2 > cap) {
            uint32_t *q = realloc(todo, (cap *= 2) * sizeof *q);
            if (!q) { kept = -1; break; }
            todo = q;
        }
        todo[top++] = av_left(a, x);
        todo[top++] = av_right(a, x);
    }
    free(todo);
    nmap_free(&seen);
    return kept;
}

/*  pairT x y = S (S I (K x)) (K y), seen through indirections and jet
 *  nodes. */
static bool pair_read(const av_arena *a, uint32_t t, uint32_t *x, uint32_t *y) {
    t = av_view(a, t);
    if (av_tag(a, t) != AV_APP) return false;
    uint32_t f = av_view(a, av_left(a, t)), ky = av_view(a, av_right(a, t));
    if (av_tag(a, f) != AV_APP || av_tag(a, ky) != AV_APP ||
        av_view(a, av_left(a, f)) != AV_NODE_S || av_view(a, av_left(a, ky)) != AV_NODE_K)
        return false;
    uint32_t g = av_view(a, av_right(a, f));            /* S I (K x) */
    if (av_tag(a, g) != AV_APP) return false;
    uint32_t si = av_view(a, av_left(a, g)), kx = av_view(a, av_right(a, g));
    if (av_tag(a, si) != AV_APP || av_tag(a, kx) != AV_APP ||
        av_view(a, av_left(a, si)) != AV_NODE_S || av_view(a, av_right(a, si)) != AV_NODE_I ||
        av_view(a, av_left(a, kx)) != AV_NODE_K)
        return false;
    *x = av_right(a, kx);
    *y = av_right(a, ky);
    return true;
}

bool av_p2_state_read(const av_arena *a, uint32_t t, uint32_t s[16]) {
    for (int i = 0; i < 16; i++) {
        uint32_t e, bits;
        if (!pair_read(a, t, &e, &t)) return false;
        uint32_t v = 0;
        for (int j = 0; j < 31; j++) {
            uint32_t b;
            if (!pair_read(a, e, &b, &e)) return false;
            b = av_view(a, b);
            if (b == AV_NODE_K) v |= 1u << j;               /* boolT true */
            else if (av_tag(a, b) != AV_APP || av_view(a, av_left(a, b)) != AV_NODE_K ||
                     av_view(a, av_right(a, b)) != AV_NODE_I)
                return false;                               /* nor boolT false */
        }
        bits = av_view(a, e);
        if (bits != AV_NODE_K) return false;                /* bitsT 31 ends in K */
        s[i] = v;
    }
    return av_view(a, t) == AV_NODE_K;                      /* so does stateN */
}

static uint32_t pair_build(av_arena *a, uint32_t si, uint32_t x, uint32_t y) {
    uint32_t f = arena_app_reserved(a, AV_NODE_S, arena_app_reserved(a, si,
                                    arena_app_reserved(a, AV_NODE_K, x)));
    return arena_app_reserved(a, f, arena_app_reserved(a, AV_NODE_K, y));
}

uint32_t p2_state_build(av_arena *a, const uint32_t s[16]) {
    uint32_t si = arena_app_reserved(a, AV_NODE_S, AV_NODE_I);
    uint32_t ki = arena_app_reserved(a, AV_NODE_K, AV_NODE_I);
    uint32_t st = AV_NODE_K;
    for (int i = 15; i >= 0; i--) {
        uint32_t e = AV_NODE_K;
        for (int j = 30; j >= 0; j--)
            e = pair_build(a, si, s[i] >> j & 1u ? AV_NODE_K : ki, e);
        st = pair_build(a, si, e, st);
    }
    return st;
}
