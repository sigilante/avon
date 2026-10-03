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
 */

#include <stdint.h>
#include <string.h>

#include "avon.h"
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
