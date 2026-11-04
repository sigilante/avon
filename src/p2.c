/**  p2.c
 *
 *  Poseidon2 over BabyBear, width 16, as lean-ski specifies it
 *  (Ski/ZK/Poseidon2.lean).  The permutation is C that lean/P2Prog.lean
 *  prints from a program it proves equal to the specification, with C's
 *  arithmetic, on every state of sixteen uint32_t values (AvonP2.permuteC);
 *  the inputs may be at or above p, since the first layer reduces them, as
 *  the specification does.  av_p2_selftest checks the specification's
 *  three test vectors (src/p2_consts.h, printed by lean-ski's
 *  bench/P2C.lean), which the Lean kernel checks against Plonky3's.
 *
 *  And the Poseidon2 jet: P's term registered (pin.c holds what pinned
 *  jets share), and the states it reads and writes.
 */

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "jets.h"
#include "p2_consts.h"
#include "p2_prog.h"

/*  The permutation is printed by lean/P2Prog.lean (src/p2_prog.h), which
 *  proves it equal to the specification's on every state of sixteen
 *  uint32_t values (AvonP2.permuteC). */
void av_p2_permute(uint32_t s[16]) { av_p2_prog(s); }

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

uint32_t p2_register(av_arena *a, uint32_t p, bool pin, const char **err) {
    uint32_t id = pin_register(a, p, pin ? AV_P2_SHA256 : NULL,
                               "not lean-ski's Poseidon2 term P: its full digest is not " AV_P2_SHA256,
                               err);
    if (id != AV_NONE && (a->jets[id].nock_dec || a->jets[id].hoon_dec)) {
        *err = "the term's digest is already another kind of jet";
        return AV_NONE;
    }
    if (id != AV_NONE) a->jets[id].p2 = true;
    return id;
}

uint32_t av_p2_register(av_arena *a, uint32_t p, const char **err) {
    return p2_register(a, p, true, err);
}

bool av_p2_state_read(const av_arena *a, uint32_t t, uint32_t s[16]) {
    for (int i = 0; i < 16; i++) {
        uint32_t e, bits;
        if (!pin_pair_read(a, t, &e, &t)) return false;
        uint32_t v = 0;
        for (int j = 0; j < 31; j++) {
            uint32_t b;
            if (!pin_pair_read(a, e, &b, &e)) return false;
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

uint32_t p2_state_build(av_arena *a, const uint32_t s[16]) {
    uint32_t si = arena_app_reserved(a, AV_NODE_S, AV_NODE_I);
    uint32_t ki = arena_app_reserved(a, AV_NODE_K, AV_NODE_I);
    uint32_t st = AV_NODE_K;
    for (int i = 15; i >= 0; i--) {
        uint32_t e = AV_NODE_K;
        for (int j = 30; j >= 0; j--)
            e = pin_pair_build(a, si, s[i] >> j & 1u ? AV_NODE_K : ki, e);
        st = pin_pair_build(a, si, e, st);
    }
    return st;
}
