/**  test_profile.c
 *
 *  The share-mode profile.  E_0 = z and E_k = B I (K E_{k-1}) a, with
 *  B = S (K S) K named: each level reduces in six contractions.  Two run
 *  B's code (`S (K S)`, `K S`).  Two run loaded nodes no name covers:
 *  `S (K I)` reaches `S f g` = `S (K I) (K E)`, the level's own node, after
 *  the run rewrote `S f`; and `K E`.  The run built `K I` and rewrote the
 *  root that became `I x`, so those two go to the run-time rows.  The
 *  charges must hold through collections, and change no count.
 */

#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "test.h"

#define LEVELS 200

static uint32_t nest(av_arena *a, unsigned k) {
    uint32_t b = av_parse(a, "S (K S) K", 9, NULL);
    uint32_t e = av_leaf(a, "z", 1), at = av_leaf(a, "a", 1);
    for (unsigned i = 0; i < k; i++)
        e = av_app(a, av_app(a, av_app(a, b, AV_NODE_I), av_app(a, AV_NODE_K, e)), at);
    return e;
}

/*  Returns the collections the run made. */
static uint64_t profile_levels(uint32_t cap) {
    av_arena *a = av_arena_new(cap);
    uint32_t t = nest(a, LEVELS);
    char h[AV_HASH_LEN + 1];
    uint32_t b = av_parse(a, "S (K S) K", 9, NULL);
    CHECK(av_structural_hash(a, b, h));
    av_profile *p = av_profile_new();
    CHECK(av_profile_name(p, h, "B"));
    CHECK(av_profile_begin(p, a, t));
    av_opts o = av_opts_default();
    o.whnf_only = true;
    o.profile = p;
    av_root_push(a, &t);
    av_result r = av_reduce(a, t, &o);
    av_root_pop(a);
    CHECK_EQ(r.status, AV_WHNF);
    CHECK_EQ(r.steps, 6 * LEVELS);
    CHECK_EQ(av_profile_total(p), r.steps);
    CHECK_EQ(av_profile_count(p, "B"), 2 * LEVELS);
    CHECK_EQ(av_profile_count(p, "(loaded, no name)"), 2 * LEVELS);
    CHECK_EQ(av_profile_count(p, "(built at run time) S"), 0);
    CHECK_EQ(av_profile_count(p, "(built at run time) K"), LEVELS);
    CHECK_EQ(av_profile_count(p, "(built at run time) I"), LEVELS);
    uint64_t collections = a->collections;
    av_profile_free(p);
    av_arena_free(a);
    return collections;
}

TEST(charges_each_contraction_to_the_code_it_runs) {
    CHECK_EQ(profile_levels(1u << 16), 0);
}

TEST(the_charges_follow_the_nodes_through_collections) {
    CHECK(profile_levels(1u << 8) > 0);             /* 256 nodes: it collects */
}

TEST(a_second_name_for_one_hash_joins_the_first) {
    av_arena *a = av_arena_new(1u << 10);
    char h[AV_HASH_LEN + 1];
    CHECK(av_structural_hash(a, av_parse(a, "S (K S) K", 9, NULL), h));
    av_profile *p = av_profile_new();
    CHECK(av_profile_name(p, h, "B"));
    CHECK(av_profile_name(p, h, "bluebird"));
    CHECK(!av_profile_name(p, "not a hash", "x"));
    uint32_t t = av_parse(a, "S (K S) K I (K z) a", 19, NULL);
    CHECK(av_profile_begin(p, a, t));
    av_opts o = av_opts_default();
    o.profile = p;
    av_reduce(a, t, &o);
    CHECK_EQ(av_profile_count(p, "B/bluebird"), 2);
    av_profile_free(p);
    av_arena_free(a);
}

TEST_MAIN(
    TEST_CASE(charges_each_contraction_to_the_code_it_runs),
    TEST_CASE(the_charges_follow_the_nodes_through_collections),
    TEST_CASE(a_second_name_for_one_hash_joins_the_first)
)
