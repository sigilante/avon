/**  test_ski.c
 *
 *  The calculus interface and the node layout: arities, leaf ids, and the
 *  facts about av_node that docs/DESIGN.md §2 relies on.
 */

#include "avon.h"
#include "test.h"

TEST(arities_follow_the_rules) {
    CHECK_EQ(ski_arity(SKI_S), 3);
    CHECK_EQ(ski_arity(SKI_K), 2);
    CHECK_EQ(ski_arity(SKI_I), 1);
}

TEST(atoms_are_inert) {
    CHECK(!ski_is_comb(SKI_ATOM_FIRST));
    CHECK_EQ(ski_arity(SKI_ATOM_FIRST), 0);
    CHECK_EQ(ski_arity(UINT32_MAX), 0);
}

TEST(a_node_is_eight_bytes) {
    CHECK_EQ(sizeof(av_node), 8);
}

TEST(the_tag_is_the_top_two_bits) {
    av_node leaf = { AV_LEAF << AV_TAG_SHIFT, SKI_K };
    av_node app  = { 7, 9 };
    CHECK_EQ(AV_TAG(leaf), AV_LEAF);
    CHECK_EQ(AV_TAG(app), AV_APP);
}

TEST_MAIN(
    TEST_CASE(arities_follow_the_rules),
    TEST_CASE(atoms_are_inert),
    TEST_CASE(a_node_is_eight_bytes),
    TEST_CASE(the_tag_is_the_top_two_bits),
)
