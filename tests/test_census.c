/**  test_census.c
 *
 *  The dynamic census of called terms, for choosing jets.  A program that
 *  calls B = S (K S) K k times, the loaded root's call among them: the
 *  census must leave the count alone, find B with its arity and cost,
 *  measure k fires, and fold B's layers into one family.  A B that only a
 *  run builds is not loaded code and is not counted.
 */

#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "test.h"

#define K_LEVELS 50

/*  E_0 = z; E_k = B I (K E_{k-1}) a, which reduces to E_{k-1} in six
 *  contractions: four for B, then I and K. */
static uint32_t nest(av_arena *a, unsigned k) {
    uint32_t b = av_parse(a, "S (K S) K", 9, NULL);
    uint32_t e = av_leaf(a, "z", 1), at = av_leaf(a, "a", 1);
    for (unsigned i = 0; i < k; i++)
        e = av_app(a, av_app(a, av_app(a, b, AV_NODE_I), av_app(a, AV_NODE_K, e)), at);
    return e;
}

static av_result run(av_arena *a, uint32_t t, av_census *c) {
    av_opts o = av_opts_default();
    o.strategy = AV_COPY;
    o.whnf_only = true;
    o.jets = false;
    o.census = c;
    if (c) CHECK(av_census_begin_run(c, a, t));
    return av_reduce(a, t, &o);
}

/*  The three passes over one program. */
static av_census *census_of(const char *src) {
    av_census *c = av_census_new();
    for (int pass = 0; pass < 3; pass++) {
        av_arena *a = av_arena_new(1u << 16);
        uint32_t t = src ? av_parse(a, src, strlen(src), NULL) : nest(a, K_LEVELS);
        run(a, t, c);
        av_arena_free(a);
        if (pass == 0) av_census_select(c, 50, 4);
        if (pass == 1) av_census_analyze(c);
    }
    return c;
}

static const av_census_row *find(av_census *c, const char *text) {
    av_census_row *rows;
    size_t n = av_census_rows(c, &rows);
    for (size_t i = 0; i < n; i++) {
        av_buf b = { 0 };
        bool hit = rows[i].term != AV_NONE &&
                   av_print(av_census_arena(c), rows[i].term, 1000, &b) &&
                   strcmp(b.s, text) == 0;
        av_buf_free(&b);
        if (hit) return &rows[i];
    }
    return NULL;
}

TEST(the_census_leaves_counts_alone) {
    av_arena *a = av_arena_new(1u << 16);
    uint32_t t = nest(a, K_LEVELS);
    av_result plain = run(a, t, NULL);
    av_census *c = av_census_new();
    av_result counted = run(a, t, c);
    CHECK_EQ(plain.status, AV_WHNF);
    CHECK_EQ(plain.steps, 6 * K_LEVELS);
    CHECK_EQ(counted.steps, plain.steps);
    CHECK(av_census_calls(c) > 0);
    av_census_free(c);
    av_arena_free(a);
}

TEST(it_finds_b_with_its_arity_and_cost) {
    av_census *c = census_of(NULL);
    const av_census_row *b = find(c, "S (K S) K");
    CHECK(b != NULL);
    if (b) {
        CHECK_EQ(b->calls, K_LEVELS);
        CHECK_EQ(b->hist[3], K_LEVELS);          /* B I (K E) a: three args */
        CHECK_EQ(b->arity, 3);
        CHECK_EQ(b->cost, 4);
        CHECK_EQ(b->fires, K_LEVELS);
        CHECK_EQ(b->saved, 4 * K_LEVELS);
    }
    /* B I is one of B's layers, met at the same calls: one family */
    const av_census_row *bi = find(c, "S (K S) K I");
    CHECK(bi != NULL);
    if (b && bi) {
        CHECK_EQ(bi->calls, K_LEVELS);
        CHECK((bi->folds_into >= 0) != (b->folds_into >= 0));
    }
    av_census_free(c);
}

TEST(a_term_only_the_run_builds_is_not_counted) {
    /* K (S (K S)) x K f g y: the run builds S (K S) K; no loaded node is B */
    av_census *c = census_of("K (S (K S)) x K f g y");
    CHECK(find(c, "K (S (K S))") != NULL);      /* the loaded root's call */
    const av_census_row *b = find(c, "S (K S) K");
    CHECK(b == NULL || b->calls == 0);
    av_census_free(c);
}

TEST_MAIN(
    TEST_CASE(the_census_leaves_counts_alone),
    TEST_CASE(it_finds_b_with_its_arity_and_cost),
    TEST_CASE(a_term_only_the_run_builds_is_not_counted),
)
