/**  test_probe.c
 *
 *  Reading values by running them: peel, decode and the Scott-numeral
 *  reader, on data built by hand from bracket abstraction, and their
 *  refusals.  tests/test_conformance.c exercises them on the corpus.
 */

#include <string.h>

#include "avon.h"
#include "test.h"

/*  Scott data, written by bracket abstraction:
 *    nothing n j   = n           K
 *    just x n j    = j x         S (K K) (S (K (S I)) K)    (as suc)
 *    zero z s      = z           K
 *    suc n z s     = s n         S (K K) (S (K (S I)) K)
 *  and a four-constructor object type S | K | I | App t u:
 *    encS s k i a  = s           K (K (K ...)) shapes below
 */
static const char SUC[] = "S (K K) (S (K (S I)) K)";

static uint32_t parse(av_arena *a, const char *s) {
    return av_parse(a, s, strlen(s), NULL);
}

TEST(peel_reads_the_constructor_and_its_fields) {
    av_arena *a = av_arena_new(0);
    av_opts o = av_opts_default();
    av_peeled p;
    /* nothing: two constructors, the first */
    CHECK(av_peel(a, parse(a, "K"), 2, &o, &p, NULL));
    CHECK_EQ(p.ctor, 0);
    CHECK_EQ(p.nfields, 0);
    /* just X, with X an atom the probe hands back */
    uint32_t just = av_app(a, parse(a, SUC), parse(a, "X"));
    CHECK(av_peel(a, just, 2, &o, &p, NULL));
    CHECK_EQ(p.ctor, 1);
    CHECK_EQ(p.nfields, 1);
    /* a field is handed back unreduced---here K X m1---and read by
     * reducing or probing it further, as run.py's fields are */
    av_result r = av_reduce(a, p.field[0], &o);
    av_buf b = { 0 };
    CHECK(r.status == AV_NORMAL && av_print(a, r.term, 10, &b) && strcmp(b.s, "X") == 0);
    av_buf_free(&b);
    av_arena_free(a);
}

TEST(peel_refuses_what_is_not_a_value) {
    av_arena *a = av_arena_new(0);
    av_opts o = av_opts_default();
    av_peeled p;
    const char *err = NULL;
    /* I applied to two markers returns the first: a marker is fine here */
    CHECK(av_peel(a, parse(a, "I"), 2, &o, &p, &err));
    /* an atom head that is not a marker */
    err = NULL;
    CHECK(!av_peel(a, parse(a, "K (X A)"), 2, &o, &p, &err));
    CHECK(err && strstr(err, "not a marker"));
    /* divergence stops at the fuel cap */
    o.max_steps = 1000;
    err = NULL;
    CHECK(!av_peel(a, parse(a, "S I I (S I I)"), 2, &o, &p, &err));
    CHECK(err && strstr(err, "weak head normal form"));
    av_arena_free(a);
}

TEST(numerals_read_back) {
    av_arena *a = av_arena_new(0);
    av_opts o = av_opts_default();
    uint32_t n = parse(a, "K");
    for (int k = 0; k <= 12; k++) {
        uint64_t got = 99;
        CHECK(av_read_nat(a, n, 1000, &o, &got, NULL));
        CHECK_EQ(got, k);
        n = av_app(a, parse(a, SUC), n);
    }
    uint64_t got;
    const char *err = NULL;
    CHECK(!av_read_nat(a, n, 5, &o, &got, &err));     /* 13 > the limit */
    CHECK(err && strstr(err, "deeper"));
    err = NULL;
    CHECK(!av_read_nat(a, parse(a, "K I"), 10, &o, &got, &err));
    CHECK(err != NULL);
    av_arena_free(a);
}

/*  The object type S | K | I | App t u, each constructor by bracket
 *  abstraction with eta:
 *    encS      = \s k i p. s      = S (K K) (S (K K) K)
 *    encK      = \s k i p. k      = K (S (K K) K)
 *    app t u   = \s k i p. p t u  = K (K (K (S (S I (K t)) (K u))))  */
static uint32_t app_of(av_arena *a, uint32_t t, uint32_t u) {
    uint32_t pt = av_app(a, av_app(a, AV_NODE_S, AV_NODE_I), av_app(a, AV_NODE_K, t));
    uint32_t ptu = av_app(a, av_app(a, AV_NODE_S, pt), av_app(a, AV_NODE_K, u));
    return av_app(a, AV_NODE_K, av_app(a, AV_NODE_K, av_app(a, AV_NODE_K, ptu)));
}

TEST(decode_rebuilds_a_quoted_term) {
    av_arena *a = av_arena_new(0);
    av_opts o = av_opts_default();
    static const char *const names[] = { "S", "K", "I", "App" };
    uint32_t encS = parse(a, "S (K K) (S (K K) K)");
    uint32_t encK = av_app(a, AV_NODE_K, parse(a, "S (K K) K"));
    /* App (App K S) K, the two K data one shared node: four probes */
    uint32_t outer = app_of(a, app_of(a, encK, encS), encK);

    const char *err = NULL;
    uint32_t d = av_decode(a, outer, 4, names, 3, 1000, &o, &err);
    av_buf b = { 0 };
    CHECK(d != AV_NONE && av_print(a, d, 100, &b));
    if (b.s && strcmp(b.s, "K S K") != 0) fprintf(stderr, "  decoded %s\n", b.s);
    CHECK(b.s && strcmp(b.s, "K S K") == 0);         /* App (App K S) K */
    av_buf_free(&b);

    /* the probe limit refuses a datum with more nodes */
    err = NULL;
    CHECK(av_decode(a, outer, 4, names, 3, 3, &o, &err) == AV_NONE);
    CHECK(err && strstr(err, "limit"));
    av_arena_free(a);
}

TEST(markers_are_found_by_id_not_by_order) {
    /* the reviewer's case: markers interned before, in reverse order */
    av_arena *a = av_arena_new(0);
    av_leaf(a, "@1", 2);
    av_leaf(a, "@0", 2);
    av_opts o = av_opts_default();
    av_peeled p;
    uint32_t just = av_app(a, parse(a, SUC), parse(a, "X"));
    CHECK(av_peel(a, just, 2, &o, &p, NULL));
    CHECK_EQ(p.ctor, 1);
    CHECK_EQ(p.nfields, 1);
    CHECK(av_peel(a, parse(a, "K"), 2, &o, &p, NULL));
    CHECK_EQ(p.ctor, 0);
    av_arena_free(a);
}

TEST_MAIN(
    TEST_CASE(peel_reads_the_constructor_and_its_fields),
    TEST_CASE(peel_refuses_what_is_not_a_value),
    TEST_CASE(numerals_read_back),
    TEST_CASE(decode_rebuilds_a_quoted_term),
    TEST_CASE(markers_are_found_by_id_not_by_order),
)
