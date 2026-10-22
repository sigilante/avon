/**  test_read.c
 *
 *  The printed form: parse and print round-trip, parenthesization as
 *  aviary_kernel.terms.pretty writes it, atoms, errors, the print budget.
 *  The DAG form: what av_print_dag writes, av_parse_dag reads back as the
 *  same term with the same sharing, each node once, under a budget.
 */

#include <string.h>

#include "avon.h"
#include "test.h"

static int roundtrip(const char *src) {
    av_arena *a = av_arena_new(0);
    av_parse_error e;
    uint32_t t = av_parse(a, src, strlen(src), &e);
    av_buf b = { 0 };
    int same = t != AV_NONE && av_print(a, t, 1000, &b) && strcmp(b.s, src) == 0;
    if (!same) fprintf(stderr, "  roundtrip: %s -> %s\n", src, b.s ? b.s : "(none)");
    av_buf_free(&b);
    av_arena_free(a);
    return same;
}

static const char *parse_error(const char *src) {
    av_arena *a = av_arena_new(0);
    av_parse_error e = { 0, NULL };
    uint32_t t = av_parse(a, src, strlen(src), &e);
    av_arena_free(a);
    return t == AV_NONE ? e.msg : NULL;
}

TEST(printed_forms_round_trip) {
    CHECK(roundtrip("S"));
    CHECK(roundtrip("S K K"));
    CHECK(roundtrip("S (K K) I"));
    CHECK(roundtrip("S (K (S I I)) (S (S (K S) K) (K (S I I)))"));
    CHECK(roundtrip("X1 (A Z) S_"));
}

TEST(redundant_parentheses_and_space_are_dropped) {
    av_arena *a = av_arena_new(0);
    const char *src = "  ((S K) (K))\n (I)  ";
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    av_buf b = { 0 };
    CHECK(av_print(a, t, 100, &b));
    CHECK(strcmp(b.s, "S K K I") == 0);
    av_buf_free(&b);
    av_arena_free(a);
}

TEST(leaves_are_interned) {
    av_arena *a = av_arena_new(0);
    CHECK_EQ(av_leaf(a, "S", 1), AV_NODE_S);
    CHECK_EQ(av_leaf(a, "K", 1), AV_NODE_K);
    CHECK_EQ(av_leaf(a, "I", 1), AV_NODE_I);
    uint32_t x = av_leaf(a, "X1", 2);
    CHECK_EQ(av_leaf(a, "X1", 2), x);
    CHECK(av_leaf(a, "X2", 2) != x);
    CHECK(av_leaf(a, "SK", 2) != AV_NODE_S);
    CHECK(strcmp(av_leaf_name(a, av_right(a, x)), "X1") == 0);
    av_arena_free(a);
}

TEST(malformed_input_is_rejected) {
    CHECK(parse_error("") != NULL);
    CHECK(parse_error("   ") != NULL);
    CHECK(parse_error("(S K") != NULL);
    CHECK(parse_error("S K)") != NULL);
    CHECK(parse_error("S () K") != NULL);
    CHECK(parse_error("S K") == NULL);
    CHECK(parse_error("S @1") != NULL);       /* reserved for probe markers */
    CHECK(parse_error("K `x") != NULL);       /* the prefix form's mark */
    CHECK(parse_error("K x`y") != NULL);
    CHECK(parse_error("K x@y") == NULL);      /* @ only reserved in front */

    /* a NUL inside a name would be silently truncated by lookup and print */
    av_arena *a = av_arena_new(0);
    av_parse_error e = { 0, NULL };
    CHECK(av_parse(a, "S K\0I", 5, &e) == AV_NONE);
    CHECK_EQ(e.pos, 3);
    av_arena_free(a);
}

TEST(the_print_budget_refuses_past_its_limit) {
    av_arena *a = av_arena_new(0);
    const char *src = "S K K";
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    av_buf b = { 0 };
    CHECK(!av_print(a, t, 3, &b));      /* five nodes in the tree */
    av_buf_free(&b);
    CHECK(av_print(a, t, 5, &b));
    av_buf_free(&b);
    av_arena_free(a);
}

TEST(deep_nesting_does_not_recurse) {
    enum { DEPTH = 200000 };
    static char src[3 * DEPTH + 8];
    size_t n = 0;
    for (int i = 0; i < DEPTH; i++) { src[n++] = 'K'; src[n++] = '('; }
    src[n++] = 'I';
    for (int i = 0; i < DEPTH; i++) src[n++] = ')';
    av_arena *a = av_arena_new(0);
    uint32_t t = av_parse(a, src, n, NULL);
    CHECK(t != AV_NONE);
    av_buf b = { 0 };
    CHECK(av_print(a, t, 10 * DEPTH, &b));
    CHECK_EQ(b.len, 4 * DEPTH - 1);     /* "K (" and ")" per level; "K I" inside */
    av_buf_free(&b);
    av_arena_free(a);
}

/*  t printed as a DAG and read back into a fresh arena: the same term, with
 *  as many distinct nodes as the printout has lines. */
static int dag_roundtrip(av_arena *a, uint32_t t, size_t nodes) {
    av_buf b = { 0 };
    int ok = av_print_dag(a, t, 1u << 20, &b);
    av_arena *c = av_arena_new(0);
    const char *msg = NULL;
    uint32_t u = ok ? av_parse_dag(c, b.s, b.len, &msg) : AV_NONE;
    av_buf p = { 0 }, q = { 0 };
    ok = u != AV_NONE && av_print(a, t, 1u << 20, &p) && av_print(c, u, 1u << 20, &q) &&
         strcmp(p.s, q.s) == 0;
    size_t defs = 0;
    for (size_t i = 0; b.s && b.s[i]; i++) defs += b.s[i] == '=';
    if (nodes && defs != nodes) ok = 0;
    if (!ok) fprintf(stderr, "  dag: %s -> %s (%zu nodes, %s)\n", p.s ? p.s : "?",
                     b.s ? b.s : "(none)", defs, msg ? msg : "");
    av_buf_free(&b); av_buf_free(&p); av_buf_free(&q);
    av_arena_free(c);
    return ok;
}

TEST(the_dag_form_prints_what_it_reads) {
    av_arena *a = av_arena_new(0);
    const char *srcs[] = { "S", "x", "S K K", "S (K a) I b", "X1 (A Z) S_",
                           "S (K (S I I)) (S (S (K S) K) (K (S I I)))" };
    for (size_t i = 0; i < sizeof srcs / sizeof *srcs; i++) {
        uint32_t t = av_parse(a, srcs[i], strlen(srcs[i]), NULL);
        CHECK(t != AV_NONE && dag_roundtrip(a, t, 0));
    }
    /* a tower of shared doublings: 2^40 leaves unfolded, 41 nodes shared */
    uint32_t t = av_leaf(a, "x", 1);
    for (int k = 0; k < 40; k++) t = av_app(a, t, t);
    av_buf b = { 0 };
    CHECK(av_print_dag(a, t, 41, &b));
    av_buf_free(&b);
    CHECK(!av_print_dag(a, t, 40, &b));         /* one node past the budget */
    av_buf_free(&b);
    av_arena *c = av_arena_new(0);
    CHECK(av_print_dag(a, t, 41, &b));
    const char *msg = NULL;
    uint32_t u = av_parse_dag(c, b.s, b.len, &msg);
    CHECK(u != AV_NONE);
    size_t defs = 0;
    for (size_t i = 0; b.s[i]; i++) defs += b.s[i] == '=';
    CHECK_EQ(defs, 41);
    /* read back shared: every level's two halves are one node */
    int levels = 0;
    for (uint32_t v = u; av_tag(c, v) == AV_APP && av_left(c, v) == av_right(c, v);
         v = av_left(c, v))
        levels++;
    CHECK_EQ(levels, 40);
    av_buf_free(&b);
    av_arena_free(c);
    /* a shared application: S, K, S K and the whole, four nodes */
    uint32_t sk = av_parse(a, "S K", 3, NULL);
    CHECK(dag_roundtrip(a, av_app(a, sk, sk), 4));
    av_arena_free(a);
}

TEST_MAIN(
    TEST_CASE(printed_forms_round_trip),
    TEST_CASE(redundant_parentheses_and_space_are_dropped),
    TEST_CASE(leaves_are_interned),
    TEST_CASE(malformed_input_is_rejected),
    TEST_CASE(the_print_budget_refuses_past_its_limit),
    TEST_CASE(deep_nesting_does_not_recurse),
    TEST_CASE(the_dag_form_prints_what_it_reads),
)
