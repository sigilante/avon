/**  test_reduce.c
 *
 *  The reducer on small terms: each rule, normal order, the fuel boundary,
 *  atoms, statuses, collection under a tiny arena, and a differential of
 *  the two strategies over random terms.
 */

#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "test.h"

typedef struct { av_status status; uint64_t steps; char text[256]; } outcome;

static outcome run(const char *src, av_strategy s, bool whnf, uint64_t fuel) {
    outcome out = { 0, 0, "" };
    av_arena *a = av_arena_new(0);
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    av_opts o = av_opts_default();
    o.strategy = s;
    o.whnf_only = whnf;
    o.max_steps = fuel;
    av_result r = av_reduce(a, t, &o);
    out.status = r.status;
    out.steps = r.steps;
    av_buf b = { 0 };
    if (r.term != AV_NONE && av_print(a, r.term, 200, &b) && b.len < sizeof out.text)
        memcpy(out.text, b.s, b.len + 1);
    av_buf_free(&b);
    av_arena_free(a);
    return out;
}

static int is(outcome o, av_status s, uint64_t steps, const char *text) {
    int ok = o.status == s && o.steps == steps && strcmp(o.text, text) == 0;
    if (!ok)
        fprintf(stderr, "  got %s %llu \"%s\", want %s %llu \"%s\"\n",
                av_status_name(o.status), (unsigned long long)o.steps, o.text,
                av_status_name(s), (unsigned long long)steps, text);
    return ok;
}

#define BOTH(src, whnf, st, n, text)                                        \
    do {                                                                    \
        CHECK(is(run(src, AV_COPY, whnf, UINT64_MAX), st, n, text));        \
        CHECK(is(run(src, AV_SHARE, whnf, UINT64_MAX), st, n, text));       \
    } while (0)

TEST(each_rule_contracts_once) {
    BOTH("I X", true, AV_WHNF, 1, "X");
    BOTH("K X A", true, AV_WHNF, 1, "X");
    BOTH("S X A Z", true, AV_WHNF, 1, "X Z (A Z)");
    BOTH("S K K X", true, AV_WHNF, 2, "X");
}

TEST(extra_arguments_stay_applied) {
    BOTH("K X A Z N", true, AV_WHNF, 1, "X Z N");
    BOTH("I I X", true, AV_WHNF, 2, "X");
}

TEST(unsaturated_heads_and_atoms_are_whnf) {
    BOTH("S X A", true, AV_WHNF, 0, "S X A");
    BOTH("K X", true, AV_WHNF, 0, "K X");
    BOTH("X (I A)", true, AV_WHNF, 0, "X (I A)");
}

TEST(normal_order_discards_divergence) {
    /* K I Ω: the head contracts first and Ω is dropped unevaluated */
    BOTH("K I (S I I (S I I)) X", true, AV_WHNF, 2, "X");
}

TEST(full_normal_form_reduces_under_arguments) {
    BOTH("X (I A) (K Z N)", false, AV_NORMAL, 2, "X A Z");
    BOTH("S (K I)", false, AV_NORMAL, 0, "S (K I)");
    BOTH("K (I (I X))", false, AV_NORMAL, 2, "K X");
}

TEST(s_contractions_need_fuel_s_plus_one) {
    /* S K K X takes 2 contractions; the third attempt finds no redex */
    CHECK(is(run("S K K X", AV_COPY, true, 3), AV_WHNF, 2, "X"));
    CHECK(is(run("S K K X", AV_COPY, true, 2), AV_FUEL, 2, "X"));
    CHECK(is(run("S K K X", AV_COPY, true, 1), AV_FUEL, 1, "K X (K X)"));
    CHECK(is(run("S K K X", AV_COPY, true, 0), AV_FUEL, 0, "S K K X"));
    CHECK(is(run("S K K X", AV_SHARE, true, 3), AV_WHNF, 2, "X"));
    CHECK(is(run("S K K X", AV_SHARE, true, 2), AV_FUEL, 2, "X"));
}

TEST(fuel_stops_under_arguments_with_the_whole_state) {
    /* normal form: X (I A) (I Z) -> X A (I Z) after one contraction */
    CHECK(is(run("X (I A) (I Z)", AV_COPY, false, 1), AV_FUEL, 1, "X A (I Z)"));
}

TEST(divergence_runs_out_of_fuel) {
    outcome o = run("S I I (S I I)", AV_COPY, true, 1000);
    CHECK_EQ(o.status, AV_FUEL);
    CHECK_EQ(o.steps, 1000);
    o = run("S I I (S I I)", AV_SHARE, true, 1000);
    CHECK_EQ(o.status, AV_FUEL);
    CHECK_EQ(o.steps, 1000);
}

TEST(sharing_contracts_a_duplicated_redex_once) {
    /* S (K X) I (I A): copy contracts I A where it is used, share once */
    outcome c = run("S I I (I X)", AV_COPY, false, UINT64_MAX);
    outcome s = run("S I I (I X)", AV_SHARE, false, UINT64_MAX);
    CHECK(strcmp(c.text, "X X") == 0);
    CHECK(strcmp(s.text, "X X") == 0);
    CHECK_EQ(c.steps, 5);
    CHECK_EQ(s.steps, 4);
}

TEST(the_interrupt_flag_stops_the_run) {
    volatile sig_atomic_t flag = 1;
    av_arena *a = av_arena_new(0);
    const char *src = "I X";
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    av_opts o = av_opts_default();
    o.interrupt = &flag;
    av_result r = av_reduce(a, t, &o);
    CHECK_EQ(r.status, AV_INTERRUPTED);
    CHECK_EQ(r.steps, 0);
    av_arena_free(a);
}

/*  -------------------------------------------------- collection under load */

/* n Church twos applied to f and X: "2 2 2 2 f X" is f^65536 X, since
 * the numeral m n is n^m. */
static char *church_power(int n, const char *f) {
    const char *two = "(S (S (K S) K) I)";
    size_t len = strlen(two) * (size_t)n + strlen(f) + 16;
    char *s = malloc(len);
    s[0] = '\0';
    for (int i = 0; i < n; i++) strcat(s, two), strcat(s, " ");
    strcat(s, f);
    strcat(s, " X");
    return s;
}

TEST(a_tiny_arena_collects_and_agrees) {
    char *src = church_power(4, "I");  /* I^65536 X */
    for (int st = 0; st < 2; st++) {
        av_arena *big = av_arena_new(1u << 22), *tiny = av_arena_new(64);
        uint32_t tb = av_parse(big, src, strlen(src), NULL);
        uint32_t tt = av_parse(tiny, src, strlen(src), NULL);
        av_opts o = av_opts_default();
        o.strategy = st ? AV_SHARE : AV_COPY;
        av_result rb = av_reduce(big, tb, &o);
        av_result rt = av_reduce(tiny, tt, &o);
        CHECK_EQ(rb.status, AV_NORMAL);
        CHECK_EQ(rt.status, AV_NORMAL);
        CHECK_EQ(rb.steps, rt.steps);
        CHECK(tiny->collections > 0);
        av_buf b1 = { 0 }, b2 = { 0 };
        CHECK(av_print(big, rb.term, 100, &b1));
        CHECK(av_print(tiny, rt.term, 100, &b2));
        CHECK(strcmp(b1.s, "X") == 0);
        CHECK(strcmp(b2.s, "X") == 0);
        av_buf_free(&b1);
        av_buf_free(&b2);
        av_arena_free(big);
        av_arena_free(tiny);
    }
    free(src);
}

TEST(caller_roots_survive_collection) {
    av_arena *a = av_arena_new(64);
    const char *keep_src = "X (A Z) (K N)";
    uint32_t keep = av_parse(a, keep_src, strlen(keep_src), NULL);
    av_root_push(a, &keep);
    char *src = church_power(3, "I");
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    av_opts o = av_opts_default();
    av_result r = av_reduce(a, t, &o);
    CHECK_EQ(r.status, AV_NORMAL);
    CHECK(a->collections > 0);
    av_buf b = { 0 };
    CHECK(av_print(a, keep, 100, &b));
    CHECK(strcmp(b.s, keep_src) == 0);
    av_buf_free(&b);
    av_root_pop(a);
    av_arena_free(a);
    free(src);
}

TEST(the_node_cap_reports_size) {
    /* K^65536 X: its normal form alone is 131,073 nodes */
    char *src = church_power(4, "K");
    av_arena *a = av_arena_new(64);
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    av_opts o = av_opts_default();
    o.strategy = AV_COPY;
    o.max_nodes = 200;
    av_result r = av_reduce(a, t, &o);
    CHECK_EQ(r.status, AV_SIZE);
    av_arena_free(a);
    free(src);
}

/*  ------------------------------------------ copy against share, at random */

static uint64_t rng = 0x9e3779b97f4a7c15u;
static uint32_t next(void) {
    rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
    return (uint32_t)(rng >> 32);
}

static uint32_t gen(av_arena *a, int depth) {
    if (depth == 0 || next() % 10 < 3) {
        static const char *leaf[] = { "S", "K", "I", "X", "A" };
        const char *nm = leaf[next() % 5];
        return av_leaf(a, nm, strlen(nm));
    }
    uint32_t f = gen(a, depth - 1);
    return av_app(a, f, gen(a, depth - 1));
}

TEST(the_strategies_agree_on_normal_forms) {
    int compared = 0, cases = getenv("AVON_FUZZ") ? atoi(getenv("AVON_FUZZ")) : 20000;
    for (int i = 0; i < cases; i++) {
        av_arena *a = av_arena_new(0);
        uint64_t saved = rng;
        uint32_t t1 = gen(a, 5);
        av_arena *b = av_arena_new(0);
        rng = saved;
        uint32_t t2 = gen(b, 5);
        av_opts o = av_opts_default();
        o.max_steps = 2000;
        o.strategy = AV_COPY;
        av_result rc = av_reduce(a, t1, &o);
        o.strategy = AV_SHARE;
        av_result rs = av_reduce(b, t2, &o);
        if (rc.status == AV_NORMAL) {
            compared++;
            CHECK_EQ(rs.status, AV_NORMAL);
            CHECK(rs.steps <= rc.steps);
            av_buf pc = { 0 }, ps = { 0 };
            bool whole = av_print(a, rc.term, 100000, &pc) &&
                         av_print(b, rs.term, 100000, &ps);
            if (whole && strcmp(pc.s, ps.s) != 0) {
                fprintf(stderr, "  case %d: copy %s, share %s\n", i, pc.s, ps.s);
                CHECK(0);
            }
            av_buf_free(&pc);
            av_buf_free(&ps);
        }
        av_arena_free(a);
        av_arena_free(b);
    }
    CHECK(compared > cases / 2);
}

TEST(a_stopped_state_too_large_to_rebuild_is_size) {
    /* Nested frames, stopped by fuel with the arena full and a node cap
     * too tight to rebuild the state (found by search: fuel 4, cap 16).
     * Before the fix this returned FUEL with no term.  Across the sweep, a
     * FUEL or INTERRUPTED result always carries its term. */
    const char *src = "Z Z I (I K I) (Z S (I K) S) (X S (K Z) Z X) "
                      "(Z S (I Z) (X I (K S)) K (X (X K) (I (X Z)) (K S (I Z) X)))";
    int rebuilt_failed = 0;
    for (uint64_t fuel = 1; fuel < 40; fuel += 3) {
        for (uint32_t cap = 16; cap < 80; cap += 4) {
            av_arena *a = av_arena_new(64);
            uint32_t t = av_parse(a, src, strlen(src), NULL);
            av_opts o = av_opts_default();
            o.strategy = AV_COPY;
            o.max_steps = fuel;
            o.max_nodes = cap;
            av_result r = av_reduce(a, t, &o);
            if (r.status == AV_FUEL || r.status == AV_INTERRUPTED)
                CHECK(r.term != AV_NONE);
            if (r.status == AV_SIZE && r.steps == fuel) rebuilt_failed++;
            av_arena_free(a);
        }
    }
    CHECK(rebuilt_failed > 0);      /* the sweep reaches the case */
}

TEST_MAIN(
    TEST_CASE(each_rule_contracts_once),
    TEST_CASE(extra_arguments_stay_applied),
    TEST_CASE(unsaturated_heads_and_atoms_are_whnf),
    TEST_CASE(normal_order_discards_divergence),
    TEST_CASE(full_normal_form_reduces_under_arguments),
    TEST_CASE(s_contractions_need_fuel_s_plus_one),
    TEST_CASE(fuel_stops_under_arguments_with_the_whole_state),
    TEST_CASE(divergence_runs_out_of_fuel),
    TEST_CASE(sharing_contracts_a_duplicated_redex_once),
    TEST_CASE(the_interrupt_flag_stops_the_run),
    TEST_CASE(a_tiny_arena_collects_and_agrees),
    TEST_CASE(caller_roots_survive_collection),
    TEST_CASE(the_node_cap_reports_size),
    TEST_CASE(a_stopped_state_too_large_to_rebuild_is_size),
    TEST_CASE(the_strategies_agree_on_normal_forms),
)
