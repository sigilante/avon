/**  test_jetstats.c
 *
 *  Jet stats (docs/DESIGN.md §6.7): each jet's fires, misses and
 *  demotions, and each fire's origin, on programs whose every contraction
 *  is worked out by hand.  M = S I I (M a = a a) is the inner jet.
 *
 *  - X1 = S (K S) K I, B I, holds B = S (K S) K: on X1 g x the outer fires
 *    from the top and B, alone a fire, does nothing -- eaten.
 *  - X = K (S I (K M)): X a b reaches b (K M b), so its residual carries M;
 *    on X z I w, X fires and then M fires from X's residual.
 *  - X z: one argument short of X's two, a miss; in share mode a demotion
 *    of the program's own node, so no copy.
 *  - X2 = S (K M) (K (K I)), arity 2: X2 z misses, its term is entered, and
 *    M fires there with one argument, from X2's term.
 *  - Three hundred X z I w in a 256-node arena: the origins follow the
 *    nodes through collections.
 *  Every copy-mode run must count the unjetted contractions.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "avon.h"
#include "test.h"

#define X1_TERM "S (K S) K I"
#define B_TERM  "S (K S) K"
#define M_TERM  "S I I"
#define X_TERM  "K (S I (K (S I I)))"
#define X2_TERM "S (K (S I I)) (K (K I))"

static uint32_t parse(av_arena *a, const char *s) {
    return av_parse(a, s, strlen(s), NULL);
}

/*  A dictionary of the given terms, in a temporary file. */
static void dictionary(char path[64], const char *const *terms, int n) {
    strcpy(path, "/tmp/avon-jetstats-XXXXXX");
    int fd = mkstemp(path);
    FILE *f = fdopen(fd, "w");
    av_arena *a = av_arena_new(1u << 10);
    for (int i = 0; i < n; i++) {
        char h[27];
        CHECK(av_structural_hash(a, parse(a, terms[i]), h));
        fprintf(f, "%s\t0\t%s\n", h, terms[i]);
    }
    av_arena_free(a);
    fclose(f);
}

static void hash_of(const char *term, char h[27]) {
    av_arena *a = av_arena_new(1u << 10);
    CHECK(av_structural_hash(a, parse(a, term), h));
    av_arena_free(a);
}

static av_jetstat_row row(const av_jetstats *s, const char *term) {
    char h[27], got[27];
    hash_of(term, h);
    size_t i;
    av_jetstat_row c = { 0 };
    if (!av_jetstats_find(s, h, &i)) return c;
    unsigned arity;
    uint64_t cost;
    size_t atoms;
    av_jetstats_row(s, i, got, &arity, &cost, &atoms, &c);
    return c;
}

static uint64_t collections;             /* the last run's */

/*  Run src with the dictionary's jets, into s; the contractions. */
static uint64_t run(const char *dict, const char *src, av_strategy mode, bool whnf,
                    uint32_t cap, av_jetstats *s) {
    av_arena *a = av_arena_new(cap);
    const char *err = NULL;
    long n = dict ? av_jets_load(a, dict, 1, &err) : 0;
    CHECK(n >= 0);
    uint32_t t = parse(a, src);
    if (dict) t = av_jets_match(a, t);
    CHECK(t != AV_NONE);
    if (s) CHECK(av_jetstats_begin(s, a, t));
    av_opts o = av_opts_default();
    o.strategy = mode;
    o.whnf_only = whnf;
    o.jets = dict != NULL;
    o.jetstats = s;
    av_root_push(a, &t);
    av_result r = av_reduce(a, t, &o);
    av_root_pop(a);
    CHECK(r.status == AV_WHNF || r.status == AV_NORMAL);
    collections = a->collections;
    av_arena_free(a);
    return r.steps;
}

TEST(an_outer_jet_eats_its_inner_one) {
    const char *both[2] = { X1_TERM, B_TERM }, *alone[1] = { B_TERM };
    char d2[64], d1[64];
    dictionary(d2, both, 2);
    dictionary(d1, alone, 1);
    for (int m = 0; m < 2; m++) {
        av_strategy mode = m ? AV_SHARE : AV_COPY;
        av_jetstats *s = av_jetstats_new(), *b = av_jetstats_new();
        uint64_t plain = run(NULL, X1_TERM " g x", AV_COPY, true, 1u << 10, NULL);
        uint64_t steps = run(d2, X1_TERM " g x", mode, true, 1u << 10, s);
        if (mode == AV_COPY) CHECK_EQ(steps, plain);
        CHECK_EQ(row(s, X1_TERM).fires, 1);
        CHECK_EQ(row(s, X1_TERM).top, 1);
        CHECK_EQ(row(s, B_TERM).fires, 0);
        run(d1, X1_TERM " g x", mode, true, 1u << 10, b);
        CHECK_EQ(row(b, B_TERM).fires, 1);             /* alone, it fires */
        CHECK_EQ(row(b, B_TERM).top, 1);
        av_jetstats_free(s);
        av_jetstats_free(b);
    }
    unlink(d2);
    unlink(d1);
}

TEST(a_fire_inside_another_jets_residual) {
    const char *terms[2] = { X_TERM, M_TERM };
    char d[64];
    dictionary(d, terms, 2);
    for (int m = 0; m < 2; m++) {
        av_strategy mode = m ? AV_SHARE : AV_COPY;
        av_jetstats *s = av_jetstats_new();
        uint64_t plain = run(NULL, X_TERM " z I w", AV_COPY, true, 1u << 10, NULL);
        uint64_t steps = run(d, X_TERM " z I w", mode, true, 1u << 10, s);
        if (mode == AV_COPY) CHECK_EQ(steps, plain);
        CHECK_EQ(row(s, X_TERM).fires, 1);
        CHECK_EQ(row(s, X_TERM).top, 1);
        CHECK_EQ(row(s, M_TERM).fires, 1);
        CHECK_EQ(row(s, M_TERM).in_residual, 1);
        av_jetstat_pair *p;
        size_t n = av_jetstats_pairs(s, &p);
        CHECK_EQ(n, 1);
        if (n == 1) {
            CHECK_EQ(p[0].kind, AV_FROM_RESIDUAL);
            CHECK_EQ(p[0].fires, 1);
        }
        free(p);
        av_jetstats_free(s);
    }
    unlink(d);
}

TEST(a_miss_and_in_share_mode_a_demotion) {
    const char *terms[2] = { X_TERM, M_TERM };
    char d[64];
    dictionary(d, terms, 2);
    for (int m = 0; m < 2; m++) {
        av_strategy mode = m ? AV_SHARE : AV_COPY;
        av_jetstats *s = av_jetstats_new();
        run(d, X_TERM " z", mode, true, 1u << 10, s);
        CHECK_EQ(row(s, X_TERM).fires, 0);
        CHECK_EQ(row(s, X_TERM).misses, 1);
        CHECK_EQ(row(s, X_TERM).demotions, mode == AV_SHARE ? 1 : 0);
        CHECK_EQ(row(s, X_TERM).copies, 0);             /* the program's node */
        av_jetstats_free(s);
    }
    unlink(d);
}

TEST(a_fire_inside_another_jets_term) {
    const char *terms[2] = { X2_TERM, M_TERM };
    char d[64];
    dictionary(d, terms, 2);
    for (int m = 0; m < 2; m++) {
        av_strategy mode = m ? AV_SHARE : AV_COPY;
        av_jetstats *s = av_jetstats_new();
        uint64_t plain = run(NULL, X2_TERM " z", AV_COPY, true, 1u << 10, NULL);
        uint64_t steps = run(d, X2_TERM " z", mode, true, 1u << 10, s);
        if (mode == AV_COPY) CHECK_EQ(steps, plain);
        CHECK_EQ(row(s, X2_TERM).fires, 0);
        CHECK_EQ(row(s, X2_TERM).misses, 1);
        CHECK_EQ(row(s, M_TERM).fires, 1);
        CHECK_EQ(row(s, M_TERM).in_term, 1);
        av_jetstats_free(s);
    }
    unlink(d);
}

TEST(origins_follow_the_nodes_through_collections) {
    const char *terms[2] = { X_TERM, M_TERM };
    char d[64];
    dictionary(d, terms, 2);
    enum { N = 300 };
    size_t len = N * (strlen(X_TERM) + 16) + 8;
    char *src = malloc(len);
    size_t at = (size_t)snprintf(src, len, "c");
    for (int i = 0; i < N; i++)
        at += (size_t)snprintf(src + at, len - at, " (" X_TERM " z I w)");
    for (int m = 0; m < 2; m++) {
        av_strategy mode = m ? AV_SHARE : AV_COPY;
        av_jetstats *s = av_jetstats_new();
        uint64_t plain = run(NULL, src, AV_COPY, false, 1u << 8, NULL);
        uint64_t steps = run(d, src, mode, false, 1u << 8, s);
        CHECK(collections > 0);
        if (mode == AV_COPY) CHECK_EQ(steps, plain);
        CHECK_EQ(row(s, X_TERM).fires, N);
        CHECK_EQ(row(s, X_TERM).top, N);
        CHECK_EQ(row(s, M_TERM).fires, N);
        CHECK_EQ(row(s, M_TERM).in_residual, N);
        CHECK(!av_jetstats_lost(s));
        av_jetstats_free(s);
    }
    free(src);
    unlink(d);
}

TEST_MAIN(
    TEST_CASE(an_outer_jet_eats_its_inner_one),
    TEST_CASE(a_fire_inside_another_jets_residual),
    TEST_CASE(a_miss_and_in_share_mode_a_demotion),
    TEST_CASE(a_fire_inside_another_jets_term),
    TEST_CASE(origins_follow_the_nodes_through_collections)
)
