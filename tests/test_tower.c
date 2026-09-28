/**  test_tower.c
 *
 *  The paper's targets (docs/DESIGN.md §1, §11 stage 1), from fixtures
 *  exported by aviary_kernel's printer:
 *
 *      T0  whnfF 3 <I K>
 *      T1  whnfF 120 <UQ <I K>>
 *      T2  whnfF 500 <whnfF 3 <I K>>
 *
 *  copy mode must give the reference counts, 340 / 91,556 / 504,930, and
 *  T0's reduced term byte for byte; share mode must reach the same normal
 *  forms.  Run from the repository root.
 */

#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "test.h"

static char *slurp(const char *path, size_t *len) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    char *s = malloc((size_t)n + 1);
    *len = fread(s, 1, (size_t)n, f);
    s[*len] = '\0';
    fclose(f);
    return s;
}

typedef struct { av_result r; char *text; } run_out;

static run_out run(const char *name, av_strategy st, bool whnf, size_t budget) {
    char path[64];
    snprintf(path, sizeof path, "tests/fixtures/%s.ski", name);
    size_t len;
    char *src = slurp(path, &len);
    run_out out = { { AV_NONE, 0, AV_FUEL, 0, 0, false }, NULL };
    if (!src) {
        fprintf(stderr, "  missing %s (run from the repository root)\n", path);
        return out;
    }
    av_arena *a = av_arena_new(1u << 20);
    uint32_t t = av_parse(a, src, len, NULL);
    av_opts o = av_opts_default();
    o.strategy = st;
    o.whnf_only = whnf;
    out.r = av_reduce(a, t, &o);
    av_buf b = { 0 };
    if (budget && av_print(a, out.r.term, budget, &b)) out.text = b.s;
    else av_buf_free(&b);
    av_arena_free(a);
    free(src);
    return out;
}

TEST(copy_mode_reproduces_the_paper) {
    static const struct { const char *name; uint64_t steps; } t[] = {
        { "t0", 340 }, { "t1", 91556 }, { "t2", 504930 },
    };
    for (size_t i = 0; i < 3; i++) {
        run_out o = run(t[i].name, AV_COPY, true, 0);
        CHECK_EQ(o.r.status, AV_WHNF);
        CHECK_EQ(o.r.steps, t[i].steps);
    }
}

TEST(copy_mode_reaches_the_reference_state_on_t0) {
    size_t len;
    char *want = slurp("tests/fixtures/t0.whnf", &len);
    CHECK(want != NULL);
    if (!want) return;
    char *term = strchr(want, '\n') + 1;
    term[strcspn(term, "\n")] = '\0';
    CHECK(strncmp(want, "WHNF 340\n", 9) == 0);
    run_out o = run("t0", AV_COPY, true, 1000000);
    CHECK(o.text && strcmp(o.text, term) == 0);
    free(o.text);
    free(want);
}

TEST(share_mode_counts_are_its_own) {
    /* Reported beside the paper's, never in place of them (§1.1).  They
     * depend on the sharing the input carries, and a printed fixture
     * carries none. */
    static const struct { const char *name; uint64_t steps; } t[] = {
        { "t0", 323 }, { "t1", 63520 }, { "t2", 314309 },
    };
    for (size_t i = 0; i < 3; i++) {
        run_out o = run(t[i].name, AV_SHARE, true, 0);
        CHECK_EQ(o.r.status, AV_WHNF);
        CHECK_EQ(o.r.steps, t[i].steps);
    }
}

TEST(both_strategies_reach_the_same_normal_forms) {
    static const char *names[] = { "t0", "t1", "t2" };
    for (size_t i = 0; i < 3; i++) {
        run_out c = run(names[i], AV_COPY, false, 10000000);
        run_out s = run(names[i], AV_SHARE, false, 10000000);
        CHECK_EQ(c.r.status, AV_NORMAL);
        CHECK_EQ(s.r.status, AV_NORMAL);
        CHECK(c.text && s.text && strcmp(c.text, s.text) == 0);
        free(c.text);
        free(s.text);
    }
}

TEST_MAIN(
    TEST_CASE(copy_mode_reproduces_the_paper),
    TEST_CASE(copy_mode_reaches_the_reference_state_on_t0),
    TEST_CASE(share_mode_counts_are_its_own),
    TEST_CASE(both_strategies_reach_the_same_normal_forms),
)
