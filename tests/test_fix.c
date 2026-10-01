/**  test_fix.c
 *
 *  Y unfolded in one step (docs/DESIGN.md §6.11): with av_opts.fix, share
 *  mode rewrites Y g, Curry's Y at the head with an argument, to g (Y g), a
 *  fresh Y g.  Convertible, not a reduct, and acyclic.
 *
 *  - A normal form is the unjetted one, in fewer steps.
 *  - A term with no normal form still stops at FUEL, at exactly the fuel
 *    given: Y K, Y I, Y (S I I).
 *  - The data-jet fixtures (tests/data/) answer and normalize as without.
 *  - Collections keep the answer; copy mode ignores fix; Y with no argument
 *    is left alone; Y g to weak head normal form is g (Y g), the one place
 *    the state's form differs, pinned here.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "avon.h"
#include "test.h"

#define Y "S (K (S I I)) (S (S (K S) K) (K (S I I)))"

static char *slurp(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    rewind(f);
    char *s = malloc((size_t)n + 1);
    if (s && fread(s, 1, (size_t)n, f) != (size_t)n) { free(s); s = NULL; }
    if (s) s[n] = '\0';
    fclose(f);
    return s;
}

/*  An empty template directory: Y is registered with a template load. */
static void empty_dir(char dir[64]) {
    strcpy(dir, "/tmp/avon-fix-XXXXXX");
    CHECK(mkdtemp(dir) != NULL);
    const char *files[2] = { "templates.tsv", "template_terms.tsv" };
    for (int i = 0; i < 2; i++) {
        char path[128];
        snprintf(path, sizeof path, "%s/%s", dir, files[i]);
        FILE *f = fopen(path, "w");
        fclose(f);
    }
}

static void rm_dir(const char *dir) {
    const char *files[2] = { "templates.tsv", "template_terms.tsv" };
    for (int i = 0; i < 2; i++) {
        char path[128];
        snprintf(path, sizeof path, "%s/%s", dir, files[i]);
        unlink(path);
    }
    rmdir(dir);
}

typedef struct {
    av_status status;
    uint64_t  steps, fix_calls, collections;
    bool      registered;
    char      nf[1 << 16];
} outcome;

/*  src reduced; with dir, its templates loaded, data jets on, and fix when
 *  asked. */
static outcome run(const char *src, const char *dir, bool fix, av_strategy st,
                   bool whnf, uint64_t fuel, uint32_t cap) {
    static outcome out;
    memset(&out, 0, sizeof out);
    av_arena *a = av_arena_new(cap);
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    CHECK(t != AV_NONE);
    if (dir) {
        CHECK(av_words_on(a));
        if (fix) av_fix_on(a);
        const char *err = NULL;
        av_tmplset *ts = av_templates_load(a, dir, &err);
        CHECK(ts != NULL);
        if (ts) {
            out.registered = av_templates_fix(ts);
            t = av_jets_match(a, t);
            CHECK(av_templates_bind(a, ts, t));
            CHECK(av_words_scan(a, t) >= 0);
            CHECK(av_words_mark(a));
            av_templates_free(ts);
        }
    }
    av_opts o = av_opts_default();
    o.strategy = st;
    o.whnf_only = whnf;
    o.max_steps = fuel;
    o.templates = dir != NULL;
    o.data = dir != NULL;
    o.fix = fix;
    av_root_push(a, &t);
    av_result r = av_reduce(a, t, &o);
    av_root_pop(a);
    out.status = r.status;
    out.steps = r.steps;
    out.fix_calls = r.fix_calls;
    out.collections = a->collections;
    av_buf b = { 0 };
    if (r.term != AV_NONE && av_print(a, r.term, 1000000, &b) && b.len < sizeof out.nf)
        memcpy(out.nf, b.s, b.len + 1);
    av_buf_free(&b);
    av_arena_free(a);
    return out;
}

TEST(a_normal_form_is_the_unjetted_one_in_fewer_steps) {
    char d[64];
    empty_dir(d);
    const char *srcs[2] = { "(" Y ") (K x)", "(" Y ") (K (K y)) z" };
    const char *want[2] = { "x", "y" };
    for (int i = 0; i < 2; i++) {
        outcome plain = run(srcs[i], NULL, false, AV_SHARE, false, 1000, 1u << 10);
        uint64_t plain_steps = plain.steps;
        CHECK(plain.status == AV_NORMAL && strcmp(plain.nf, want[i]) == 0);
        outcome fx = run(srcs[i], d, true, AV_SHARE, false, 1000, 1u << 10);
        CHECK(fx.registered);
        CHECK(fx.status == AV_NORMAL && strcmp(fx.nf, want[i]) == 0);
        CHECK_EQ(fx.fix_calls, 1);
        CHECK(fx.steps < plain_steps);
    }
    rm_dir(d);
}

TEST(no_normal_form_still_stops_at_its_fuel) {
    char d[64];
    empty_dir(d);
    const char *srcs[3] = { "(" Y ") K", "(" Y ") I", "(" Y ") (S I I)" };
    for (int i = 0; i < 3; i++) {
        for (int whnf = 0; whnf < 2; whnf++) {
            if (i == 0 && whnf) continue;               /* Y K has a head normal form */
            outcome plain = run(srcs[i], NULL, false, AV_SHARE, whnf, 1000, 1u << 10);
            CHECK_EQ(plain.status, AV_FUEL);
            outcome fx = run(srcs[i], d, true, AV_SHARE, whnf, 1000, 1u << 10);
            CHECK_EQ(fx.status, AV_FUEL);
            CHECK_EQ(fx.steps, 1000);
            CHECK(fx.fix_calls > 0);
        }
    }
    rm_dir(d);
}

TEST(y_to_head_normal_form_is_g_of_a_fresh_y) {
    /* the one documented difference: the state reached, not its value */
    char d[64];
    empty_dir(d);
    outcome fx = run("(" Y ") K", d, true, AV_SHARE, true, 1000, 1u << 10);
    CHECK_EQ(fx.status, AV_WHNF);
    CHECK_EQ(fx.steps, 1);
    CHECK(strcmp(fx.nf, "K (" Y " K)") == 0);
    rm_dir(d);
}

TEST(y_short_of_its_argument_is_left_alone) {
    char d[64];
    empty_dir(d);
    outcome plain = run(Y, NULL, false, AV_SHARE, false, 1000, 1u << 10);
    outcome fx = run(Y, d, true, AV_SHARE, false, 1000, 1u << 10);
    CHECK_EQ(fx.fix_calls, 0);
    CHECK_EQ(fx.status, plain.status);
    CHECK(strcmp(fx.nf, plain.nf) == 0);
    rm_dir(d);
}

TEST(copy_mode_ignores_fix) {
    char d[64];
    empty_dir(d);
    const char *src = "(" Y ") (K (K y)) z";
    outcome plain = run(src, NULL, false, AV_COPY, false, 1000, 1u << 10);
    outcome fx = run(src, d, true, AV_COPY, false, 1000, 1u << 10);
    CHECK_EQ(fx.fix_calls, 0);
    CHECK_EQ(fx.steps, plain.steps);
    CHECK(strcmp(fx.nf, plain.nf) == 0);
    rm_dir(d);
}

static char *fixture(const char *prog, const char *name) {
    char path[128];
    snprintf(path, sizeof path, "tests/data/%s/%s.txt", prog, name);
    char *s = slurp(path);
    CHECK(s != NULL);
    if (s) s[strcspn(s, "\n")] = '\0';
    return s;
}

TEST(the_fixtures_answer_and_normalize_as_without) {
    const char *progs[2] = { "lists", "nats" };
    for (int i = 0; i < 2; i++) {
        char dir[64];
        snprintf(dir, sizeof dir, "tests/data/%s", progs[i]);
        char *main_src = fixture(progs[i], "main"), *out_src = fixture(progs[i], "out");
        if (!main_src || !out_src) { free(main_src); free(out_src); continue; }
        outcome fx = run(main_src, dir, true, AV_SHARE, true, 10000000, 1u << 12);
        CHECK(fx.status == AV_WHNF && strcmp(fx.nf, "Ff") == 0);
        CHECK(fx.fix_calls > 0);
        outcome plain = run(out_src, NULL, false, AV_SHARE, false, 100000000, 1u << 12);
        static char want[1 << 16];
        strcpy(want, plain.nf);
        CHECK(plain.status == AV_NORMAL);
        outcome fn = run(out_src, dir, true, AV_SHARE, false, 100000000, 1u << 12);
        CHECK_EQ(fn.status, AV_NORMAL);
        CHECK(strcmp(fn.nf, want) == 0);
        free(main_src);
        free(out_src);
    }
}

TEST(collections_keep_the_answer) {
    char *src = fixture("nats", "main");
    if (!src) return;
    outcome fx = run(src, "tests/data/nats", true, AV_SHARE, true, 10000000, 1u << 8);
    CHECK_EQ(fx.status, AV_WHNF);
    CHECK(strcmp(fx.nf, "Ff") == 0);
    CHECK(fx.collections > 0);
    CHECK(fx.fix_calls > 0);
    free(src);
}

TEST_MAIN(
    TEST_CASE(a_normal_form_is_the_unjetted_one_in_fewer_steps),
    TEST_CASE(no_normal_form_still_stops_at_its_fuel),
    TEST_CASE(y_to_head_normal_form_is_g_of_a_fresh_y),
    TEST_CASE(y_short_of_its_argument_is_left_alone),
    TEST_CASE(copy_mode_ignores_fix),
    TEST_CASE(the_fixtures_answer_and_normalize_as_without),
    TEST_CASE(collections_keep_the_answer)
)
