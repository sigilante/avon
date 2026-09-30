/**  test_templates.c
 *
 *  Supercombinator templates (docs/DESIGN.md §6.9), on hand-made template
 *  files.  B's template -- formals f g x, body f (g x) -- has the key
 *  S (K S) K; M's -- x, x x -- has S I I.
 *
 *  - Where the key meets its arguments in share mode the body is
 *    instantiated, one step, and the normal form is the unjetted one.
 *  - A body that does not abstract to its key is refused, and the term runs
 *    as pure SKI; an η-template, an open body and a leaf key are skipped.
 *  - Copy mode ignores templates: its counts are the unjetted ones.
 *  - Short of its arguments the key's term is entered and its node stays a
 *    jet node, not demoted: the next full application of it fires.
 *  - Fuel stops a looping template program; collections keep the globals.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "avon.h"
#include "test.h"

#define B_KEY  "S (K S) K"
#define M_KEY  "S I I"

static void hash_of(const char *term, char h[27]) {
    av_arena *a = av_arena_new(1u << 10);
    CHECK(av_structural_hash(a, av_parse(a, term, strlen(term), NULL), h));
    av_arena_free(a);
}

/*  A template directory: templates.tsv lines "KEYTERM|k|formals|body",
 *  the key given as a term and hashed here; template_terms.tsv empty or
 *  holding refs, each given as a term. */
static void tdir(char dir[64], const char *const *lines, int n,
                 const char *const *refs, int nrefs) {
    strcpy(dir, "/tmp/avon-tmpl-XXXXXX");
    CHECK(mkdtemp(dir) != NULL);
    char path[128];
    snprintf(path, sizeof path, "%s/templates.tsv", dir);
    FILE *f = fopen(path, "w");
    for (int i = 0; i < n; i++) {
        char key[128], k[8], formals[64], body[256], h[27];
        CHECK(sscanf(lines[i], "%127[^|]|%7[^|]|%63[^|]|%255[^\n]", key, k, formals, body) == 4);
        hash_of(key, h);
        fprintf(f, "%s\ttest\tt%d\t%s\t%s\t%s\n", h, i, k, formals, body);
    }
    fclose(f);
    snprintf(path, sizeof path, "%s/template_terms.tsv", dir);
    f = fopen(path, "w");
    for (int i = 0; i < nrefs; i++) {
        char h[27];
        hash_of(refs[i], h);
        fprintf(f, "%s\t0\t%s\n", h, refs[i]);
    }
    fclose(f);
}

static void rmdir_all(const char *dir) {
    char path[128];
    snprintf(path, sizeof path, "%s/templates.tsv", dir);
    unlink(path);
    snprintf(path, sizeof path, "%s/template_terms.tsv", dir);
    unlink(path);
    rmdir(dir);
}

typedef struct {
    av_status status;
    uint64_t  steps, tmpl_calls, collections;
    long      accepted, refused, skipped, unbound;
    char      nf[1 << 16];
} outcome;

/*  src reduced in mode, with dir's templates when dir is not NULL. */
static outcome run(const char *src, const char *dir, av_strategy mode, bool whnf,
                   uint64_t fuel, uint32_t cap) {
    outcome out = { 0 };
    av_arena *a = av_arena_new(cap);
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    CHECK(t != AV_NONE);
    if (dir) {
        const char *err = NULL;
        av_tmplset *ts = av_templates_load(a, dir, &err);
        CHECK(ts != NULL);
        if (ts) {
            t = av_jets_match(a, t);
            CHECK(av_templates_bind(a, ts, t));
            av_templates_counts(ts, &out.accepted, &out.refused, &out.skipped, &out.unbound);
            av_templates_free(ts);
        }
    }
    av_opts o = av_opts_default();
    o.strategy = mode;
    o.whnf_only = whnf;
    o.max_steps = fuel;
    o.templates = dir != NULL;
    av_root_push(a, &t);
    av_result r = av_reduce(a, t, &o);
    av_root_pop(a);
    out.status = r.status;
    out.steps = r.steps;
    out.tmpl_calls = r.tmpl_calls;
    out.collections = a->collections;
    av_buf b = { 0 };
    if (r.term != AV_NONE && av_print(a, r.term, 100000, &b) && b.len < sizeof out.nf)
        memcpy(out.nf, b.s, b.len + 1);
    av_buf_free(&b);
    av_arena_free(a);
    return out;
}

TEST(a_template_fires_where_its_key_meets_its_arguments) {
    const char *lines[1] = { B_KEY "|3|0,1,2|`v0 `v1 v2" };
    char d[64];
    tdir(d, lines, 1, NULL, 0);
    outcome plain = run(B_KEY " f g x", NULL, AV_SHARE, false, 1000, 1u << 10);
    outcome jet = run(B_KEY " f g x", d, AV_SHARE, false, 1000, 1u << 10);
    CHECK_EQ(jet.accepted, 1);
    CHECK_EQ(jet.refused, 0);
    CHECK(strcmp(plain.nf, "f (g x)") == 0);
    CHECK(strcmp(jet.nf, plain.nf) == 0);
    CHECK_EQ(jet.tmpl_calls, 1);
    CHECK_EQ(jet.steps, 1);
    CHECK(plain.steps > 1);
    rmdir_all(d);
}

TEST(a_body_that_is_not_its_key_is_refused) {
    const char *lines[1] = { B_KEY "|3|0,1,2|`v1 `v0 v2" };    /* C, not B */
    char d[64];
    tdir(d, lines, 1, NULL, 0);
    outcome plain = run(B_KEY " f g x", NULL, AV_SHARE, false, 1000, 1u << 10);
    outcome jet = run(B_KEY " f g x", d, AV_SHARE, false, 1000, 1u << 10);
    CHECK_EQ(jet.accepted, 0);
    CHECK_EQ(jet.refused, 1);
    CHECK_EQ(jet.tmpl_calls, 0);
    CHECK(strcmp(jet.nf, plain.nf) == 0);
    CHECK_EQ(jet.steps, plain.steps);                /* pure SKI */
    rmdir_all(d);
}

TEST(eta_open_and_leaf_templates_are_skipped) {
    /* η: λx. B x compiles to B itself; open: v1 is no formal; a leaf key:
     * λx y. x is K */
    char b_hash[27], eta[128];
    hash_of(B_KEY, b_hash);
    snprintf(eta, sizeof eta, B_KEY "|1|0|`#%s v0", b_hash + 10);
    const char *lines[3] = { eta, "K|1|0|v1", "K|2|0,1|v0" };
    const char *refs[1] = { B_KEY };
    char d[64];
    tdir(d, lines, 3, refs, 1);
    outcome jet = run(B_KEY " f g x", d, AV_SHARE, false, 1000, 1u << 10);
    CHECK_EQ(jet.accepted, 0);
    CHECK_EQ(jet.refused, 0);
    CHECK_EQ(jet.skipped, 3);
    CHECK_EQ(jet.tmpl_calls, 0);
    rmdir_all(d);
}

TEST(copy_mode_ignores_templates) {
    const char *lines[1] = { B_KEY "|3|0,1,2|`v0 `v1 v2" };
    char d[64];
    tdir(d, lines, 1, NULL, 0);
    outcome plain = run(B_KEY " f g x", NULL, AV_COPY, false, 1000, 1u << 10);
    outcome jet = run(B_KEY " f g x", d, AV_COPY, false, 1000, 1u << 10);
    CHECK_EQ(jet.tmpl_calls, 0);
    CHECK_EQ(jet.steps, plain.steps);
    CHECK(strcmp(jet.nf, plain.nf) == 0);
    rmdir_all(d);
}

TEST(short_of_its_arguments_the_key_stays_a_root) {
    /* B f g, reduced to weak head normal form, reaches B's node with two
     * of its three arguments: a miss.  The node must stay a jet node, not
     * be demoted to an indirection, so the same node applied to three
     * arguments afterwards fires. */
    const char *lines[1] = { B_KEY "|3|0,1,2|`v0 `v1 v2" };
    char d[64];
    tdir(d, lines, 1, NULL, 0);
    av_arena *a = av_arena_new(1u << 10);
    const char *src = B_KEY " f g";
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    const char *err = NULL;
    av_tmplset *ts = av_templates_load(a, d, &err);
    CHECK(ts != NULL);
    t = av_jets_match(a, t);
    CHECK(av_templates_bind(a, ts, t));
    av_templates_free(ts);
    uint32_t j = av_left(a, av_left(a, t));             /* B's node */
    CHECK_EQ(av_tag(a, j), AV_JET);
    av_opts o = av_opts_default();
    o.whnf_only = true;
    o.templates = true;
    av_root_push(a, &j);
    av_result r1 = av_reduce(a, t, &o);
    CHECK_EQ(r1.tmpl_calls, 0);
    CHECK_EQ(av_tag(a, j), AV_JET);                     /* not demoted */
    uint32_t again = av_app(a, av_app(a, av_app(a, j, av_leaf(a, "f", 1)),
                                      av_leaf(a, "g", 1)), av_leaf(a, "x", 1));
    av_result r2 = av_reduce(a, again, &o);
    av_root_pop(a);
    CHECK_EQ(r2.tmpl_calls, 1);
    av_buf b = { 0 };
    CHECK(av_print(a, r2.term, 1000, &b) && strcmp(b.s, "f (g x)") == 0);
    av_buf_free(&b);
    av_arena_free(a);
    rmdir_all(d);
}

TEST(fuel_stops_a_looping_template_program) {
    const char *lines[1] = { M_KEY "|1|0|`v0 v0" };
    char d[64];
    tdir(d, lines, 1, NULL, 0);
    outcome jet = run(M_KEY " (" M_KEY ")", d, AV_SHARE, true, 500, 1u << 10);
    CHECK_EQ(jet.status, AV_FUEL);
    CHECK_EQ(jet.steps, 500);
    CHECK(jet.tmpl_calls > 0);
    rmdir_all(d);
}

/*  Occurrences of needle in hay. */
static int count(const char *hay, const char *needle) {
    int n = 0;
    for (const char *p = hay; (p = strstr(p, needle)); p += strlen(needle)) n++;
    return n;
}

TEST(collections_keep_the_globals) {
    /* W = λx. x x B, a body with a global: its key is S (S I I) (K B).
     * W W fires to W W B, and again to W W B B: after n fires the term is
     * W W B .. B, B's text n + 2 times (once in each W).  Its live set
     * grows, so a 256-node arena collects, and every instance points at the
     * one global B: a pointer left stale would print as something else. */
    char b_hash[27], line[160];
    hash_of(B_KEY, b_hash);
    snprintf(line, sizeof line, "S (S I I) (K (" B_KEY "))|1|0|``v0 v0 #%s", b_hash + 10);
    const char *lines[1] = { line };
    const char *refs[1] = { B_KEY };
    char d[64];
    tdir(d, lines, 1, refs, 1);
    const char *w = "S (S I I) (K (" B_KEY "))";
    char src[256];
    snprintf(src, sizeof src, "%s (%s)", w, w);
    outcome jet = run(src, d, AV_SHARE, true, 2000, 1u << 8);
    CHECK_EQ(jet.accepted, 1);
    CHECK_EQ(jet.status, AV_FUEL);
    CHECK_EQ(jet.tmpl_calls, 2000);
    CHECK(jet.collections > 0);
    CHECK_EQ(count(jet.nf, B_KEY), 2000 + 2);
    rmdir_all(d);
}

TEST_MAIN(
    TEST_CASE(a_template_fires_where_its_key_meets_its_arguments),
    TEST_CASE(a_body_that_is_not_its_key_is_refused),
    TEST_CASE(eta_open_and_leaf_templates_are_skipped),
    TEST_CASE(copy_mode_ignores_templates),
    TEST_CASE(short_of_its_arguments_the_key_stays_a_root),
    TEST_CASE(fuel_stops_a_looping_template_program),
    TEST_CASE(collections_keep_the_globals)
)
