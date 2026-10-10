/**  test_conformance.c
 *
 *  Stage 3's acceptance (docs/DESIGN.md §10.2 items 1 and 2, §11): every
 *  target skijack exports -- each level-1 declaration of the corpus, the
 *  EXAMPLES.md §4 fuel boundary, the paper's T3 and scry tables and the
 *  tower -- is reduced to weak head normal form in both strategies, peeled
 *  and decoded by probing, and must give the exported constructor and
 *  rendered payload.  In copy mode the status and the contraction count
 *  must match exactly.  The manifest is python/skijack/export.py's; run from
 *  the repository root.
 */

#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "test.h"

#define DIR "tests/conformance/"

typedef struct {
    unsigned n, app;
    char *name[16];
    unsigned arity[16];
} ctors;

/* "RVal/1 RErr/0 RTime/0", "*App/2" marking the application constructor */
static bool parse_ctors(char *s, ctors *c) {
    c->n = 0;
    c->app = UINT32_MAX;
    for (char *tok = strtok(s, " "); tok; tok = strtok(NULL, " ")) {
        if (c->n == 16) return false;
        if (*tok == '*') { c->app = c->n; tok++; }
        char *slash = strchr(tok, '/');
        if (!slash) return false;
        *slash = '\0';
        c->name[c->n] = tok;
        c->arity[c->n] = (unsigned)atoi(slash + 1);
        c->n++;
    }
    return c->n > 0;
}

static uint8_t *slurp(const char *path, size_t *len) {
    FILE *f = test_open(path);
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *p = malloc((size_t)n + 1);
    *len = fread(p, 1, (size_t)n, f);
    fclose(f);
    return p;
}

typedef struct {
    char *id, *file, *status, *rctors, *octors, *ctor, *payload;
    uint64_t max_steps, steps;
} target;

static size_t targets_checked, values_checked;
static uint64_t jets_fired, interps_fired;
static bool interp_pass;           /* interpreter jets on: counts change */

/*  With `shared` an arena holding the dictionary's jets: the target is
 *  matched against them, run with every fire checked (§6.6), and must give
 *  exactly what it gives without them. */
static void check_target(const target *t, av_strategy st, av_arena *shared) {
    char path[512];
    snprintf(path, sizeof path, DIR "%s", t->file);
    size_t len;
    uint8_t *bytes = slurp(path, &len);
    CHECK(bytes != NULL);
    if (!bytes) return;
    av_arena *a = shared ? shared : av_arena_new(1u << 16);
    const char *err = NULL;
    uint32_t term = av_cue(a, bytes, len, &err);
    free(bytes);
    CHECK(term != AV_NONE);
    if (term == AV_NONE) { if (!shared) av_arena_free(a); return; }
    if (shared) {
        term = av_jets_match(a, term);
        CHECK(term != AV_NONE);
    }

    av_opts o = av_opts_default();
    o.strategy = st;
    o.whnf_only = true;
    o.max_steps = t->max_steps;
    o.jets = shared != NULL;
    o.interp_jets = interp_pass;
    o.jet_check = shared ? 1 : 0;
    av_result r = av_reduce(a, term, &o);
    CHECK(!r.jet_fault);
    jets_fired += r.jet_calls;
    interps_fired += r.interp_calls;
    const char *sname = st == AV_COPY ? "copy" : "share";
    if (strcmp(av_status_name(r.status), t->status) != 0) {
        fprintf(stderr, "  %s (%s): status %s, want %s\n", t->id, sname,
                av_status_name(r.status), t->status);
        CHECK(0);
    }
    if (st == AV_COPY && !interp_pass && r.steps != t->steps) {
        fprintf(stderr, "  %s: %llu contractions, want %llu\n", t->id,
                (unsigned long long)r.steps, (unsigned long long)t->steps);
        CHECK(0);
    }
    targets_checked++;

    if (strcmp(t->ctor, "-") != 0 && r.status == AV_WHNF) {
        char rbuf[512], obuf[512];
        ctors rc, oc;
        snprintf(rbuf, sizeof rbuf, "%s", t->rctors);
        snprintf(obuf, sizeof obuf, "%s", t->octors);
        CHECK(parse_ctors(rbuf, &rc) && parse_ctors(obuf, &oc) && oc.app < oc.n);
        av_opts po = o;
        po.max_steps = 5000000;
        av_peeled p;
        bool peeled = av_peel(a, r.term, rc.n, &po, &p, &err);
        CHECK(peeled);
        if (peeled) {
            if (strcmp(rc.name[p.ctor], t->ctor) != 0) {
                fprintf(stderr, "  %s (%s): %s, want %s\n", t->id, sname,
                        rc.name[p.ctor], t->ctor);
                CHECK(0);
            }
            CHECK_EQ(p.nfields, rc.arity[p.ctor]);
            if (p.nfields > 0) {
                uint32_t d = av_decode(a, p.field[0], oc.n,
                                       (const char *const *)oc.name, oc.app,
                                       200000, &po, &err);
                av_buf b = { 0 };
                bool shown = d != AV_NONE && av_print(a, d, 10000000, &b);
                if (!shown || strcmp(b.s, t->payload) != 0) {
                    fprintf(stderr, "  %s (%s): payload %.60s, want %.60s%s%s\n",
                            t->id, sname, shown ? b.s : "(none)", t->payload,
                            err ? ": " : "", err ? err : "");
                    CHECK(0);
                }
                av_buf_free(&b);
            } else {
                CHECK(strcmp(t->payload, "-") == 0);
            }
            values_checked++;
        }
    }
    if (!shared) av_arena_free(a);
}

typedef void (*visit_fn)(const target *t, void *ctx);

static size_t each_target(visit_fn fn, void *ctx) {
    size_t len;
    char *text = (char *)slurp(DIR "manifest.tsv", &len);
    CHECK(text != NULL);
    if (!text) return 0;
    text[len] = '\0';
    size_t lines = 0;
    for (char *line = text, *next; *line; line = next) {
        next = strchr(line, '\n');
        if (next) *next++ = '\0';
        else next = line + strlen(line);
        char *f[9];
        int k = 0;
        for (char *p = line; k < 9; k++) {
            f[k] = p;
            char *tab = strchr(p, '\t');
            if (!tab) { k++; break; }
            *tab = '\0';
            p = tab + 1;
        }
        CHECK_EQ(k, 9);
        if (k != 9) continue;
        target t = { f[0], f[1], f[3], f[5], f[6], f[7], f[8],
                     strtoull(f[2], NULL, 10), strtoull(f[4], NULL, 10) };
        fn(&t, ctx);
        lines++;
    }
    free(text);
    return lines;
}

static void plain(const target *t, void *ctx) {
    (void)ctx;
    check_target(t, AV_COPY, NULL);
    check_target(t, AV_SHARE, NULL);
}

static void jetted(const target *t, void *ctx) {
    check_target(t, AV_COPY, ctx);
    check_target(t, AV_SHARE, ctx);
}

TEST(every_exported_target_conforms) {
    targets_checked = values_checked = 0;
    size_t lines = each_target(plain, NULL);
    CHECK_EQ(lines, 45);
    printf("  %zu targets, %zu runs, %zu values decoded\n", lines,
           targets_checked, values_checked);
}

/*  Stage 4 (§6.5, §11): the same targets with the corpus dictionary's
 *  residual jets, in one arena for all of them, so the dashboard outlives
 *  collections and both strategies' runs. */
TEST(every_target_conforms_with_jets) {
    av_arena *a = av_arena_new(1u << 16);
    const char *err = NULL;
    CHECK_EQ(av_jets_load(a, DIR "dictionary.tsv", 8, &err), 135);
    targets_checked = values_checked = 0;
    jets_fired = 0;
    size_t lines = each_target(jetted, a);
    CHECK_EQ(lines, 45);
    CHECK_EQ(values_checked, 86);
    CHECK(jets_fired > 0);
    printf("  jets on: %zu runs, %zu values decoded, %llu jets fired, %llu collections\n",
           targets_checked, values_checked, (unsigned long long)jets_fired,
           (unsigned long long)a->collections);
    av_arena_free(a);
}

/*  Stage 5 (§7, §11): the same targets with interpreter jets too.  They
 *  change counts, so only statuses and values are compared -- and every
 *  fire is checked against the unjetted interpreter. */
TEST(every_target_conforms_with_interpreter_jets) {
    av_arena *a = av_arena_new(1u << 16);
    const char *err = NULL;
    CHECK_EQ(av_jets_load(a, DIR "dictionary.tsv", 8, &err), 135);
    CHECK_EQ(av_interps_load(a, DIR "interpreters.tsv", DIR "dictionary.tsv", &err), 5);
    targets_checked = values_checked = 0;
    jets_fired = interps_fired = 0;
    interp_pass = true;
    size_t lines = each_target(jetted, a);
    interp_pass = false;
    CHECK_EQ(lines, 45);
    CHECK_EQ(values_checked, 86);
    CHECK(interps_fired > 0);
    printf("  interpreter jets on: %zu runs, %zu values decoded, %llu interpreter fires\n",
           targets_checked, values_checked, (unsigned long long)interps_fired);
    av_arena_free(a);
}

TEST_MAIN(
    TEST_CASE(every_exported_target_conforms),
    TEST_CASE(every_target_conforms_with_jets),
    TEST_CASE(every_target_conforms_with_interpreter_jets),
)
