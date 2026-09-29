/**  test_selfhost.c
 *
 *  Stage 8 (docs/DESIGN.md §20.3): the compiler's core, bracket
 *  abstraction written in SKIjack (tests/selfhost/abstract.ascii.ski), run
 *  as a term in Avon, reproduces every abstraction skijack performed
 *  compiling that same source -- the fixed point -- result for result,
 *  text and hash; and so does its jet, native abstraction, every fire
 *  checked against the term.  A term that does not abstract as aviary does
 *  is not admitted as the compiler.  Run from the repository root;
 *  tests/selfhost_check.sh runs the corpus.
 */

#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "test.h"

#define DIR "tests/selfhost/"

static uint8_t *slurp(const char *path, size_t *len) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *p = malloc((size_t)n + 1);
    *len = fread(p, 1, (size_t)n, f);
    p[*len] = 0;
    fclose(f);
    return p;
}

static uint32_t load(av_arena *a, const char *name) {
    char path[256];
    snprintf(path, sizeof path, DIR "%s.skit", name);
    size_t len;
    uint8_t *b = slurp(path, &len);
    uint32_t t = b ? av_cue(a, b, len, NULL) : AV_NONE;
    free(b);
    return t;
}

static av_compiler compiler(av_arena *a) {
    av_compiler c = {
        load(a, "abs"), load(a, "TS"), load(a, "TK"), load(a, "TI"), load(a, "TV"),
        load(a, "TA"), load(a, "Ap"), load(a, "Zero"), load(a, "Suc"),
    };
    return c;
}

typedef struct { uint64_t calls, same, steps, fires; } tally;

/*  Every line of own.tsv through abs, jets as o says. */
static void run_calls(const av_opts *o, bool jet, tally *t) {
    size_t len;
    char *text = (char *)slurp(DIR "own.tsv", &len);
    CHECK(text != NULL);
    if (!text) return;
    for (char *line = text, *nl; *line; line = nl) {
        nl = strchr(line, '\n');
        if (nl) *nl++ = '\0';
        char *fld[4];
        int k = 0;
        for (char *p = line; k < 4 && p; k++) {
            fld[k] = p;
            p = strchr(p, '\t');
            if (p) *p++ = '\0';
        }
        CHECK_EQ(k, 4);
        av_arena *a = av_arena_new(1u << 16);
        av_compiler c = compiler(a);
        const char *err = NULL;
        CHECK(av_compiler_register(a, &c, &err));
        av_compiler k2;
        memcpy(&k2, a->compiler, sizeof k2);
        uint32_t body = av_parse(a, fld[1], strlen(fld[1]), NULL);
        uint32_t d = body == AV_NONE ? AV_NONE : av_tm_encode(a, &k2, body);
        uint32_t x = av_tm_nat(a, &k2, strtoull(fld[0], NULL, 10));
        uint32_t q = av_app(a, av_app(a, k2.abs, x), d);
        q = av_jets_match(a, q);
        av_opts ro = *o;
        uint64_t p0 = a->probe_steps;
        av_result r = av_reduce(a, q, &ro);       /* to the head: a tm datum */
        CHECK_EQ(r.status, AV_WHNF);
        CHECK(!r.jet_fault);
        av_root_push(a, &r.term);
        ro.compile_jets = false;                  /* decoding reads, never fires */
        uint32_t out = av_tm_decode(a, r.term, &ro, &err);
        av_root_pop(a);
        CHECK(out != AV_NONE);
        av_buf b = { 0 };
        char h[27];
        bool same = out != AV_NONE && av_print(a, out, 10000000, &b) && strcmp(b.s, fld[3]) == 0 &&
                    av_structural_hash(a, out, h) && strcmp(h, fld[2]) == 0;
        if (!same) fprintf(stderr, "  [v%s] %.60s:\n    got  %.80s\n    want %.80s\n", fld[0], fld[1],
                           b.s ? b.s : "-", fld[3]);
        av_buf_free(&b);
        t->calls++;
        t->same += same;
        t->steps += r.steps + (a->probe_steps - p0);
        t->fires += r.jet_calls;
        (void)jet;
        av_arena_free(a);
    }
    free(text);
}

TEST(the_compiler_term_reproduces_its_own_compilation) {
    av_opts o = av_opts_default();
    o.strategy = AV_COPY;
    o.whnf_only = true;
    o.jets = false;
    o.max_steps = 100000000;
    tally t = { 0 };
    run_calls(&o, false, &t);
    printf("  the term: %llu of %llu abstractions of its own compilation are Python's, "
           "%llu contractions\n", (unsigned long long)t.same, (unsigned long long)t.calls,
           (unsigned long long)t.steps);
    CHECK_EQ(t.calls, 87);
    CHECK_EQ(t.same, t.calls);
}

TEST(the_compiler_jet_agrees_every_fire_checked) {
    av_opts o = av_opts_default();
    o.strategy = AV_COPY;
    o.whnf_only = true;
    o.max_steps = 100000000;
    o.compile_jets = true;
    o.jet_check = 1;
    tally t = { 0 };
    run_calls(&o, true, &t);
    printf("  the jet: %llu of %llu the same, %llu fires, %llu contractions charged\n",
           (unsigned long long)t.same, (unsigned long long)t.calls, (unsigned long long)t.fires,
           (unsigned long long)t.steps);
    CHECK_EQ(t.same, t.calls);
    CHECK_EQ(t.fires, t.calls);
}

/*  The compiler in a pill (§20.1): booted, a kernel whose event `Abs x t`
 *  has the effect `Out ([vx] t)`; poked with every call of its own
 *  compilation, by the term and with the jet. */
TEST(the_compiler_in_a_pill_answers_pokes) {
    for (int jet = 0; jet < 2; jet++) {
        av_arena *a = av_arena_new(1u << 16);
        av_compiler c = compiler(a);
        const char *err = NULL;
        CHECK(av_compiler_register(a, &c, &err));
        av_opts o = av_opts_default();
        o.strategy = AV_COPY;
        o.max_steps = 100000000;
        o.compile_jets = jet;
        o.jet_check = jet;
        av_kernel k;
        bool is_kernel;
        uint32_t value;
        av_result r;
        CHECK_EQ(av_kernel_boot(&k, a, load(a, "pill"), AV_NODE_I, &o, &is_kernel, &value, &r),
                 AV_WHNF);
        CHECK(is_kernel);
        if (!is_kernel) { av_arena_free(a); return; }
        uint32_t absev = load(a, "AbsEvent");
        av_root_push(a, &absev);
        size_t len;
        char *text = (char *)slurp(DIR "own.tsv", &len);
        int n = 0, same = 0;
        for (char *line = text, *nl; text && *line; line = nl) {
            nl = strchr(line, '\n');
            if (nl) *nl++ = '\0';
            char *fld[4];
            int f = 0;
            for (char *p = line; f < 4 && p; f++) {
                fld[f] = p;
                p = strchr(p, '\t');
                if (p) *p++ = '\0';
            }
            av_compiler kc;
            memcpy(&kc, a->compiler, sizeof kc);
            uint32_t body = av_parse(a, fld[1], strlen(fld[1]), NULL);
            uint32_t ev = av_app(a, av_app(a, absev, av_tm_nat(a, &kc, strtoull(fld[0], NULL, 10))),
                                 av_tm_encode(a, &kc, body));
            uint32_t eff;
            CHECK_EQ(av_kernel_poke(&k, ev, &eff, &r), AV_WHNF);
            av_root_push(a, &eff);
            av_opts po = o;
            po.no_collect = true;
            av_peeled outs, out;
            uint32_t got = AV_NONE;
            if (av_peel(a, eff, 2, &po, &outs, NULL) && outs.ctor == 1 &&
                av_peel(a, outs.field[0], 1, &po, &out, NULL) && out.nfields == 1)
                got = av_tm_decode(a, out.field[0], &po, &err);
            char h[27];
            same += got != AV_NONE && av_structural_hash(a, got, h) && strcmp(h, fld[2]) == 0;
            av_root_pop(a);
            n++;
        }
        free(text);
        printf("  the pill%s: %d of %d pokes answered with Python's abstraction\n",
               jet ? ", jetted" : "", same, n);
        CHECK_EQ(n, 87);
        CHECK_EQ(same, n);
        av_root_pop(a);
        av_kernel_free(&k);
        av_arena_free(a);
    }
}

TEST(a_term_that_is_no_compiler_is_refused) {
    av_arena *a = av_arena_new(1u << 16);
    av_compiler c = compiler(a);
    c.abs = av_parse(a, "K K", 3, NULL);          /* abs x t = K: nothing like it */
    const char *err = NULL;
    CHECK(!av_compiler_register(a, &c, &err));
    CHECK(err != NULL);
    CHECK_EQ(a->compiler[0], 0);
    av_arena_free(a);
}

TEST_MAIN(
    TEST_CASE(the_compiler_term_reproduces_its_own_compilation),
    TEST_CASE(the_compiler_jet_agrees_every_fire_checked),
    TEST_CASE(the_compiler_in_a_pill_answers_pokes),
    TEST_CASE(a_term_that_is_no_compiler_is_refused),
)
