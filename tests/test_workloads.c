/**  test_workloads.c
 *
 *  The constructor jets and the jet dictionaries.  Known terms have their
 *  constructor shapes, Joy's word constructors past the old arity cap among
 *  them; and every run of SKIjack's corpus and SKIlark's workloads, with
 *  the constructors found in it and the bird and Joy dictionaries jetted,
 *  every fire checked, gives the manifest's copy-mode count.  Run from the
 *  repository root.
 */

#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "test.h"

static char *slurp(const char *path, size_t *len) {
    FILE *f = test_open(path);
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    char *s = malloc((size_t)n + 1);
    *len = fread(s, 1, (size_t)n, f);
    s[*len] = '\0';
    fclose(f);
    return s;
}

static av_ctor shape(av_arena *a, const char *src) {
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    return av_ctor_of(a, t, 100000);
}

#define SHAPE(a, src, f, i, n) do {                                        \
        av_ctor c_ = shape(a, src);                                        \
        CHECK(c_.fields == (f) && c_.index == (i) && c_.count == (n));     \
        if (c_.fields != (f) || c_.index != (i) || c_.count != (n))        \
            fprintf(stderr, "  %s: %u/%u/%u\n", src, c_.fields, c_.index,  \
                    c_.count);                                             \
    } while (0)

TEST(constructors_have_their_shapes) {
    av_arena *a = av_arena_new(0);
    SHAPE(a, "K", 0, 0, 2);                             /* true  */
    SHAPE(a, "K I", 0, 1, 2);                           /* false */
    SHAPE(a, "S (K (S I)) K", 1, 0, 1);                 /* T     */
    SHAPE(a, "S (S (K S) (S (K K) (S (K S) (S (K (S I)) K)))) (K K)", 2, 0, 1);  /* V */
    SHAPE(a, "S (K K) (S (K (S I)) K)", 1, 1, 2);       /* Suc   */
    SHAPE(a, "S (K S) K", 0, 0, 0);                     /* B: no */
    SHAPE(a, "S I I", 0, 0, 0);                         /* M: no */
    SHAPE(a, "S (K (S I I)) (S (S (K S) K) (K (S I I)))", 0, 0, 0);   /* Y */
    av_arena_free(a);
}

/*  Joy's word constructors: 12 of them, nullary but Lit and Quote. */
/*  Each of FORM's word constructors in jets/joy_names.tsv, its index in
    WORDS and its one field or none: a constructor jet of a COUNT-way sum.
    Returns how many it checked. */
static unsigned check_words(av_arena *a, const char *names_tsv, const char *form,
                            const char *const *words, unsigned nwords, unsigned count,
                            const char *const *one_field, unsigned nfield) {
    size_t n = 0;
    char *names = slurp(names_tsv, &n);
    CHECK(names != NULL);
    if (!names) return 0;
    size_t flen = strlen(form);
    unsigned seen = 0;
    for (char *line = names, *nl; line && *line; line = nl) {
        nl = strchr(line, '\n');
        if (nl) *nl++ = '\0';
        char *t1 = strchr(line, '\t'), *t2 = t1 ? strchr(t1 + 1, '\t') : NULL;
        if (!t2 || (size_t)(t1 - line) != flen || strncmp(line, form, flen) != 0) continue;
        *t2 = '\0';
        for (unsigned w = 0; w < nwords; w++) {
            if (strcmp(t1 + 1, words[w]) != 0) continue;
            av_digest d;
            CHECK(av_hash_parse(t2 + 1, &d));
            uint32_t id = AV_NONE;
            for (uint32_t j = 0; j < a->njets; j++)
                if (av_digest_eq(a->jets[j].digest, d)) id = j;
            CHECK(id != AV_NONE);
            if (id == AV_NONE) continue;
            unsigned fields = 0;
            for (unsigned f = 0; f < nfield; f++)
                if (strcmp(words[w], one_field[f]) == 0) fields = 1;
            CHECK_EQ(a->jets[id].ctor.count, count);
            CHECK_EQ(a->jets[id].ctor.index, w);
            CHECK_EQ(a->jets[id].ctor.fields, fields);
            CHECK_EQ(a->jets[id].arity, count + fields);
            seen++;
        }
    }
    free(names);
    return seen;
}

TEST(joys_words_are_wide_constructors) {
    av_arena *a = av_arena_new(1u << 16);
    const char *err = NULL;
    CHECK_EQ(av_jets_load(a, "jets/joy.tsv", 2, &err), 78);
    static const char *const one[] = { "Lit", "Quote", "Truth" };
    /* phase 1, the basis: a 12-way word */
    static const char *const basis[] = { "Dup", "Swap", "Pop", "Qcons", "Cat", "Unit",
                                         "Dip", "Do", "Ifz", "Lit", "Quote", "Add" };
    CHECK_EQ(check_words(a, "jets/joy_names.tsv", "joy-phase1", basis, 12, 12, one, 3), 12);
    /* the interpreted kernel: Joy's words of a 28-way word, the 28th the
       internal Choose; Lit, Quote and Truth take 29 arguments, under the cap */
    static const char *const kernel[] = { "Dup", "Swap", "Pop", "Qcons", "Cat", "Unit",
                                          "Dip", "Do", "Lit", "Quote", "Add", "Sub", "Mul",
                                          "Div", "Rem", "Succ", "Pred", "Max", "Min", "Eql",
                                          "Lt", "Truth", "And", "Or", "Not", "Branch", "Ifte" };
    CHECK_EQ(check_words(a, "jets/joy_names.tsv", "joy-interpreted", kernel, 27, 28, one, 3), 27);
    av_arena_free(a);
}

typedef struct { uint64_t runs, steps, jet_steps, fires, ctors, wrong; } tally;

static void run_manifest(const char *manifest, tally *t) {
    size_t len;
    char *text = slurp(manifest, &len);
    CHECK(text != NULL);
    if (!text) return;
    const char *slash = strrchr(manifest, '/');
    int dirlen = slash ? (int)(slash - manifest + 1) : 0;
    for (char *line = text, *nl; line && *line; line = nl) {
        nl = strchr(line, '\n');
        if (nl) *nl++ = '\0';
        char *fld[5];
        int k = 0;
        for (char *p = line; k < 5 && p; k++) {
            fld[k] = p;
            p = strchr(p, '\t');
            if (p) *p++ = '\0';
        }
        if (k < 5) continue;
        char path[1024];
        snprintf(path, sizeof path, "%.*s%s", dirlen, manifest, fld[1]);
        size_t blen;
        char *bytes = slurp(path, &blen);
        CHECK(bytes != NULL);
        if (!bytes) continue;
        av_arena *a = av_arena_new(1u << 16);
        CHECK(av_jets_load(a, "jets/birds.tsv", 2, NULL) == 153);
        CHECK(av_jets_load(a, "jets/joy.tsv", 2, NULL) == 78);
        uint32_t term = av_cue(a, (const uint8_t *)bytes, blen, NULL);
        free(bytes);
        CHECK(term != AV_NONE);
        av_root_push(a, &term);
        long found = av_jets_ctors(a, term, 64);
        av_root_pop(a);
        CHECK(found >= 0);
        term = av_jets_match(a, term);
        av_opts o = av_opts_default();
        o.strategy = AV_COPY;
        o.whnf_only = true;
        o.max_steps = strtoull(fld[2], NULL, 10);
        o.jet_check = 1;
        av_result r = av_reduce(a, term, &o);
        CHECK(!r.jet_fault);
        if (r.steps != strtoull(fld[4], NULL, 10) ||
            strcmp(av_status_name(r.status), fld[3]) != 0) {
            fprintf(stderr, "  %s: %s %llu, the manifest says %s %s\n", fld[0],
                    av_status_name(r.status), (unsigned long long)r.steps, fld[3], fld[4]);
            t->wrong++;
        }
        t->runs++;
        t->steps += r.steps;
        t->jet_steps += r.jet_steps;
        t->fires += r.jet_calls;
        t->ctors += (uint64_t)found;
        av_arena_free(a);
    }
    free(text);
}

TEST(every_run_keeps_its_count) {
    static const char *const manifests[] = {
        "tests/conformance/manifest.tsv", "tests/workloads/skilark/manifest.tsv",
    };
    for (int m = 0; m < 2; m++) {
        tally t = { 0 };
        run_manifest(manifests[m], &t);
        CHECK_EQ(t.wrong, 0);
        CHECK(t.fires > 0);
        printf("  %s: %llu runs, %llu contractions, %llu fires absorbing %llu "
               "(%.1f%%), %llu constructors found\n", manifests[m],
               (unsigned long long)t.runs, (unsigned long long)t.steps,
               (unsigned long long)t.fires, (unsigned long long)t.jet_steps,
               t.steps ? 100.0 * (double)t.jet_steps / (double)t.steps : 0.0,
               (unsigned long long)t.ctors);
    }
}

TEST_MAIN(
    TEST_CASE(constructors_have_their_shapes),
    TEST_CASE(joys_words_are_wide_constructors),
    TEST_CASE(every_run_keeps_its_count),
)
