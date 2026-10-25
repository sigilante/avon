/**  test_data.c
 *
 *  Data jets, on skijack's own output: tests/data/ holds four programs and
 *  what tests/data/export.py writes for each, its templates, its numeral
 *  and list operations (words.tsv), and its names main, lazy and out
 *  printed.  main and lazy check themselves and are True, Ff.
 *
 *  - Every mode gives the same answer, and data jets dispatch constructors,
 *    fused into the branch's template, and run numeral operations on words.
 *  - Normal forms are the unjetted ones, byte for byte.
 *  - A word prints, hashes and jams as its numeral, and dispatches in one
 *    step; copy mode runs its term, counts unchanged.
 *  - Every numeral operation agrees with its term on operands 0 .. 7; one
 *    whose operands are not words yet runs its term; a divergent operand is
 *    never forced; a term that is not the operation it claims is refused.
 *  - A list word prints, hashes and jams as its list, and dispatches in one
 *    step; every list operation agrees with its term on lists of 0 .. 3
 *    numerals and indices 0 .. 4; one whose list is not a list word yet
 *    runs its term.
 *  - Collections keep words and list words; fuel stops a run.
 *  - A case joined to its instance is the instance and the dispatch after
 *    it: every count and state the same with joins and without.
 *  - An instance whose root is deferred leaves only nodes unwritten:
 *    every count and state the same with deferral and without, at every
 *    fuel to 400 and in an arena small enough to collect; and a deferred
 *    node keeps nothing alive, so a node cap the undeferred run fits within
 *    by 10% fits the deferred run too.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "avon.h"
#include "test.h"

#define SUC "S (K K) (S (K (S I)) K)"

static char *slurp(const char *path) {
    FILE *f = test_open(path);
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    rewind(f);
    char *s = malloc((size_t)n + 1);
    if (s && fread(s, 1, (size_t)n, f) != (size_t)n) { free(s); s = NULL; }
    if (s) s[n] = '\0';
    fclose(f);
    return s;
}

typedef enum { SKI, TEMPLATES, DATA } mode;

typedef struct {
    av_status status;
    uint64_t  steps, tmpl_calls, dispatches, fused, word_ops, list_ops, collections, joins, deferred;
    long      admitted, refused, words;
    char      nf[1 << 17];
} outcome;

/*  src reduced in share mode (or copy), with dir's templates and, in DATA,
 *  its data jets: the load avon reduce does. */
static bool no_join;    /* run() joins cases to instances unless set */
static bool no_defer;   /* run() defers instances' roots unless set */
static uint32_t max_nodes;  /* run()'s node cap; 0: none */

static outcome run(const char *src, const char *dir, mode md, av_strategy st, bool whnf,
                   uint64_t fuel, uint32_t cap) {
    static outcome out;
    memset(&out, 0, sizeof out);
    av_arena *a = av_arena_new(cap);
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    CHECK(t != AV_NONE);
    if (md != SKI) {
        if (md == DATA) CHECK(av_words_on(a));
        const char *err = NULL;
        av_tmplset *ts = av_templates_load(a, dir, &err);
        CHECK(ts != NULL);
        if (ts) {
            t = av_jets_match(a, t);
            CHECK(av_templates_bind(a, ts, t));
            if (md == DATA) {
                av_templates_word_counts(ts, &out.admitted, &out.refused);
                out.words = av_words_scan(a, t, NULL);
                CHECK(out.words >= 0);
                CHECK(av_words_mark(a));
            }
            av_templates_free(ts);
        }
    }
    av_opts o = av_opts_default();
    o.strategy = st;
    o.whnf_only = whnf;
    o.max_steps = fuel;
    o.templates = md != SKI;
    o.data = md == DATA;
    o.no_join = no_join;
    o.no_defer = no_defer;
    if (max_nodes) o.max_nodes = max_nodes;
    av_root_push(a, &t);
    av_result r = av_reduce(a, t, &o);
    av_root_pop(a);
    out.status = r.status;
    out.steps = r.steps;
    out.tmpl_calls = r.tmpl_calls;
    out.dispatches = r.dispatches;
    out.fused = r.fused;
    out.word_ops = r.word_ops;
    out.list_ops = r.list_ops;
    out.joins = r.joins;
    out.deferred = r.deferred;
    out.collections = a->collections;
    av_buf b = { 0 };
    if (r.term != AV_NONE && av_print(a, r.term, 10000000, &b) && b.len < sizeof out.nf)
        memcpy(out.nf, b.s, b.len + 1);
    av_buf_free(&b);
    av_arena_free(a);
    return out;
}

static char *fixture(const char *prog, const char *name) {
    char path[128];
    snprintf(path, sizeof path, "tests/data/%s/%s.txt", prog, name);
    char *s = slurp(path);
    CHECK(s != NULL);
    if (s) s[strcspn(s, "\n")] = '\0';
    return s;
}

TEST(every_mode_gives_the_same_answer) {
    const char *progs[5][2] = { { "lists", "main" }, { "nats", "main" }, { "nats", "lazy" },
                                { "quot", "main" }, { "listops", "main" } };
    for (int i = 0; i < 5; i++) {
        char dir[64];
        snprintf(dir, sizeof dir, "tests/data/%s", progs[i][0]);
        char *src = fixture(progs[i][0], progs[i][1]);
        if (!src) continue;
        outcome ski = run(src, dir, SKI, AV_SHARE, true, 10000000, 1u << 12);
        CHECK(ski.status == AV_WHNF && strcmp(ski.nf, "Ff") == 0);
        outcome tm = run(src, dir, TEMPLATES, AV_SHARE, true, 10000000, 1u << 12);
        CHECK(tm.status == AV_WHNF && strcmp(tm.nf, "Ff") == 0);
        CHECK_EQ(tm.dispatches, 0);
        outcome dt = run(src, dir, DATA, AV_SHARE, true, 10000000, 1u << 12);
        CHECK(dt.status == AV_WHNF && strcmp(dt.nf, "Ff") == 0);
        CHECK(dt.dispatches > 0);
        if (strcmp(progs[i][1], "main") == 0) {
            CHECK(dt.fused > 0);                    /* case branches, fused */
            CHECK(dt.steps < tm.steps);
            CHECK(dt.tmpl_calls < tm.tmpl_calls);
        }
        if (strcmp(progs[i][0], "nats") == 0 && strcmp(progs[i][1], "main") == 0) {
            CHECK_EQ(dt.admitted, 5);
            CHECK_EQ(dt.refused, 0);
            CHECK(dt.words > 0);
            CHECK(dt.word_ops > 0);
        }
        if (strcmp(progs[i][0], "quot") == 0) {     /* the quotient and remainder too */
            CHECK_EQ(dt.admitted, 7);
            CHECK_EQ(dt.refused, 0);
            CHECK(dt.words > 0);
            CHECK(dt.word_ops > 0);
        }
        if (strcmp(progs[i][0], "listops") == 0) {  /* the five list operations, and ifeq */
            CHECK_EQ(dt.admitted, 6);
            CHECK_EQ(dt.refused, 0);
            CHECK(dt.words > 0);
            CHECK(dt.list_ops > 0);
        }
        free(src);
    }
}

TEST(normal_forms_are_the_unjetted_ones) {
    const char *progs[4] = { "lists", "nats", "quot", "listops" };
    for (int i = 0; i < 4; i++) {
        char dir[64];
        snprintf(dir, sizeof dir, "tests/data/%s", progs[i]);
        char *src = fixture(progs[i], "out");
        if (!src) continue;
        outcome ski = run(src, dir, SKI, AV_SHARE, false, 100000000, 1u << 12);
        static char want[1 << 17];
        strcpy(want, ski.nf);
        CHECK(ski.status == AV_NORMAL && strlen(want) > 0);
        outcome dt = run(src, dir, DATA, AV_SHARE, false, 100000000, 1u << 12);
        CHECK(dt.status == AV_NORMAL);
        CHECK(strcmp(dt.nf, want) == 0);
        CHECK(dt.dispatches > 0);
        free(src);
    }
}

/*  The numeral n, printed as av_print prints it: SUC applied n times to K. */
static void numeral(char *out, size_t cap, unsigned n) {
    size_t at = 0;
    for (unsigned i = 0; i < n; i++)
        at += (size_t)snprintf(out + at, cap - at, i + 1 < n ? SUC " (" : SUC " ");
    at += (size_t)snprintf(out + at, cap - at, "K");
    for (unsigned i = 0; i + 1 < n; i++) at += (size_t)snprintf(out + at, cap - at, ")");
}

TEST(a_word_prints_hashes_and_jams_as_its_numeral) {
    char src[1024];
    numeral(src, sizeof src, 3);
    av_arena *a = av_arena_new(1u << 10);
    uint32_t plain = av_parse(a, src, strlen(src), NULL);
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    CHECK(av_words_on(a));
    CHECK_EQ(av_words_scan(a, t, NULL), 3);
    CHECK(av_is_word(a, t));
    CHECK_EQ(av_word_value(a, t), 3);
    CHECK(!av_is_word(a, plain));
    av_buf b = { 0 };
    CHECK(av_print(a, t, 10000, &b) && strcmp(b.s, src) == 0);
    av_buf_free(&b);
    char h1[AV_HASH_LEN + 1], h2[AV_HASH_LEN + 1];
    CHECK(av_structural_hash(a, t, h1) && av_structural_hash(a, plain, h2));
    CHECK(strcmp(h1, h2) == 0);
    av_buf j1 = { 0 }, j2 = { 0 };
    CHECK(av_jam(a, t, 10000, &j1, NULL) && av_jam(a, plain, 10000, &j2, NULL));
    CHECK(j1.len == j2.len && memcmp(j1.s, j2.s, j1.len) == 0);
    av_buf_free(&j1);
    av_buf_free(&j2);
    CHECK_EQ(av_equal(a, t, plain, 1000), 1);
    av_arena_free(a);
}

TEST(a_word_dispatches_in_one_step_and_copy_mode_runs_its_term) {
    char num[1024], src[1100], want[1100];
    numeral(num, sizeof num, 3);
    snprintf(src, sizeof src, "(%s) z s", num);
    for (int copy = 0; copy < 2; copy++) {
        /* the same run with no words: its state and count, in copy mode */
        av_arena *p = av_arena_new(1u << 10);
        av_opts o = av_opts_default();
        o.strategy = copy ? AV_COPY : AV_SHARE;
        o.whnf_only = true;
        av_result pr = av_reduce(p, av_parse(p, src, strlen(src), NULL), &o);
        av_buf pb = { 0 };
        CHECK(av_print(p, pr.term, 10000, &pb));
        av_arena *a = av_arena_new(1u << 10);
        uint32_t t = av_parse(a, src, strlen(src), NULL);
        uint32_t w = av_left(a, av_left(a, t));
        CHECK(av_words_on(a));
        CHECK_EQ(av_words_scan(a, t, NULL), 3);
        CHECK(av_is_word(a, w));
        o.data = true;
        av_result r = av_reduce(a, t, &o);
        CHECK_EQ(r.status, AV_WHNF);
        av_buf b = { 0 };
        CHECK(av_print(a, r.term, 10000, &b));
        if (copy) {
            CHECK_EQ(r.dispatches, 0);
            CHECK_EQ(r.steps, pr.steps);
            CHECK(strcmp(b.s, pb.s) == 0);
        } else {                    /* W 3 z s is s (W 2): one step */
            char two[1024];
            numeral(two, sizeof two, 2);
            snprintf(want, sizeof want, "s (%s)", two);
            CHECK_EQ(r.dispatches, 1);
            CHECK_EQ(r.steps, 1);
            CHECK(strcmp(b.s, want) == 0);
        }
        av_buf_free(&b);
        av_buf_free(&pb);
        av_arena_free(a);
        av_arena_free(p);
    }
}

/*  The words.tsv line for op in prog's: its term, printed; quot's lists
 *  all seven numeral operations, listops the five list operations. */
static char *prog_op_term(const char *prog, const char *op) {
    char path[128];
    snprintf(path, sizeof path, "tests/data/%s/words.tsv", prog);
    char *text = slurp(path);
    CHECK(text != NULL);
    if (!text) return NULL;
    for (char *line = strtok(text, "\n"); line; line = strtok(NULL, "\n")) {
        char *f1 = strchr(line, '\t'), *f2 = f1 ? strchr(f1 + 1, '\t') : NULL;
        char *f3 = f2 ? strchr(f2 + 1, '\t') : NULL;
        if (!f3) continue;
        *f2 = '\0';
        if (strcmp(f1 + 1, op) == 0) {
            char *t = strdup(f3 + 1);
            free(text);
            return t;
        }
    }
    free(text);
    return NULL;
}

static char *op_term(const char *op) { return prog_op_term("quot", op); }

TEST(every_numeral_operation_agrees_with_its_term) {
    const char *ops[7] = { "add", "sub", "mul", "ifeq", "ifle", "div", "rem" };
    static char src[1 << 16], x[4096], y[4096];
    for (int k = 0; k < 7; k++) {
        char *term = op_term(ops[k]);
        CHECK(term != NULL);
        if (!term) continue;
        bool test = k == 3 || k == 4;
        for (unsigned m = 0; m < 8; m++) {
            for (unsigned n = 0; n < 8; n++) {
                numeral(x, sizeof x, m);
                numeral(y, sizeof y, n);
                snprintf(src, sizeof src, "(%s) (%s) (%s)%s", term, x, y, test ? " yes no" : "");
                outcome ski = run(src, "tests/data/quot", SKI, AV_SHARE, test, 10000000, 1u << 12);
                static char want[1 << 17];
                strcpy(want, ski.nf);
                outcome dt = run(src, "tests/data/quot", DATA, AV_SHARE, test, 10000000, 1u << 12);
                CHECK_EQ(dt.word_ops, 1);
                CHECK(strcmp(dt.nf, want) == 0);
                if (test)
                    CHECK(strcmp(want, (k == 3 ? m == n : m <= n) ? "yes" : "no") == 0);
            }
        }
        free(term);
    }
}

TEST(an_operand_not_yet_a_word_runs_the_term) {
    char *term = op_term("add");
    static char src[1 << 16], x[4096], y[4096];
    if (!term) return;
    numeral(x, sizeof x, 2);
    numeral(y, sizeof y, 3);
    snprintf(src, sizeof src, "(%s) (I (%s)) (%s)", term, x, y);    /* I x: a thunk */
    outcome ski = run(src, "tests/data/nats", SKI, AV_SHARE, false, 10000000, 1u << 12);
    static char want[1 << 17];
    strcpy(want, ski.nf);
    outcome dt = run(src, "tests/data/nats", DATA, AV_SHARE, false, 10000000, 1u << 12);
    CHECK_EQ(dt.word_ops, 0);
    CHECK_EQ(dt.status, AV_NORMAL);
    CHECK(strcmp(dt.nf, want) == 0);
    free(term);
}

TEST(a_divergent_operand_is_never_forced) {
    char *src = fixture("nats", "lazy");
    if (!src) return;
    outcome dt = run(src, "tests/data/nats", DATA, AV_SHARE, true, 10000, 1u << 12);
    CHECK_EQ(dt.status, AV_WHNF);
    CHECK(strcmp(dt.nf, "Ff") == 0);
    free(src);
}

/*  A copy of tests/data/nats with words.tsv rewritten by edit. */
static void nats_copy(char dir[64], void (*edit)(char *text)) {
    strcpy(dir, "/tmp/avon-data-XXXXXX");
    CHECK(mkdtemp(dir) != NULL);
    const char *files[3] = { "templates.tsv", "template_terms.tsv", "words.tsv" };
    for (int i = 0; i < 3; i++) {
        char from[128], to[128];
        snprintf(from, sizeof from, "tests/data/nats/%s", files[i]);
        snprintf(to, sizeof to, "%s/%s", dir, files[i]);
        char *text = slurp(from);
        CHECK(text != NULL);
        if (!text) continue;
        if (i == 2) edit(text);
        FILE *f = fopen(to, "w");
        fputs(text, f);
        fclose(f);
        free(text);
    }
}

static void nats_rm(const char *dir) {
    const char *files[3] = { "templates.tsv", "template_terms.tsv", "words.tsv" };
    for (int i = 0; i < 3; i++) {
        char path[128];
        snprintf(path, sizeof path, "%s/%s", dir, files[i]);
        unlink(path);
    }
    rmdir(dir);
}

static void swap_add_mul(char *text) {         /* add's term labelled mul */
    char *add = strstr(text, "\tadd\t"), *mul = strstr(text, "\tmul\t");
    if (add && mul) { memcpy(add + 1, "mul", 3); memcpy(mul + 1, "add", 3); }
}

static void break_hash(char *text) {           /* the first hash's last digit */
    char *tab = strchr(text, '\t');
    if (tab) tab[-1] = tab[-1] == '0' ? '1' : '0';
}

TEST(a_term_that_is_not_its_operation_is_refused) {
    char dir[64];
    nats_copy(dir, swap_add_mul);
    char *src = fixture("nats", "main");
    if (src) {
        outcome dt = run(src, dir, DATA, AV_SHARE, true, 10000000, 1u << 12);
        CHECK_EQ(dt.admitted, 3);
        CHECK_EQ(dt.refused, 2);
        CHECK(strcmp(dt.nf, "Ff") == 0);            /* their terms run */
        free(src);
    }
    nats_rm(dir);
    nats_copy(dir, break_hash);
    av_arena *a = av_arena_new(1u << 10);
    CHECK(av_words_on(a));
    const char *err = NULL;
    CHECK(av_templates_load(a, dir, &err) == NULL);
    CHECK(err && strstr(err, "hash"));
    av_arena_free(a);
    nats_rm(dir);
}

/*  An addition that agrees with + on 0 .. 6 and not past it, under its own
 *  hash: word_admit's samples pass it, and only the pinned term refuses
 *  it. */
static const char FAKE_ADD[] =
    "skijack-2:69d694910576d08246bde51344e2d59f\tadd\t0\t"
    "S S (K (S (K (S (K (S (K K) (S (K (S I)) K))))) (S (K (S (S S (K"
    " (S (K (S (K (S (K K) (S (K (S I)) K))))) (S (K (S (S S (K (S (K"
    " (S (K (S (K K) (S (K (S I)) K))))) (S (K (S (S S (K (S (K (S (K"
    " (S (K K) (S (K (S I)) K))))) (S (K (S (S S (K (S (K (S (K (S (K"
    " K) (S (K (S I)) K))))) (S (K (S (S S (K (S (K (S (K (S (K K) (S"
    " (K (S I)) K))))) (S (K (S (K I))) K)))))) K)))))) K)))))) K))))"
    ")) K)))))) K)))";

static void no_edit(char *text) { (void)text; }

TEST(only_skijacks_operations_are_admitted) {
    char dir[64];
    nats_copy(dir, no_edit);
    char path[96];
    snprintf(path, sizeof path, "%s/words.tsv", dir);
    char *text = slurp(path);
    REQUIRE(text != NULL);
    FILE *f = fopen(path, "w");
    REQUIRE(f != NULL);
    for (char *line = text, *nl; *line; line = nl ? nl + 1 : line + strlen(line)) {
        nl = strchr(line, '\n');
        if (nl) *nl = '\0';
        if (!strstr(line, "\tadd\t")) fprintf(f, "%s\n", line);
    }
    fprintf(f, "%s\n", FAKE_ADD);
    fclose(f);
    free(text);
    char *src = fixture("nats", "main");
    REQUIRE(src != NULL);
    outcome dt = run(src, dir, DATA, AV_SHARE, true, 10000000, 1u << 12);
    CHECK_EQ(dt.admitted, 4);
    CHECK_EQ(dt.refused, 1);
    CHECK(strcmp(dt.nf, "Ff") == 0);
    free(src);
    nats_rm(dir);
}

TEST(collections_keep_words_and_fuel_stops) {
    char *src = fixture("nats", "main");
    if (!src) return;
    outcome dt = run(src, "tests/data/nats", DATA, AV_SHARE, true, 10000000, 1u << 8);
    CHECK_EQ(dt.status, AV_WHNF);
    CHECK(strcmp(dt.nf, "Ff") == 0);
    CHECK(dt.collections > 0);
    outcome f = run(src, "tests/data/nats", DATA, AV_SHARE, true, 50, 1u << 12);
    CHECK_EQ(f.status, AV_FUEL);
    CHECK_EQ(f.steps, 50);
    free(src);
}

/*  A case joined to its instance is the instance and the dispatch after
 *  it, minus the spine: with joins and without, every count and every
 *  state the same---to normal form, to weak head normal form, at every
 *  fuel from 0 to 400 (a join is made only when both its steps fit), and
 *  through collections. */
static bool same(const outcome *x, const outcome *y) {
    return x->status == y->status && x->steps == y->steps && x->tmpl_calls == y->tmpl_calls &&
           x->dispatches == y->dispatches && x->fused == y->fused &&
           x->word_ops == y->word_ops && x->list_ops == y->list_ops && strcmp(x->nf, y->nf) == 0;
}

TEST(a_joined_case_is_its_instance_and_dispatch) {
    const char *progs[6][2] = { { "lists", "main" }, { "nats", "main" }, { "nats", "lazy" },
                                { "lists", "out" }, { "listops", "main" }, { "listops", "out" } };
    uint64_t collected = 0;
    for (int i = 0; i < 6; i++) {
        char dir[64];
        snprintf(dir, sizeof dir, "tests/data/%s", progs[i][0]);
        char *src = fixture(progs[i][0], progs[i][1]);
        if (!src) continue;
        bool whnf = strcmp(progs[i][1], "out") != 0;
        static outcome off;
        no_join = true;
        off = run(src, dir, DATA, AV_SHARE, whnf, 100000000, 1u << 12);
        no_join = false;
        outcome on = run(src, dir, DATA, AV_SHARE, whnf, 100000000, 1u << 12);
        CHECK(same(&on, &off));
        CHECK_EQ(off.joins, 0);
        CHECK(on.joins > 0);
        on = run(src, dir, DATA, AV_SHARE, whnf, 100000000, 1u << 8);    /* collecting */
        CHECK(same(&on, &off));
        collected += on.collections;
        for (uint64_t fuel = 0; fuel <= 400; fuel++) {
            no_join = true;
            off = run(src, dir, DATA, AV_SHARE, whnf, fuel, 1u << 12);
            no_join = false;
            on = run(src, dir, DATA, AV_SHARE, whnf, fuel, 1u << 12);
            CHECK(same(&on, &off));
            if (!same(&on, &off))
                fprintf(stderr, "  %s/%s at fuel %llu\n", progs[i][0], progs[i][1],
                        (unsigned long long)fuel);
        }
        free(src);
    }
    CHECK(collected > 0);       /* the small arena collected, in some run */
}

/*  Deferral off and on, in mode md, for every fixture: the same outcome,
 *  joins too, with deferral at work; again in a small arena, collecting;
 *  and at every fuel to 400, where the state reported is the stopped one. */
static void deferral_changes_nothing(mode md) {
    const char *progs[6][2] = { { "lists", "main" }, { "nats", "main" }, { "nats", "lazy" },
                                { "lists", "out" }, { "listops", "main" }, { "listops", "out" } };
    uint64_t collected = 0, deferred = 0;
    for (int i = 0; i < 6; i++) {
        char dir[64];
        snprintf(dir, sizeof dir, "tests/data/%s", progs[i][0]);
        char *src = fixture(progs[i][0], progs[i][1]);
        if (!src) continue;
        bool whnf = strcmp(progs[i][1], "out") != 0;
        static outcome off;
        no_defer = true;
        off = run(src, dir, md, AV_SHARE, whnf, 100000000, 1u << 12);
        no_defer = false;
        outcome on = run(src, dir, md, AV_SHARE, whnf, 100000000, 1u << 12);
        CHECK(same(&on, &off));
        CHECK_EQ(on.joins, off.joins);
        CHECK_EQ(off.deferred, 0);
        deferred += on.deferred;
        on = run(src, dir, md, AV_SHARE, whnf, 100000000, 1u << 8);    /* collecting */
        CHECK(same(&on, &off));
        CHECK_EQ(on.joins, off.joins);
        collected += on.collections;
        for (uint64_t fuel = 0; fuel <= 400; fuel++) {
            no_defer = true;
            off = run(src, dir, md, AV_SHARE, whnf, fuel, 1u << 12);
            no_defer = false;
            on = run(src, dir, md, AV_SHARE, whnf, fuel, 1u << 12);
            CHECK(same(&on, &off));
            CHECK_EQ(on.joins, off.joins);
            if (!same(&on, &off) || on.joins != off.joins)
                fprintf(stderr, "  %s/%s at fuel %llu\n", progs[i][0], progs[i][1],
                        (unsigned long long)fuel);
            on = run(src, dir, md, AV_SHARE, whnf, fuel, 1u << 8);
            CHECK(same(&on, &off));
        }
        free(src);
    }
    CHECK(deferred > 0);        /* deferral was at work */
    CHECK(collected > 0);       /* the small arena collected, in some run */
}

TEST(a_deferred_root_changes_no_count_or_state_with_templates) { deferral_changes_nothing(TEMPLATES); }
TEST(a_deferred_root_changes_no_count_or_state_with_data_jets) { deferral_changes_nothing(DATA); }

/*  A deferred root's node holds no stale redex: nats/main's normal form,
 *  which the undeferred run reaches within 1,225 live nodes, is reached by
 *  both runs under a cap of 1,350.  A deferred node that kept its redex
 *  needed 1,470. */
TEST(a_deferred_node_keeps_nothing_alive) {
    char *src = fixture("nats", "main");
    if (!src) return;
    static outcome off;
    max_nodes = 1350;
    no_defer = true;
    off = run(src, "tests/data/nats", DATA, AV_SHARE, false, 100000000, 1u << 8);
    no_defer = false;
    outcome on = run(src, "tests/data/nats", DATA, AV_SHARE, false, 100000000, 1u << 8);
    max_nodes = 0;
    CHECK_EQ(off.status, AV_NORMAL);
    CHECK(same(&on, &off));
    CHECK(on.deferred > 0);
    free(src);
}

/*  The list of the numerals xs[0 .. n-1], printed as av_print prints it:
 *  CONS x applied to the rest, K the empty list. */
#define CONS "S (K (S (K K))) (S (S (K S) (S (K K) (S (K S) (S (K (S I)) K)))) (K K))"
static void plain_list(char *out, size_t cap, const unsigned *xs, unsigned n) {
    size_t at = 0;
    for (unsigned i = 0; i < n; i++) {
        char x[512];
        numeral(x, sizeof x, xs[i]);
        at += (size_t)snprintf(out + at, cap - at, xs[i] ? CONS " (%s) " : CONS " %s ", x);
        if (i + 1 < n) at += (size_t)snprintf(out + at, cap - at, "(");
    }
    at += (size_t)snprintf(out + at, cap - at, "K");
    for (unsigned i = 0; i + 1 < n; i++) at += (size_t)snprintf(out + at, cap - at, ")");
}

TEST(a_list_word_prints_hashes_and_jams_as_its_list) {
    static const unsigned xs[3] = { 2, 0, 1 };
    char src[4096];
    plain_list(src, sizeof src, xs, 3);
    av_arena *a = av_arena_new(1u << 10);
    uint32_t plain = av_parse(a, src, strlen(src), NULL);
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    CHECK(av_words_on(a));
    long lists = -1;
    CHECK_EQ(av_words_scan(a, t, &lists), 6);       /* three cells, and numerals 2 and 1 */
    CHECK_EQ(lists, 3);
    uint32_t n = 0;
    CHECK(av_is_list(a, t) && !av_is_word(a, t));
    CHECK(av_list(a, t, &n) && n == 3);
    CHECK(!av_is_list(a, plain));
    av_buf b = { 0 };
    CHECK(av_print(a, t, 10000, &b) && strcmp(b.s, src) == 0);
    av_buf_free(&b);
    char h1[AV_HASH_LEN + 1], h2[AV_HASH_LEN + 1];
    CHECK(av_structural_hash(a, t, h1) && av_structural_hash(a, plain, h2));
    CHECK(strcmp(h1, h2) == 0);
    av_buf j1 = { 0 }, j2 = { 0 };
    CHECK(av_jam(a, t, 10000, &j1, NULL) && av_jam(a, plain, 10000, &j2, NULL));
    CHECK(j1.len == j2.len && memcmp(j1.s, j2.s, j1.len) == 0);
    av_buf_free(&j1);
    av_buf_free(&j2);
    CHECK_EQ(av_equal(a, t, plain, 1000), 1);
    av_arena_free(a);
}

TEST(a_collection_keeps_list_words) {
    static const unsigned xs[3] = { 2, 0, 1 };
    char src[4096];
    plain_list(src, sizeof src, xs, 3);
    av_arena *a = av_arena_new(1u << 10);
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    CHECK(av_words_on(a));
    CHECK_EQ(av_words_scan(a, t, NULL), 6);
    av_root_push(a, &t);
    CHECK(av_collect(a, 0, NULL, NULL, NULL));
    av_root_pop(a);
    CHECK(a->collections > 0);
    uint32_t n = 0, m = 0;
    CHECK(av_list(a, t, &n) && n == 3);
    CHECK(av_list(a, av_right(a, av_right(a, t)), &m) && m == 2);   /* its rest */
    av_buf b = { 0 };
    CHECK(av_print(a, t, 10000, &b) && strcmp(b.s, src) == 0);
    av_buf_free(&b);
    av_arena_free(a);
}

TEST(a_list_word_dispatches_in_one_step_and_copy_mode_runs_its_term) {
    static const unsigned xs[2] = { 0, 0 };
    char lst[2048], src[2100];
    plain_list(lst, sizeof lst, xs, 2);
    snprintf(src, sizeof src, "(%s) n c", lst);
    for (int copy = 0; copy < 2; copy++) {
        av_arena *p = av_arena_new(1u << 10);
        av_opts o = av_opts_default();
        o.strategy = copy ? AV_COPY : AV_SHARE;
        o.whnf_only = true;
        av_result pr = av_reduce(p, av_parse(p, src, strlen(src), NULL), &o);
        av_buf pb = { 0 };
        CHECK(av_print(p, pr.term, 10000, &pb));
        av_arena *a = av_arena_new(1u << 10);
        uint32_t t = av_parse(a, src, strlen(src), NULL);
        CHECK(av_words_on(a));
        long lists = 0;
        CHECK_EQ(av_words_scan(a, t, &lists), 2);
        CHECK_EQ(lists, 2);
        CHECK(av_is_list(a, av_left(a, av_left(a, t))));
        o.data = true;
        av_result r = av_reduce(a, t, &o);
        CHECK_EQ(r.status, AV_WHNF);
        av_buf b = { 0 };
        CHECK(av_print(a, r.term, 10000, &b));
        if (copy) {
            CHECK_EQ(r.dispatches, 0);
            CHECK_EQ(r.steps, pr.steps);
            CHECK(strcmp(b.s, pb.s) == 0);
        } else {                    /* L 2 n c is c K (L 1): one step */
            static const unsigned one[1] = { 0 };
            char rest[1024], want[1100];
            plain_list(rest, sizeof rest, one, 1);
            snprintf(want, sizeof want, "c K (%s)", rest);
            CHECK_EQ(r.dispatches, 1);
            CHECK_EQ(r.steps, 1);
            CHECK(strcmp(b.s, want) == 0);
        }
        av_buf_free(&b);
        av_buf_free(&pb);
        av_arena_free(a);
        av_arena_free(p);
    }
}

TEST(every_list_operation_agrees_with_its_term) {
    static const unsigned lists[4][3] = { { 0 }, { 3 }, { 1, 0 }, { 2, 4, 0 } };
    static const unsigned lens[4] = { 0, 1, 2, 3 };
    const char *ops[5] = { "len", "at", "app", "take", "drop" };
    static char src[1 << 16], l[4096], r2[4096], k[512], d[512];
    for (int o = 0; o < 5; o++) {
        char *term = prog_op_term("listops", ops[o]);
        CHECK(term != NULL);
        if (!term) continue;
        for (unsigned i = 0; i < 4; i++) {
            plain_list(l, sizeof l, lists[i], lens[i]);
            unsigned js = o == 0 ? 1 : o == 2 ? 4 : 5;
            for (unsigned j = 0; j < js; j++) {
                numeral(k, sizeof k, j);
                numeral(d, sizeof d, 6);
                if (o == 0) snprintf(src, sizeof src, "(%s) (%s)", term, l);
                else if (o == 1) snprintf(src, sizeof src, "(%s) (%s) (%s) (%s)", term, l, k, d);
                else if (o == 2) {
                    plain_list(r2, sizeof r2, lists[j], lens[j]);
                    snprintf(src, sizeof src, "(%s) (%s) (%s)", term, l, r2);
                } else snprintf(src, sizeof src, "(%s) (%s) (%s)", term, l, k);
                outcome ski = run(src, "tests/data/listops", SKI, AV_SHARE, false, 10000000, 1u << 12);
                static char want[1 << 17];
                strcpy(want, ski.nf);
                CHECK_EQ(ski.status, AV_NORMAL);
                outcome dt = run(src, "tests/data/listops", DATA, AV_SHARE, false, 10000000, 1u << 12);
                CHECK_EQ(dt.status, AV_NORMAL);
                CHECK_EQ(dt.list_ops, 1);
                CHECK(strcmp(dt.nf, want) == 0);
                if (strcmp(dt.nf, want) != 0) fprintf(stderr, "  %s on list %u, %u\n", ops[o], i, j);
            }
        }
        free(term);
    }
}

TEST(a_list_operand_not_yet_a_list_word_runs_the_term) {
    char *term = prog_op_term("listops", "len");
    static char src[1 << 16], l[4096];
    static const unsigned xs[2] = { 1, 2 };
    if (!term) return;
    plain_list(l, sizeof l, xs, 2);
    snprintf(src, sizeof src, "(%s) (I (%s))", term, l);            /* I l: a thunk */
    outcome ski = run(src, "tests/data/listops", SKI, AV_SHARE, false, 10000000, 1u << 12);
    static char want[1 << 17];
    strcpy(want, ski.nf);
    outcome dt = run(src, "tests/data/listops", DATA, AV_SHARE, false, 10000000, 1u << 12);
    CHECK_EQ(dt.list_ops, 0);
    CHECK_EQ(dt.status, AV_NORMAL);
    CHECK(strcmp(dt.nf, want) == 0);
    free(term);
}

TEST_MAIN(
    TEST_CASE(every_mode_gives_the_same_answer),
    TEST_CASE(a_joined_case_is_its_instance_and_dispatch),
    TEST_CASE(a_deferred_root_changes_no_count_or_state_with_templates),
    TEST_CASE(a_deferred_root_changes_no_count_or_state_with_data_jets),
    TEST_CASE(a_deferred_node_keeps_nothing_alive),
    TEST_CASE(normal_forms_are_the_unjetted_ones),
    TEST_CASE(a_word_prints_hashes_and_jams_as_its_numeral),
    TEST_CASE(a_word_dispatches_in_one_step_and_copy_mode_runs_its_term),
    TEST_CASE(every_numeral_operation_agrees_with_its_term),
    TEST_CASE(an_operand_not_yet_a_word_runs_the_term),
    TEST_CASE(a_divergent_operand_is_never_forced),
    TEST_CASE(a_term_that_is_not_its_operation_is_refused),
    TEST_CASE(only_skijacks_operations_are_admitted),
    TEST_CASE(collections_keep_words_and_fuel_stops),
    TEST_CASE(a_list_word_prints_hashes_and_jams_as_its_list),
    TEST_CASE(a_collection_keeps_list_words),
    TEST_CASE(a_list_word_dispatches_in_one_step_and_copy_mode_runs_its_term),
    TEST_CASE(every_list_operation_agrees_with_its_term),
    TEST_CASE(a_list_operand_not_yet_a_list_word_runs_the_term)
)
