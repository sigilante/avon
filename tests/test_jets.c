/**  test_jets.c
 *
 *  Hash and residual jets' acceptance: the structural hash matches
 *  skijack's strings on every dictionary row; the loader finds the rows
 *  skijack's hash_all finds; and residual jets leave every copy-mode count,
 *  every stopped state and every value as it was without them---on every
 *  registered jet over random arguments and fuel, and with --jet-check on
 *  every fire, which catches a corrupted jet.  tests/test_conformance.c
 *  runs the corpus with jets on.  Run from the repository root.
 */

#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "../src/jets.h"
#include "test.h"

#define DICT "tests/conformance/dictionary.tsv"
#define NAMES "tests/conformance/dictionary_names.tsv"

static char *hash_of(av_arena *a, const char *src) {
    static char h[27];
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    return t != AV_NONE && av_structural_hash(a, t, h) ? h : NULL;
}

TEST(the_hash_is_skijacks) {
    /* python/skijack/dictionary.py's structural_hash, 5dfc75 */
    static const char *const want[][2] = {
        { "S", "skijack-1:8de0b3c47f112c59" },
        { "K", "skijack-1:86be9a55762d316a" },
        { "I", "skijack-1:a83dd0ccbffe39d0" },
        { "S K", "skijack-1:cd1e0f4e27bd7f92" },
        { "S K K", "skijack-1:2e490652d25a0ff9" },
        { "S (K I)", "skijack-1:47b7611dc637f626" },
        { "X1", "skijack-1:ad667b78ba8ed027" },
    };
    av_arena *a = av_arena_new(0);
    for (size_t i = 0; i < sizeof want / sizeof want[0]; i++) {
        char *h = hash_of(a, want[i][0]);
        CHECK(h && strcmp(h, want[i][1]) == 0);
    }
    uint64_t d;
    CHECK(av_hash_parse("skijack-1:8de0b3c47f112c59", &d) && d == 0x8de0b3c47f112c59u);
    CHECK(!av_hash_parse("skijack-2:8de0b3c47f112c59", &d));
    CHECK(!av_hash_parse("skijack-1:8de0b3c47f112c5", &d));
    av_arena_free(a);
}

/*  ------------------------------------------------ the dictionary export */

typedef struct { char *text; char **hash; size_t *atoms; char **term; size_t n; } dict;

static dict load_dict(void) {
    dict d = { 0 };
    FILE *f = test_open(DICT);
    fseek(f, 0, SEEK_END);
    size_t len = (size_t)ftell(f);
    fseek(f, 0, SEEK_SET);
    d.text = malloc(len + 1);
    len = fread(d.text, 1, len, f);
    d.text[len] = '\0';
    fclose(f);
    for (size_t i = 0; i < len; i++) d.n += d.text[i] == '\n';
    d.hash = malloc(d.n * sizeof *d.hash);
    d.atoms = malloc(d.n * sizeof *d.atoms);
    d.term = malloc(d.n * sizeof *d.term);
    char *p = d.text;
    for (size_t k = 0; k < d.n; k++) {
        char *nl = strchr(p, '\n'), *t1 = strchr(p, '\t'), *t2 = strchr(t1 + 1, '\t');
        *nl = *t1 = *t2 = '\0';
        d.hash[k] = p;
        d.atoms[k] = strtoull(t1 + 1, NULL, 10);
        d.term[k] = t2 + 1;
        p = nl + 1;
    }
    return d;
}

static void free_dict(dict *d) {
    free(d->text); free(d->hash); free(d->atoms); free(d->term);
}

static size_t leaves(const av_arena *a, uint32_t t) {
    t = av_view(a, t);
    return av_tag(a, t) == AV_LEAF ? 1 : leaves(a, av_left(a, t)) + leaves(a, av_right(a, t));
}

TEST(every_dictionary_hash_matches) {
    dict d = load_dict();
    CHECK_EQ(d.n, 282);
    av_arena *a = av_arena_new(0);
    for (size_t k = 0; k < d.n; k++) {
        uint32_t t = av_parse(a, d.term[k], strlen(d.term[k]), NULL);
        char h[27];
        CHECK(t != AV_NONE && av_structural_hash(a, t, h));
        if (strcmp(h, d.hash[k]) != 0) {
            fprintf(stderr, "  row %zu: %s, want %s\n", k, h, d.hash[k]);
            CHECK(0);
        }
        CHECK_EQ(leaves(a, t), d.atoms[k]);
    }
    av_arena_free(a);
    free_dict(&d);
}

/*  The rows the loader finds inside a term, counted by distinct
 *  hash---skijack's hash_all over the same term gives these. */
static const char *term_named(const dict *d, const char *program, const char *name) {
    FILE *f = test_open(NAMES);
    char line[512], *hash = NULL;
    static char found[32];
    while (fgets(line, sizeof line, f)) {
        char *t1 = strchr(line, '\t'), *t2 = t1 ? strchr(t1 + 1, '\t') : NULL;
        if (!t2) continue;
        *t1 = *t2 = '\0';
        t2[1 + strcspn(t2 + 1, "\n")] = '\0';
        if (strcmp(line, program) == 0 && strcmp(t1 + 1, name) == 0) {
            snprintf(found, sizeof found, "%s", t2 + 1);
            hash = found;
        }
    }
    fclose(f);
    for (size_t k = 0; hash && k < d->n; k++)
        if (strcmp(d->hash[k], hash) == 0) return d->term[k];
    return NULL;
}

static void coverage(const dict *d, const char *program, const char *name,
                     size_t want_distinct, size_t want_rows, size_t want_big) {
    const char *src = term_named(d, program, name);
    CHECK(src != NULL);
    if (!src) return;
    av_arena *a = av_arena_new(0);
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    /* every subterm's hash, deduplicated */
    size_t cap = 1024, n = 0, top = 0;
    char (*seen)[27] = malloc(cap * sizeof *seen);
    uint32_t *stk = malloc(4096 * sizeof *stk);
    stk[top++] = t;
    while (top) {
        uint32_t x = stk[--top];
        char h[27];
        av_structural_hash(a, x, h);
        size_t i = 0;
        while (i < n && strcmp(seen[i], h) != 0) i++;
        if (i == n) {
            if (n == cap) seen = realloc(seen, (cap *= 2) * sizeof *seen);
            memcpy(seen[n++], h, 27);
        }
        if (av_tag(a, x) == AV_APP) { stk[top++] = av_left(a, x); stk[top++] = av_right(a, x); }
    }
    size_t rows = 0, big = 0;
    for (size_t i = 0; i < n; i++)
        for (size_t k = 0; k < d->n; k++)
            if (strcmp(seen[i], d->hash[k]) == 0) { rows++; big += d->atoms[k] >= 3; }
    CHECK_EQ(n, want_distinct);
    CHECK_EQ(rows, want_rows);
    CHECK_EQ(big, want_big);
    free(seen);
    free(stk);
    av_arena_free(a);
}

TEST(the_loader_finds_what_hash_all_finds) {
    dict d = load_dict();
    /* measured with skijack.dictionary.hash_all over the same export */
    coverage(&d, "interp-whnff", "whnfF", 147, 28, 26);
    coverage(&d, "scry-wfn", "wfN", 224, 38, 36);
    coverage(&d, "tower", "UQ", 33, 6, 3);
    coverage(&d, "interp-t3", "wf5Abs", 177, 36, 33);
    free_dict(&d);
}

/*  --------------------------------------------------------- residual jets */

TEST(registration_follows_the_rules) {
    av_arena *a = av_arena_new(0);
    const char *why = NULL;
    /* below the floor */
    uint32_t k = av_parse(a, "K", 1, NULL);
    CHECK(av_jet_register(a, k, 2, 1000, &why) == AV_NONE && why && strstr(why, "floor"));
    /* pair a b c = c a b: arity 3, the third argument at the head */
    const char *pair = "S (S (K S) (S (K K) (S (K S) (S (K (S I)) K)))) (K K)";
    uint32_t p = av_parse(a, pair, strlen(pair), NULL);
    av_root_push(a, &p);                            /* registration collects */
    uint32_t id = av_jet_register(a, p, 3, 1000, &why);
    CHECK(id != AV_NONE);
    if (id != AV_NONE) {
        CHECK_EQ(a->jets[id].arity, 3);
        CHECK(a->jets[id].ctor.fields == 2 && a->jets[id].ctor.index == 0 &&
              a->jets[id].ctor.count == 1);         /* V: a constructor */
        /* the state when an atom first reaches the head: normal order has
         * not reduced the arguments, which are c's a and b unevaluated */
        av_buf b = { 0 };
        CHECK(av_print(a, a->jets[id].residual, 100, &b));
        CHECK(b.s && strcmp(b.s, "@x2 (K @x0 @x2) (K K @x0 @x1 @x2)") == 0);
        CHECK_EQ(a->jets[id].cost, 14);
        av_buf_free(&b);
        CHECK_EQ(av_jet_register(a, p, 3, 1000, NULL), id);   /* once */
    }
    av_root_pop(a);
    /* 33 nested K discard 32 arguments: no arity up to AV_JET_ARITY_MAX
     * exposes one (K K alone does: K K a b c is b) */
    uint32_t kk = AV_NODE_K;
    for (unsigned i = 0; i < AV_JET_ARITY_MAX + 1; i++) kk = av_app(a, AV_NODE_K, kk);
    CHECK(av_jet_register(a, kk, 2, 1000, &why) == AV_NONE && strstr(why, "arity"));
    uint32_t k2 = av_parse(a, "K K", 3, NULL);
    uint32_t id2 = av_jet_register(a, k2, 2, 1000, NULL);
    CHECK(id2 != AV_NONE && a->jets[id2].arity == 3);
    /* a divergent term never halts */
    uint32_t om = av_parse(a, "S I I (S I I)", 13, NULL);
    CHECK(av_jet_register(a, om, 2, 1000, &why) == AV_NONE && strstr(why, "halt"));
    av_arena_free(a);
}

TEST(the_dictionary_registers) {
    av_arena *a = av_arena_new(0);
    const char *err = NULL;
    CHECK_EQ(av_jets_load(a, DICT, 8, &err), 135);
    for (uint32_t i = 0; i < a->njets; i++) {
        CHECK(a->jets[i].arity >= 1 && a->jets[i].arity <= 8);
        CHECK(a->jets[i].cost > 0);
        CHECK(a->jets[i].atoms >= 8);
    }
    av_arena_free(a);
}

static uint64_t rng = 0x243f6a8885a308d3u;
static uint32_t next(void) {
    rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
    return (uint32_t)(rng >> 32);
}

static uint32_t gen(av_arena *a, int depth) {
    if (depth == 0 || next() % 10 < 4) {
        static const char *leaf[] = { "S", "K", "I", "X", "Z" };
        const char *nm = leaf[next() % 5];
        return av_leaf(a, nm, strlen(nm));
    }
    uint32_t f = gen(a, depth - 1);
    return av_app(a, f, gen(a, depth - 1));
}

typedef struct { av_status s; uint64_t steps, calls; bool fault; char *text; } run_out;

static run_out run(av_arena *a, uint32_t t, av_strategy st, bool whnf,
                   uint64_t fuel, bool jets) {
    av_opts o = av_opts_default();
    o.strategy = st;
    o.whnf_only = whnf;
    o.max_steps = fuel;
    o.jets = jets;
    o.jet_check = jets ? 1 : 0;
    av_result r = av_reduce(a, t, &o);
    av_buf b = { 0 };
    run_out out = { r.status, r.steps, r.jet_calls, r.jet_fault, NULL };
    if (r.term != AV_NONE && av_print(a, r.term, 200000, &b)) out.text = b.s;
    else av_buf_free(&b);
    return out;
}

/*  Every jet over random arguments, one to three extra, at random fuel:
 *  copy mode stops at the same state after the same count jets on and
 *  off, and share mode reaches the same normal form. */
TEST(every_jet_leaves_counts_and_states_alone) {
    av_arena *a = av_arena_new(1u << 16);
    CHECK(av_jets_load(a, DICT, 8, NULL) == 135);
    int rounds = getenv("AVON_FUZZ") ? atoi(getenv("AVON_FUZZ")) : 20;
    uint64_t fired = 0, compared = 0;
    for (int round = 0; round < rounds; round++) {
        for (uint32_t id = 0; id < a->njets; id++) {
            uint32_t t = a->jets[id].fallback;
            unsigned extra = next() % 3;
            for (unsigned i = 0; i < a->jets[id].arity + extra; i++)
                t = av_app(a, t, gen(a, 3));
            t = av_jets_match(a, t);
            av_root_push(a, &t);
            uint64_t fuel = next() % 2 ? 1 + next() % (2 * a->jets[id].cost + 4)
                                       : 20000;
            bool whnf = next() % 2;
            run_out on = run(a, t, AV_COPY, whnf, fuel, true);
            run_out off = run(a, t, AV_COPY, whnf, fuel, false);
            CHECK(!on.fault);
            CHECK_EQ(on.s, off.s);
            CHECK_EQ(on.steps, off.steps);
            if (on.text && off.text) {
                if (strcmp(on.text, off.text) != 0) {
                    fprintf(stderr, "  jet %u: jets on %.60s, off %.60s\n", id, on.text, off.text);
                    CHECK(0);
                }
                compared++;
            }
            fired += on.calls;
            if (off.s == AV_NORMAL) {
                run_out sh = run(a, t, AV_SHARE, false, 1000000, true);
                CHECK(!sh.fault);
                CHECK(sh.s == AV_NORMAL && sh.text && off.text && strcmp(sh.text, off.text) == 0);
                free(sh.text);
            }
            free(on.text);
            free(off.text);
            av_root_pop(a);
        }
    }
    CHECK(compared > a->njets * (unsigned)rounds / 2);
    CHECK(fired > 0);
    av_arena_free(a);
}

TEST(the_check_catches_a_corrupted_jet) {
    av_arena *a = av_arena_new(0);
    const char *pair = "S (S (K S) (S (K K) (S (K S) (S (K (S I)) K)))) (K K)";
    uint32_t p = av_parse(a, pair, strlen(pair), NULL);
    av_root_push(a, &p);                            /* registration collects */
    uint32_t id = av_jet_register(a, p, 3, 1000, NULL);
    av_root_pop(a);
    CHECK(id != AV_NONE);
    uint32_t t = av_parse(a, "X Z A", 5, NULL);     /* arguments, as atoms */
    uint32_t prog = av_app(a, av_app(a, av_app(a, p, av_left(a, av_left(a, t))),
                                     av_right(a, av_left(a, t))), av_right(a, t));
    prog = av_jets_match(a, prog);
    av_root_push(a, &prog);                         /* the runs collect */
    run_out good = run(a, prog, AV_COPY, true, 1000, true);
    CHECK(!good.fault && good.calls == 1 && good.steps == 14 && good.text &&
          strcmp(good.text, "A (K X A) (K K X Z A)") == 0);
    free(good.text);
    run_out nf = run(a, prog, AV_COPY, false, 1000, true);
    CHECK(!nf.fault && nf.s == AV_NORMAL && nf.text && strcmp(nf.text, "A X Z") == 0);
    free(nf.text);
    a->jets[id].cost++;                              /* now it overcharges */
    run_out bad = run(a, prog, AV_COPY, true, 1000, true);
    CHECK(bad.fault && bad.s == AV_INTERRUPTED);
    free(bad.text);
    av_root_pop(a);
    av_arena_free(a);
}

static size_t jet_nodes(const av_arena *a, uint32_t t, size_t depth) {
    if (depth > 64) return 0;
    t = av_res(a, t);
    if (av_tag(a, t) == AV_JET) return 1 + jet_nodes(a, av_right(a, t), depth + 1);
    if (av_tag(a, t) != AV_APP) return 0;
    return jet_nodes(a, av_left(a, t), depth + 1) + jet_nodes(a, av_right(a, t), depth + 1);
}

/*  A node is a jet's only if it is the jet's term: the 64-bit digest
 *  finds a candidate, and the trees must match.  Here the jet's term is
 *  changed after registration, as a colliding term under the same digest
 *  would be. */
TEST(a_digest_match_is_not_enough) {
    av_arena *a = av_arena_new(0);
    const char *pair = "S (S (K S) (S (K K) (S (K S) (S (K (S I)) K)))) (K K)";
    uint32_t p = av_parse(a, pair, strlen(pair), NULL);
    av_root_push(a, &p);
    uint32_t id = av_jet_register(a, p, 3, 1000, NULL);
    REQUIRE(id != AV_NONE);
    uint32_t x = av_parse(a, "X", 1, NULL);
    uint32_t prog = av_app(a, p, x);
    av_root_push(a, &prog);
    uint32_t m = av_jets_match(a, prog);
    CHECK_EQ(jet_nodes(a, m, 0), 1);                /* the term: wrapped */
    a->jets[id].fallback = av_parse(a, "K K", 3, NULL);
    m = av_jets_match(a, prog);
    CHECK_EQ(jet_nodes(a, m, 0), 0);                /* the digest alone: not */
    av_root_pop(a);
    av_root_pop(a);
    av_arena_free(a);
}

/*  A digest is 64 bits, so two terms may share one.  An entry, or a
 *  registration, offered a term under a digest whose jet holds another
 *  term is refused as a collision: it is never merged into that jet, so a
 *  template or an interpreter cannot inherit another term's behaviour.  No
 *  collision is searched for: the colliding digest is passed in, as the
 *  template loader passes its key, or the jet's term is replaced. */
TEST(a_collision_is_refused_not_merged) {
    av_arena *a = av_arena_new(0);
    const char *suc = "S (K K) (S (K (S I)) K)";
    uint32_t x = av_parse(a, suc, strlen(suc), NULL);
    uint32_t t = av_parse(a, "K I", 3, NULL);
    av_root_push(a, &x);
    av_root_push(a, &t);
    char h[27];
    uint64_t dx;
    REQUIRE(av_structural_hash(a, x, h) && av_hash_parse(h, &dx));
    const char *why = NULL;
    uint32_t id = jet_entry_for(a, dx, x, &why);
    REQUIRE(id != AV_NONE);
    CHECK_EQ(jet_entry_for(a, dx, x, &why), id);            /* its own term: its entry */
    uint32_t x2 = av_parse(a, suc, strlen(suc), NULL);
    CHECK_EQ(jet_entry_for(a, dx, x2, &why), id);           /* a copy of it: the same */
    CHECK_EQ(jet_entry_for(a, dx, t, &why), AV_NONE);       /* another term: refused */
    CHECK(why == jet_collision);
    CHECK_EQ(a->njets, 1);
    /* registration: the entry's term replaced, x is now the other term */
    a->jets[id].fallback = t;
    why = NULL;
    CHECK_EQ(av_jet_register(a, x, 1, 1000, &why), AV_NONE);
    CHECK(why == jet_collision);
    av_root_pop(a);
    av_root_pop(a);
    av_arena_free(a);
}

/*  A program's copy of a jet's term may share less than the term: here the
 *  term holds a constant of 15 distinct nodes whose tree has 2^14 leaves,
 *  and the program holds the tree.  The match is by identity of trees,
 *  not a comparison with a budget on the jet's size, which refused it
 *  (92 templates of front1's own source). */
TEST(a_jet_matches_a_copy_that_shares_less) {
    av_arena *a = av_arena_new(0);
    uint32_t c = AV_NODE_S;
    for (int i = 0; i < 14; i++) c = av_app(a, c, c);    /* shared: 15 nodes */
    /* J = S (K (K K)) (K C): J x y z is y, its constant discarded */
    uint32_t kk = av_app(a, AV_NODE_K, AV_NODE_K);
    uint32_t j = av_app(a, av_app(a, AV_NODE_S, av_app(a, AV_NODE_K, kk)), av_app(a, AV_NODE_K, c));
    av_root_push(a, &j);
    const char *why = NULL;
    uint32_t id = av_jet_register(a, j, 2, 100000, &why);
    REQUIRE(id != AV_NONE);
    av_buf b = { 0 };
    REQUIRE(av_print(a, j, 1u << 24, &b));
    uint32_t tree = av_parse(a, b.s, b.len, NULL);       /* the same term, unshared */
    av_buf_free(&b);
    REQUIRE(tree != AV_NONE);
    uint32_t prog = av_app(a, tree, av_parse(a, "X", 1, NULL));
    av_root_push(a, &prog);
    uint32_t m = av_jets_match(a, prog);
    CHECK_EQ(jet_nodes(a, m, 0), 1);
    av_root_pop(a);
    av_root_pop(a);
    av_arena_free(a);
}

TEST(jets_survive_collection) {
    FILE *f = test_open("tests/fixtures/t1.ski");
    static char src[1 << 16];
    size_t len = fread(src, 1, sizeof src, f);
    fclose(f);
    for (int st = 0; st < 2; st++) {
        av_arena *a = av_arena_new(64);
        CHECK(av_jets_load(a, DICT, 8, NULL) == 135);
        uint32_t t = av_jets_match(a, av_parse(a, src, len, NULL));
        run_out r = run(a, t, st ? AV_SHARE : AV_COPY, true, UINT64_MAX, true);
        CHECK(a->collections > 0);
        CHECK(!r.fault && r.s == AV_WHNF && r.calls > 0);
        if (!st) CHECK_EQ(r.steps, 91556);
        free(r.text);
        av_arena_free(a);
    }
}

TEST(a_snapshot_holds_no_jets) {
    av_arena *a = av_arena_new(0);
    CHECK(av_jets_load(a, DICT, 8, NULL) == 135);
    FILE *f = test_open("tests/fixtures/t0.ski");
    static char src[1 << 14];
    size_t len = fread(src, 1, sizeof src, f);
    fclose(f);
    uint32_t t = av_jets_match(a, av_parse(a, src, len, NULL));
    bool wrapped = false;
    for (uint32_t i = 0; i < a->used; i++) wrapped |= av_tag(a, i) == AV_JET;
    CHECK(wrapped);
    av_buf before = { 0 }, after = { 0 };
    CHECK(av_print(a, t, 1000000, &before));
    CHECK(av_snapshot_save(a, t, "build/test_jets.img", NULL));
    uint32_t r;
    av_arena *b = av_snapshot_load("build/test_jets.img", &r, NULL);
    CHECK(b != NULL);
    if (b) {
        CHECK(av_print(b, r, 1000000, &after) && strcmp(before.s, after.s) == 0);
        av_arena_free(b);
    }
    av_buf_free(&before);
    av_buf_free(&after);
    av_arena_free(a);
}

/*  The bug this guards against: share mode writes in place, and a jet
 *  node's term---the dashboard's, or reached through a residual's inner
 *  jets---must never be written, or a later copy-mode run charges a
 *  registered cost against a different tree.  Share runs over jetted
 *  terms leave every dashboard term's hash unchanged, and a graph a share
 *  run has already reduced still counts the same jets on and off. */
TEST(share_mode_never_writes_the_dashboard) {
    av_arena *a = av_arena_new(1u << 16);
    CHECK(av_jets_load(a, DICT, 8, NULL) == 135);
    uint32_t n = a->njets;
    char (*before)[2][27] = malloc(n * sizeof *before);
    for (uint32_t i = 0; i < n; i++) {
        av_structural_hash(a, a->jets[i].fallback, before[i][0]);
        av_structural_hash(a, a->jets[i].residual, before[i][1]);
    }
    for (int round = 0; round < 3; round++)
    for (uint32_t id = 0; id < n; id++) {
        uint32_t t = a->jets[id].fallback;
        for (unsigned i = 0; i < a->jets[id].arity + round; i++) t = av_app(a, t, gen(a, 3));
        t = av_jets_match(a, t);
        av_root_push(a, &t);
        run_out sh = run(a, t, AV_SHARE, false, 100000, true);   /* writes t */
        CHECK(!sh.fault);
        /* the two states compared as graphs: after share mode's sharing
         * their trees can be too large to print */
        av_opts o = av_opts_default();
        o.strategy = AV_COPY;
        o.whnf_only = true;
        o.max_steps = 5000;
        o.jet_check = 1;
        av_result on = av_reduce(a, t, &o);
        uint32_t on_term = on.term;
        av_root_push(a, &on_term);
        o.jets = false;
        o.jet_check = 0;
        av_result off = av_reduce(a, t, &o);
        CHECK(!on.jet_fault);
        CHECK_EQ(on.status, off.status);
        CHECK_EQ(on.steps, off.steps);
        int eq = av_equal(a, on_term, off.term, 10000000);
        if (eq != 1) fprintf(stderr, "  jet %u round %d: states %s\n", id, round,
                             eq ? "too large to compare" : "differ");
        CHECK_EQ(eq, 1);
        free(sh.text);
        av_root_pop(a);
        av_root_pop(a);
    }
    for (uint32_t i = 0; i < n; i++) {
        char h[27];
        av_structural_hash(a, a->jets[i].fallback, h);
        CHECK(strcmp(h, before[i][0]) == 0);
        av_structural_hash(a, a->jets[i].residual, h);
        CHECK(strcmp(h, before[i][1]) == 0);
    }
    free(before);
    av_arena_free(a);
}

/*  A fire rebuilds its residual's closed subterms, where stepping shares
 *  them.  Under a node cap that stepping fits, a fire that cannot have its
 *  nodes steps instead: S I (K B), B 2,001 nodes. */
TEST(a_fire_short_of_nodes_steps) {
    size_t n = 2000, len = 1;
    char *b = malloc(4 * n + 64);
    strcpy(b, "S");
    for (size_t i = 0; i < n; i++) {                  /* S (S (... S)) */
        memmove(b + 3, b, len + 1);
        memcpy(b, "S (", 3);
        len += 3;
        b[len++] = ')';
        b[len] = '\0';
    }
    char *g = malloc(len + 32), *src = malloc(len + 64);
    snprintf(g, len + 32, "S I (K (%s))", b);
    snprintf(src, len + 64, "(%s) I", g);
    for (int on = 0; on < 2; on++) {
        av_arena *a = av_arena_new(256);
        uint32_t j = av_parse(a, g, strlen(g), NULL);
        av_root_push(a, &j);
        CHECK(av_jet_register(a, j, 0, 1000000, NULL) != AV_NONE);
        uint32_t t = av_jets_match(a, av_parse(a, src, strlen(src), NULL));
        av_root_push(a, &t);
        av_opts o = av_opts_default();
        o.strategy = AV_COPY;
        o.whnf_only = true;
        o.jets = on;
        o.max_nodes = 6000;
        av_result r = av_reduce(a, t, &o);
        CHECK_EQ(r.status, AV_WHNF);
        CHECK_EQ(r.steps, 4);
        av_arena_free(a);
    }
    free(b);
    free(g);
    free(src);
}

TEST_MAIN(
    TEST_CASE(the_hash_is_skijacks),
    TEST_CASE(every_dictionary_hash_matches),
    TEST_CASE(the_loader_finds_what_hash_all_finds),
    TEST_CASE(registration_follows_the_rules),
    TEST_CASE(the_dictionary_registers),
    TEST_CASE(every_jet_leaves_counts_and_states_alone),
    TEST_CASE(the_check_catches_a_corrupted_jet),
    TEST_CASE(a_digest_match_is_not_enough),
    TEST_CASE(a_collision_is_refused_not_merged),
    TEST_CASE(a_jet_matches_a_copy_that_shares_less),
    TEST_CASE(share_mode_never_writes_the_dashboard),
    TEST_CASE(jets_survive_collection),
    TEST_CASE(a_snapshot_holds_no_jets),
    TEST_CASE(a_fire_short_of_nodes_steps),
)
