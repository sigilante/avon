/**  test_interp.c
 *
 *  The interpreter jet's acceptance.  The specs load; T2's cost is its
 *  object run, T0, plus the probes that decode its datum; and over random
 *  object terms and fuel, the jet gives the unjetted interpreter's
 *  outcome---constructor and decoded payload---for whnfF, wf5Abs (an error
 *  arm) and wf5Omg (a diverging arm, where the jet declines and both run
 *  out of host fuel).  tests/test_conformance.c runs the corpus, scry
 *  tables and fuel boundaries included, jets on.  Run from the repository
 *  root.
 */

#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "avon.h"
#include "test.h"

#define DIR "tests/conformance/"

static av_arena *loaded(void) {
    av_arena *a = av_arena_new(1u << 16);
    const char *err = NULL;
    CHECK_EQ(av_jets_load(a, DIR "dictionary.tsv", 8, &err), 135);
    CHECK_EQ(av_interps_load(a, DIR "interpreters.tsv", DIR "dictionary.tsv", &err), 5);
    return a;
}

static const av_interp *by_roles(const av_arena *a, unsigned nobj, int extra) {
    for (uint32_t i = 0; i < a->ninterps; i++) {
        const av_interp *p = &a->interps[i];
        if (p->nobj != nobj) continue;
        if (extra < 0 || p->orole[4] == extra) return p;
    }
    return NULL;
}

TEST(the_specs_load) {
    av_arena *a = loaded();
    const av_interp *w = by_roles(a, 4, -1);            /* whnfF: S K I App */
    CHECK(w != NULL);
    if (w) {
        CHECK_EQ(w->nparams, 0);
        CHECK_EQ(w->nres, 2);                           /* Nothing | Just */
        CHECK_EQ(w->rrole[w->value], AV_RROLE_VALUE);
        CHECK_EQ(w->rrole[w->timeout], AV_RROLE_TIMEOUT);
        CHECK(a->jets[w->jet].interp >= 0);
    }
    CHECK(by_roles(a, 5, AV_OROLE_ERR) != NULL);
    CHECK(by_roles(a, 5, AV_OROLE_DIVERGE) != NULL);
    CHECK(by_roles(a, 5, AV_OROLE_SCRY) != NULL);
    av_arena_free(a);
}

static uint8_t *slurp(const char *path, size_t *len) {
    FILE *f = test_open(path);
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *p = malloc((size_t)n);
    *len = fread(p, 1, (size_t)n, f);
    fclose(f);
    return p;
}

/*  T2 is whnfF over the quoted T0: the jet's object run is T0 itself, 340
 *  contractions; the rest of its charge is the probing that decodes the
 *  quoted interpreter and encodes the value. */
TEST(t2_costs_t0_plus_its_decoding) {
    av_arena *a = loaded();
    size_t len;
    uint8_t *bytes = slurp(DIR "tower.t2.skit", &len);
    CHECK(bytes != NULL);
    if (!bytes) { av_arena_free(a); return; }
    uint32_t t = av_jets_match(a, av_cue(a, bytes, len, NULL));
    free(bytes);
    av_opts o = av_opts_default();
    o.strategy = AV_COPY;
    o.whnf_only = true;
    o.interp_jets = true;                 /* unchecked: probes are the fire's */
    uint64_t p0 = a->probe_steps;
    av_result r = av_reduce(a, t, &o);
    uint64_t probes = a->probe_steps - p0;
    CHECK_EQ(r.status, AV_WHNF);
    CHECK_EQ(r.interp_calls, 1);
    CHECK(!r.jet_fault);
    /* After the fire the outer run brings the outcome datum, the value
     * constructor over the encoded value, to weak head normal form: */
    const av_interp *w = by_roles(a, 4, -1);
    av_opts c = av_opts_default();
    c.strategy = AV_COPY;
    c.whnf_only = true;
    uint32_t v = av_app(a, w->rctor[w->value], av_leaf(a, "X", 1));
    uint64_t post = av_reduce(a, v, &c).steps;
    CHECK_EQ(post, 2);
    /* and the rest of the charge is the object run: T0, exactly */
    CHECK_EQ(r.steps - probes - post, 340);
    printf("  T2 with the interpreter jet: %llu contractions -- the object run "
           "340 (T0), probing %llu, the outcome's own %llu\n",
           (unsigned long long)r.steps, (unsigned long long)probes,
           (unsigned long long)post);
    CHECK(r.steps < 504930 / 10);
    av_arena_free(a);
}

/*  A fire's object run may collect: the arena is left with f free nodes
 *  before T2 runs, for a sweep of f, so some run fills it inside the
 *  fire.  Every run must still cost 342 and reach the value. */
TEST(a_fire_survives_a_collection_inside_it) {
    size_t len;
    uint8_t *bytes = slurp(DIR "tower.t2.skit", &len);
    CHECK(bytes != NULL);
    if (!bytes) return;
    unsigned collected = 0;
    for (uint32_t f = 0; f < 4000; f += 25) {
        av_arena *a = loaded();
        uint32_t t = av_jets_match(a, av_cue(a, bytes, len, NULL));
        av_root_push(a, &t);
        while (a->cap - a->used > f) av_app(a, AV_NODE_I, AV_NODE_I);   /* garbage */
        uint64_t c0 = a->collections;
        av_opts o = av_opts_default();
        o.strategy = AV_COPY;
        o.whnf_only = true;
        o.interp_jets = true;
        av_result r = av_reduce(a, t, &o);
        CHECK_EQ(r.status, AV_WHNF);
        CHECK_EQ(r.steps, 342);
        CHECK_EQ(r.interp_calls, 1);
        collected += a->collections > c0;
        av_root_pop(a);
        av_arena_free(a);
    }
    free(bytes);
    printf("  T2 from a full arena: %u of 160 runs collected\n", collected);
    CHECK(collected > 0);
}

/*  ------------------------------------------------- the random differential */

static uint64_t rng = 0x94d049bb133111ebu;
static uint32_t next(void) {
    rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
    return (uint32_t)(rng >> 32);
}

/*  One node in five wrapped in I: the same value, but no longer the
 *  constructor by structure, so the jet must probe it. */
static uint32_t disguise(av_arena *a, uint32_t t) {
    return next() % 5 == 0 ? av_app(a, AV_NODE_I, t) : t;
}

/*  A random object term's datum, built from the spec's own constructors:
 *  leaves S, K, I and, with extra, the fifth constructor. */
static uint32_t datum(av_arena *a, const av_interp *p, int depth, bool extra) {
    unsigned app = 3;
    if (depth == 0 || next() % 10 < 4) {
        unsigned n = extra ? 4 : 3;
        unsigned pick = next() % n;
        return disguise(a, p->octor[pick == 3 ? 4 : pick]);
    }
    uint32_t f = datum(a, p, depth - 1, extra), x = datum(a, p, depth - 1, extra);
    return disguise(a, av_app(a, av_app(a, p->octor[app], f), x));
}

static const char SUC[] = "S (K K) (S (K (S I)) K)";

static uint32_t numeral(av_arena *a, unsigned k) {
    uint32_t n = AV_NODE_K;
    uint32_t suc = av_parse(a, SUC, strlen(SUC), NULL);
    for (unsigned i = 0; i < k; i++) n = disguise(a, av_app(a, suc, n));
    return n;
}

typedef struct { av_status s; unsigned ctor; int payload; uint32_t term; } outcome;

static outcome run(av_arena *a, const av_interp *p, uint32_t prog, bool jets,
                   av_strategy st) {
    av_opts o = av_opts_default();
    o.strategy = st;
    o.whnf_only = true;
    o.interp_jets = jets;
    o.jet_check = jets ? 1 : 0;
    o.max_steps = 3000000;
    o.no_collect = true;
    av_result r = av_reduce(a, prog, &o);
    outcome out = { r.status, 0, 0, AV_NONE };
    CHECK(!r.jet_fault);
    if (r.status != AV_WHNF) return out;
    av_peeled pe;
    av_opts po = av_opts_default();
    po.strategy = AV_COPY;
    po.no_collect = true;
    CHECK(av_peel(a, r.term, p->nres, &po, &pe, NULL));
    out.ctor = pe.ctor;
    if (pe.nfields == 1) {
        static const char *const names[] = { "S", "K", "I", "App", "X5" };
        out.term = av_decode(a, pe.field[0], p->nobj, names, 3, 5000000, &po, NULL);
        out.payload = out.term != AV_NONE;
    }
    return out;
}

static void differential(const av_interp *spec_kind(av_arena *), bool extra,
                         int cases, const char *label) {
    av_arena *a = loaded();
    const av_interp *p = spec_kind(a);
    CHECK(p != NULL);
    if (!p) { av_arena_free(a); return; }
    int compared = 0, fuel_outs = 0;
    for (int i = 0; i < cases; i++) {
        uint32_t loop = a->jets[p->jet].fallback;
        uint32_t d = datum(a, p, 4, extra);
        unsigned k = next() % 24;
        uint32_t prog = av_app(a, av_app(a, loop, numeral(a, k)), d);
        prog = av_jets_match(a, prog);
        outcome off = run(a, p, prog, false, AV_COPY);
        outcome on = run(a, p, prog, true, AV_COPY);
        outcome sh = run(a, p, prog, true, AV_SHARE);
        CHECK_EQ(on.s, off.s);
        CHECK_EQ(sh.s, off.s);
        if (off.s != AV_WHNF) { fuel_outs++; continue; }
        CHECK_EQ(on.ctor, off.ctor);
        CHECK_EQ(sh.ctor, off.ctor);
        CHECK_EQ(on.payload, off.payload);
        if (off.payload && on.payload && sh.payload) {
            CHECK_EQ(av_equal(a, on.term, off.term, 10000000), 1);
            CHECK_EQ(av_equal(a, sh.term, off.term, 10000000), 1);
        }
        compared++;
    }
    printf("  %s: %d compared, %d past the host cap both ways\n", label,
           compared, fuel_outs);
    CHECK(compared > 0);
    av_arena_free(a);
}

static const av_interp *whnff(av_arena *a) { return by_roles(a, 4, -1); }
static const av_interp *wf5abs(av_arena *a) { return by_roles(a, 5, AV_OROLE_ERR); }
static const av_interp *wf5omg(av_arena *a) { return by_roles(a, 5, AV_OROLE_DIVERGE); }

TEST(whnff_agrees_with_its_interpreter) {
    differential(whnff, false, getenv("AVON_FUZZ") ? atoi(getenv("AVON_FUZZ")) : 150, "whnfF");
}

TEST(an_error_arm_agrees) {
    differential(wf5abs, true, getenv("AVON_FUZZ") ? atoi(getenv("AVON_FUZZ")) : 150, "wf5Abs");
}

TEST(a_diverging_arm_declines_and_diverges) {
    /* terms with Err reach its arm and diverge on the host, jet or not */
    differential(wf5omg, true, getenv("AVON_FUZZ") ? atoi(getenv("AVON_FUZZ")) / 4 + 1 : 30, "wf5Omg");
}

/*  A dictionary row is used only if its term has the row's hash: the
 *  numeral Zero's row given S for its K refuses the load. */
TEST(a_dictionary_row_must_be_its_hash) {
    size_t len;
    uint8_t *raw = slurp(DIR "dictionary.tsv", &len);
    REQUIRE(raw != NULL);
    char *d = malloc(len + 1);                       /* slurp's bytes, as a string */
    REQUIRE(d != NULL);
    memcpy(d, raw, len);
    d[len] = '\0';
    free(raw);
    const char *zero = "skijack-1:86be9a55762d316a";   /* interpreters.tsv's nat Zero */
    char *row = strstr(d, zero);
    REQUIRE(row != NULL);
    char *t1 = strchr(row, '\t'), *t2 = t1 ? strchr(t1 + 1, '\t') : NULL, *nl = t2 ? strchr(t2, '\n') : NULL;
    REQUIRE(nl != NULL);
    char path[] = "/tmp/avon-dict-XXXXXX";
    int fd = mkstemp(path);
    REQUIRE(fd >= 0);
    FILE *f = fdopen(fd, "w");
    REQUIRE(f != NULL);
    fwrite(d, 1, (size_t)(t2 + 1 - d), f);           /* through the second tab */
    fputs("S", f);                                    /* not Zero's term, K */
    fputs(nl, f);
    fclose(f);
    av_arena *a = av_arena_new(1u << 16);
    const char *err = NULL;
    CHECK(av_interps_load(a, DIR "interpreters.tsv", path, &err) < 0);
    CHECK(err != NULL && strstr(err, "hash") != NULL);
    av_arena_free(a);
    unlink(path);
    free(d);
}

TEST_MAIN(
    TEST_CASE(the_specs_load),
    TEST_CASE(t2_costs_t0_plus_its_decoding),
    TEST_CASE(a_fire_survives_a_collection_inside_it),
    TEST_CASE(whnff_agrees_with_its_interpreter),
    TEST_CASE(an_error_arm_agrees),
    TEST_CASE(a_diverging_arm_declines_and_diverges),
    TEST_CASE(a_dictionary_row_must_be_its_hash),
)
