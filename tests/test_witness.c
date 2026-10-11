/**  test_witness.c
 *
 *  The witness strategy: its tables for I K and S K K S are lean-ski's,
 *  byte for byte; atoms and over-budget runs are refused; and on random
 *  closed terms it halts with copy mode's count on the term copy mode
 *  reaches, read back from its heap as Mach.decode does.
 *  tests/witness_check.sh checks the corpus against lean-ski itself.
 */

#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "test.h"

static char *table_of(const char *src) {
    av_arena *a = av_arena_new(0);
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    av_witness w;
    av_buf b = { 0 };
    char *out = NULL;
    if (av_witness_run(a, t, 1u << 20, 1u << 20, &w, NULL) == AV_WHNF &&
        av_witness_table(a, t, &w, 4, &b))
        out = b.s;
    else
        av_buf_free(&b);
    av_witness_free(&w);
    av_arena_free(a);
    return out;
}

/* bench/plonky3/tables/ik.txt as ski-air writes it (lean-ski 0da9554) */
static const char IK[] =
    "`IK\n16\nI\nK\nA 0 1\nN\nC 1 3\nN\nN\nN\nN\nN\nN\nN\nN\nN\nN\nN\n16\n"
    "2 3 4\n0 4 5\n1 3 5\n1 3 5\n1 3 5\n1 3 5\n1 3 5\n1 3 5\n1 3 5\n1 3 5\n"
    "1 3 5\n1 3 5\n1 3 5\n1 3 5\n1 3 5\n1 3 5\n";

TEST(i_k_is_lean_skis_table) {
    char *t = table_of("I K");
    CHECK(t && strcmp(t, IK) == 0);
    free(t);
}

TEST(s_k_k_s_writes_three_cells_per_s) {
    av_arena *a = av_arena_new(0);
    uint32_t t = av_parse(a, "S K K S", 7, NULL);
    av_witness w;
    CHECK_EQ(av_witness_run(a, t, 100, 100, &w, NULL), AV_WHNF);
    CHECK_EQ(w.contractions, 2);                 /* S, then K */
    CHECK_EQ(w.loaded, 8);                       /* 7 term cells and nil */
    CHECK_EQ(w.nrows, 6);                        /* 3 unwinds, S, K, halt */
    CHECK_EQ(w.nmem, 8 + 3 + 3);                 /* 3 unwinds, 3 for S */
    /* loaded: S0 K1 A(0,1)2 K3 A(2,3)4 S5 A(4,5)6 N7; three unwinds leave
     * x = K1, y = K3, z = S5 on the stack, and the S step at c = 11 writes
     * A y z, C c s3, C z (c+1) */
    CHECK(w.mem[11].tag == AV_CELL_APP && w.mem[11].a == 3 && w.mem[11].b == 5);
    CHECK(w.mem[12].tag == AV_CELL_CONS && w.mem[12].a == 11 && w.mem[12].b == 7);
    CHECK(w.mem[13].tag == AV_CELL_CONS && w.mem[13].a == 5 && w.mem[13].b == 12);
    av_witness_free(&w);
    av_arena_free(a);
}

TEST(atoms_and_budgets_are_refused) {
    av_arena *a = av_arena_new(0);
    uint32_t t = av_parse(a, "I X", 3, NULL);
    av_witness w;
    const char *err = NULL;
    CHECK_EQ(av_witness_run(a, t, 100, 100, &w, &err), AV_SIZE);
    CHECK(err && strstr(err, "atoms"));
    av_witness_free(&w);

    t = av_parse(a, "S I I (S I I)", 13, NULL);    /* diverges */
    err = NULL;
    CHECK_EQ(av_witness_run(a, t, 1000, 1u << 20, &w, &err), AV_SIZE);
    CHECK(err && strstr(err, "row budget"));
    CHECK_EQ(w.nrows, 1000);
    av_witness_free(&w);
    err = NULL;
    CHECK_EQ(av_witness_run(a, t, 1u << 20, 1000, &w, &err), AV_SIZE);
    CHECK(err && strstr(err, "cell budget"));
    av_witness_free(&w);
    av_arena_free(a);
}

TEST(a_table_needs_a_run) {
    av_arena *a = av_arena_new(0);
    av_witness w;
    memset(&w, 0, sizeof w);
    av_buf b = { 0 };
    CHECK(!av_witness_table(a, AV_NODE_I, &w, 4, &b));
    av_buf_free(&b);
    av_arena_free(a);
}

TEST(prefix_form_round_trips) {
    av_arena *a = av_arena_new(0);
    const char *src = "S (K I) (S I K) K";
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    av_buf b = { 0 }, p = { 0 };
    CHECK(av_prefix(a, t, 100, &b));
    CHECK(strcmp(b.s, "```S`KI``SIKK") == 0);
    uint32_t u = av_parse_prefix(a, b.s, b.len, NULL);
    CHECK(u != AV_NONE && av_print(a, u, 100, &p) && strcmp(p.s, src) == 0);
    CHECK(av_parse_prefix(a, "`S", 2, NULL) == AV_NONE);
    CHECK(av_parse_prefix(a, "SK", 2, NULL) == AV_NONE);
    CHECK(av_parse_prefix(a, "`SX", 3, NULL) == AV_NONE);
    av_buf_free(&b);
    av_buf_free(&p);
    av_arena_free(a);
}

/*  -------------------------------------- against copy mode, at random */

/* Mach.decode: the head's term applied to the stack's arguments. */
static uint32_t cell_term(av_arena *a, const av_witness *w, uint32_t addr) {
    const av_cell *c = &w->mem[addr];
    switch (c->tag) {
    case AV_CELL_S: return AV_NODE_S;
    case AV_CELL_K: return AV_NODE_K;
    case AV_CELL_I: return AV_NODE_I;
    case AV_CELL_APP:
        return av_app(a, cell_term(a, w, c->a), cell_term(a, w, c->b));
    default: return AV_NONE;
    }
}

static uint32_t decode_state(av_arena *a, const av_witness *w) {
    const av_row *r = &w->rows[w->nrows - 1];
    uint32_t t = cell_term(a, w, r->hd);
    for (uint32_t s = r->stk; w->mem[s].tag == AV_CELL_CONS; s = w->mem[s].b)
        t = av_app(a, t, cell_term(a, w, w->mem[s].a));
    return t;
}

static uint64_t rng = 0x5851f42d4c957f2du;
static uint32_t next(void) {
    rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
    return (uint32_t)(rng >> 32);
}

static uint32_t gen(av_arena *a, int depth) {
    if (depth == 0 || next() % 10 < 3) {
        static const uint32_t leaf[] = { AV_NODE_S, AV_NODE_K, AV_NODE_I };
        return leaf[next() % 3];
    }
    uint32_t f = gen(a, depth - 1);
    return av_app(a, f, gen(a, depth - 1));
}

TEST(the_witness_halts_where_copy_mode_does) {
    int cases = getenv("AVON_FUZZ") ? atoi(getenv("AVON_FUZZ")) : 20000;
    int compared = 0;
    for (int i = 0; i < cases; i++) {
        av_arena *a = av_arena_new(0);
        uint32_t t = gen(a, 7);
        av_root_push(a, &t);
        av_opts o = av_opts_default();
        o.strategy = AV_COPY;
        o.whnf_only = true;
        o.max_steps = 3000;
        av_result r = av_reduce(a, t, &o);
        if (r.status == AV_WHNF) {
            av_buf want = { 0 }, got = { 0 };
            if (av_print(a, r.term, 20000, &want)) {
                av_witness w;
                CHECK_EQ(av_witness_run(a, t, 1u << 22, 1u << 22, &w, NULL), AV_WHNF);
                CHECK_EQ(w.contractions, r.steps);
                /* Air.checkA's final condition: the last row halts */
                uint32_t d = decode_state(a, &w);
                CHECK(d != AV_NONE && av_print(a, d, 20000, &got) &&
                      strcmp(got.s, want.s) == 0);
                av_witness_free(&w);
                compared++;
            }
            av_buf_free(&want);
            av_buf_free(&got);
        }
        av_root_pop(a);
        av_arena_free(a);
    }
    CHECK(compared > cases / 2);
}

/*  Jetted witnesses: lean-ski's jet file, and instantiation rows.
 *  The jet `λx y. x` compiles to K, so K's cell is its root; it pops two
 *  arguments, writes no cell, and its root is its first argument. */

static const char K_JET[] = "roots 1\n0 0\njets 1\n2 0 A 0\n";

TEST(a_jet_file_is_read_and_its_errors_refused) {
    av_jettable jt;
    CHECK(av_jettable_read(K_JET, strlen(K_JET), &jt, NULL));
    CHECK_EQ(jt.nroots, 1);
    CHECK_EQ(jt.njets, 1);
    CHECK_EQ(jt.jets[0].k, 2);
    CHECK_EQ(jt.jets[0].ncells, 0);
    CHECK(jt.jets[0].root.kind == AV_JOP_ARG && jt.jets[0].root.val == 0);
    av_jettable_free(&jt);
    /* a cell with operands, then each kind of bad file */
    const char *ok = "roots 0\njets 1\n1 2 L 1\n1\n3 L 0 A 0\n";
    CHECK(av_jettable_read(ok, strlen(ok), &jt, NULL));
    av_jettable_free(&jt);
    const char *bad[] = {
        "roots 1\n0 1\njets 1\n2 0 A 0\n",         /* a root names no jet */
        "roots 0\njets 1\n1 1 L 0\n3 L 0 A 0\n",   /* a local operand names itself */
        "roots 0\njets 1\n1 1 L 0\n3 A 1 A 0\n",   /* an argument past the arity */
        "roots 0\njets 1\n1 0 L 0\n",               /* a root past the cells */
        "roots 0\njets 0\nextra",                    /* text after the file */
        "roots 1\n0 0\njets 1\n2 0 X 0\n",         /* no such operand */
    };
    for (size_t i = 0; i < sizeof bad / sizeof bad[0]; i++) {
        const char *err = NULL;
        CHECK(!av_jettable_read(bad[i], strlen(bad[i]), &jt, &err));
        CHECK(err != NULL);
    }
}

TEST(a_jet_instantiates_at_its_root) {
    av_arena *a = av_arena_new(0);
    uint32_t t = av_parse(a, "K S K", 5, NULL);
    av_jettable jt;
    CHECK(av_jettable_read(K_JET, strlen(K_JET), &jt, NULL));
    av_witness w;
    uint64_t insts = 0;
    CHECK_EQ(av_witness_run_jets(a, t, &jt, 100, 100, &w, &insts, NULL), AV_WHNF);
    /* loaded: K0 S1 A(0,1)2 K3 A(2,3)4 N5; two unwinds put S and K on the
     * stack, then one row instantiates the jet at K: the head becomes S
     * (address 1), the stack the empty one, and nothing is written */
    CHECK_EQ(insts, 1);
    CHECK_EQ(w.contractions, 0);
    CHECK_EQ(w.nrows, 4);
    CHECK_EQ(w.nmem, 6 + 2);
    CHECK(w.rows[2].hd == 0 && w.rows[2].stk == 7 && w.rows[2].ctr == 8);
    CHECK(w.rows[3].hd == 1 && w.rows[3].stk == 5 && w.rows[3].ctr == 8);
    av_witness_free(&w);
    av_jettable_free(&jt);
    av_arena_free(a);
}

TEST(an_instantiation_needs_its_arguments) {
    av_arena *a = av_arena_new(0);
    uint32_t t = av_parse(a, "K S", 3, NULL);
    av_jettable jt;
    CHECK(av_jettable_read(K_JET, strlen(K_JET), &jt, NULL));
    av_witness w;
    uint64_t insts = 0;
    CHECK_EQ(av_witness_run_jets(a, t, &jt, 100, 100, &w, &insts, NULL), AV_WHNF);
    CHECK_EQ(insts, 0);                          /* K with one argument halts */
    CHECK_EQ(w.nrows, 2);
    av_witness_free(&w);
    av_jettable_free(&jt);
    av_arena_free(a);
}

/*  ------------------------------------------------------- probe segments */

static const char ZERO_PLAN[] = "plan 1\n0 2 0 0 0 0\n";   /* nat 0 = Zero */

static bool probe_of(const char *term, const char *plan_src, av_buf *out,
                     const char **err) {
    av_arena *a = av_arena_new(0);
    uint32_t t = av_parse(a, term, strlen(term), NULL);
    av_plan plan;
    av_witness w;
    av_probe pr;
    bool ok = false;
    if (av_plan_read(plan_src, strlen(plan_src), &plan, err)) {
        av_status st = av_witness_run_probe(a, t, NULL, &plan, 1000, 1000, &w, &pr, NULL, err);
        ok = st == AV_WHNF && av_witness_table(a, t, &w, 4, out) &&
             av_probe_table(&w, &pr, 4, out);
        static char kept[160];              /* *err may point into pr */
        if (*err) {
            snprintf(kept, sizeof kept, "%s", *err);
            *err = kept;
        }
        av_witness_free(&w);
        av_probe_free(&pr);
        av_plan_free(&plan);
    }
    av_arena_free(a);
    return ok;
}

/*  K is Zero, a nat's first constructor: the probe writes markers X 0 and
 *  X 1 and a stack of them, K selects X 0 over a nil. */
TEST(a_probe_binds_k_as_zero) {
    av_buf b = { 0 };
    const char *err = NULL;
    CHECK(probe_of("K", ZERO_PLAN, &b, &err));
    static const char want_mem[] =
        "K\n16\nK\nN\nX 0\nX 1\nC 2 5\nC 3 6\nN\nN\nN\nN\nN\nN\nN\nN\nN\nN\n16\n"
        "0 1 2\n0 4 7\n2 6 7\n";
    CHECK(b.s && strncmp(b.s, want_mem, strlen(want_mem)) == 0);
    /* rows padded with the last; then the start rows and the fields */
    CHECK(b.s && strstr(b.s, "2 6 7\nstarts 2\n0\n15\nfields 1\n0\n") != NULL);
    av_buf_free(&b);
}

TEST(a_probe_refuses_another_outcome) {
    av_buf b = { 0 };
    const char *err = NULL;
    /* Suc Zero: marker 1 over one field---K ends at marker 0 */
    CHECK(!probe_of("K", "plan 2\n0 2 1 1 0 0\n2 2 0 0 0 0\n", &b, &err));
    CHECK(err && strstr(err, "segment 0 ends at marker 0, not its marker 1"));
    /* one marker only: K stops short of its arguments */
    CHECK(!probe_of("K", "plan 1\n0 1 0 0 0 0\n", &b, &err));
    CHECK(err && strstr(err, "short of arguments"));
    /* a hand-built plan whose segment reads a field never popped */
    av_arena *a = av_arena_new(0);
    uint32_t k = av_parse(a, "K", 1, NULL);
    av_seg segs[2] = { { 0, 2, 0, 0, 0, 0 }, { 2, 2, 0, 0, 0, 0 } };
    av_plan hand = { segs, 2 };
    av_witness w;
    av_probe pr;
    CHECK_EQ(av_witness_run_probe(a, k, NULL, &hand, 1000, 1000, &w, &pr, NULL, &err), AV_SIZE);
    CHECK(err && strstr(err, "malformed plan"));
    av_witness_free(&w);
    av_probe_free(&pr);
    av_arena_free(a);
    av_buf_free(&b);
}

TEST(a_malformed_plan_is_refused) {
    av_plan p;
    const char *err = NULL;
    CHECK(!av_plan_read("plan 0\n", 7, &p, &err));
    CHECK(!av_plan_read("plan 1\n0 2 0 0 0\n", 17, &p, &err));
    CHECK(!av_plan_read("plan 1\n0 2 0 0 0 0 7\n", 21, &p, &err));
    CHECK(!av_plan_read("segs 1\n0 2 0 0 0 0\n", 19, &p, &err));
    /* shapes Air.planOf never gives */
    static const char *const bad[] = {
        "plan 1\n1 2 0 0 0 0\n",                  /* markers not from 0 */
        "plan 1\n0 2 2 0 0 0\n",                  /* ctor past k */
        "plan 1\n0 2 0 1 0 0\n",                  /* a field nobody reads */
        "plan 2\n0 2 1 1 0 0\n0 2 0 0 0 0\n",    /* overlapping markers */
        "plan 2\n0 2 1 1 0 0\n2 2 0 0 1 0\n",    /* parent not before */
        "plan 2\n0 2 1 1 0 0\n2 2 0 0 0 1\n",    /* no such field */
        "plan 3\n0 2 1 2 0 0\n2 2 0 0 0 0\n4 2 0 0 0 0\n",   /* read twice */
        "plan 1\n4294967295 2 0 0 0 0\n",         /* past 2^32 */
    };
    for (size_t i = 0; i < sizeof bad / sizeof *bad; i++) {
        err = NULL;
        CHECK(!av_plan_read(bad[i], strlen(bad[i]), &p, &err));
        if (!err) fprintf(stderr, "  accepted: %s", bad[i]);
    }
    CHECK(av_plan_read(ZERO_PLAN, strlen(ZERO_PLAN), &p, &err));
    CHECK(p.n == 1 && p.segs[0].k == 2);
    av_plan_free(&p);
}

/*  ------------------------------------------- composed statements, jetted */

/*  A statement by hand (Avon decides nothing of its meaning): a bit at 3, a
 *  region cell at 4, the nil at 5, and two segments, from `A 1 0` (I K)
 *  and from the region cell. */
static const char STMT[] =
    "formula test\nW 1\nlog 8 8 8 8\nbits 1\nroots 6 4\nnil 5\n6 5 7\n"
    "K\nI\nA 0 1\nW\nW\nN\nA 1 0\n";

static av_status composed_of(const char *stmt, const char *jets, const char *wit,
                             av_buf *out, uint64_t *insts, const char **err) {
    av_cstmt st;
    av_jettable jt;
    av_witness w = { 0 };
    size_t *ends = NULL;
    av_cell priv[8];
    av_status r = AV_SIZE;
    if (!av_cstmt_read(stmt, strlen(stmt), &st, err)) return r;
    if (av_jettable_read(jets, strlen(jets), &jt, err)) {
        if (av_cwitness_read(wit, strlen(wit), &st, priv, err)) {
            r = av_witness_run_composed(&st, priv, &jt, &w, &ends, insts, err);
            if (r == AV_WHNF && out && !av_composed_table(&st, &w, ends, out)) r = AV_SIZE;
        }
        av_jettable_free(&jt);
    }
    av_witness_free(&w);
    free(ends);
    av_cstmt_free(&st);
    return r;
}

/*  I K over the nil: unwind, I, a halt at K; the region cell K halts at
 *  once.  The rows and memory pad to 2^8, the ends are the restart and the
 *  padded table's last row. */
TEST(a_composed_table_pads_to_the_statements_heights) {
    av_buf b = { 0 };
    uint64_t insts = 9;
    const char *err = NULL;
    CHECK_EQ(composed_of(STMT, "roots 0\njets 0\n", "1\nK\n", &b, &insts, &err), AV_WHNF);
    CHECK_EQ(insts, 0);
    const char head[] = "formula test\nW 1\n256\nK\nI\nA 0 1\nK\nK\nN\nA 1 0\nC 0 5\nN\n";
    CHECK(b.s && strncmp(b.s, head, strlen(head)) == 0);
    const char *ends = b.s ? strstr(b.s, "ends 2\n2\n255\n256\n6 5 7\n1 7 8\n0 5 8\n4 5 8\n4 5 8\n") : NULL;
    CHECK(ends != NULL);
    size_t rows = 0;
    for (const char *p = ends; p && *p; p++) rows += *p == '\n';
    CHECK_EQ(rows, 4 + 256);                    /* ends 2, two ends, 256, the rows */
    av_buf_free(&b);
}

/*  A jet of arity 0 at the first root: one instantiation row, its root the
 *  global K. */
TEST(a_composed_run_instantiates_at_a_root) {
    av_buf b = { 0 };
    uint64_t insts = 0;
    CHECK_EQ(composed_of(STMT, "roots 1\n6 0\njets 1\n0 0 G 0\n", "0\nK\n", &b, &insts, NULL), AV_WHNF);
    CHECK_EQ(insts, 1);
    CHECK(b.s && strstr(b.s, "ends 2\n1\n255\n256\n6 5 7\n0 5 7\n4 5 7\n") != NULL);
    av_buf_free(&b);
}

TEST(a_composed_witness_must_satisfy_the_statement) {
    const char *err = NULL;
    /* the region cell S: the second segment halts at S */
    CHECK_EQ(composed_of(STMT, "roots 0\njets 0\n", "1\nS\n", NULL, NULL, &err), AV_INTERRUPTED);
    CHECK(err != NULL);
    /* no budgets: a composed statement, not one with jets */
    char plain[sizeof STMT];
    memcpy(plain, STMT, sizeof STMT);
    memcpy(strstr(plain, "log 8 8 8 8"), "log 8 9", 7);
    memmove(strstr(plain, "log 8 9") + 7, strstr(plain, "log 8 9") + 11, strlen(strstr(plain, "log 8 9") + 11) + 1);
    err = NULL;
    CHECK_EQ(composed_of(plain, "roots 0\njets 0\n", "1\nK\n", NULL, NULL, &err), AV_SIZE);
    CHECK(err != NULL && strstr(err, "budgets") != NULL);
    /* a witness of the wrong length */
    err = NULL;
    CHECK_EQ(composed_of(STMT, "roots 0\njets 0\n", "1\n", NULL, NULL, &err), AV_SIZE);
    CHECK(err != NULL);
}

TEST(a_malformed_statement_is_refused) {
    const char *bad[] = {
        "formula test\nW 1\nlog 7 8 8 8\nbits 1\nroots 6 4\nnil 5\n6 5 7\nK\nI\nA 0 1\nW\nW\nN\nA 1 0\n",
        "formula test\nW 1\nlog 11 11\nbits 1\nroots 6 4\nnil 5\n6 5 7\nK\nI\nA 0 1\nW\nW\nN\nA 1 0\n",
        "formula test\nW 1\nlog 8 8 8\nbits 1\nroots 6 4\nnil 5\n6 5 7\nK\nI\nA 0 1\nW\nW\nN\nA 1 0\n",
        "formula test\nW 1\nlog 8 8 8 8\nbits 1\nroots 6 4\nnil 5\n6 5 7\nK\nI\nA 0 1\nW\nW\nW\nA 1 0\n",
        "formula test\nW 1\nlog 8 8 8 8\nbits 1\nroots 6 4\nnil 5\n6 5 7\nK\nI\nA 0 1\nW\nN\nN\nA 1 0\n",
        "formula test\nW 1\nlog 8 8 8 8\nbits 1\nroots\nnil 5\n6 5 7\nK\nI\nA 0 1\nW\nW\nN\nA 1 0\n",
        "formula test\nW 1\nlog 8 8 8 8\nbits 1\nroots 6 4\nnil 5\n6 5 7\nK\nI\nA 0 1\nW\nW\nN\n",
        "theorem test\nW 1\nlog 8 8 8 8\nbits 1\nroots 6 4\nnil 5\n6 5 7\nK\nI\nA 0 1\nW\nW\nN\nA 1 0\n",
    };
    for (size_t i = 0; i < sizeof bad / sizeof *bad; i++) {
        av_cstmt st;
        const char *err = NULL;
        CHECK(!av_cstmt_read(bad[i], strlen(bad[i]), &st, &err));
        CHECK(err != NULL);
    }
    av_cstmt st;
    const char *err = NULL;
    const char trunc[] = "formula test\nW 1\nlog 8 8 8 8\nbits 1\nroots 6 4\nnil 5\n6 5 7\nK\nI\n";
    CHECK(!av_cstmt_read(trunc, strlen(trunc), &st, &err));
    CHECK(err && strcmp(err, "a truncated statement") == 0);
    const char nul[] = "formula a\0b\nW 1\n";
    CHECK(!av_cstmt_read(nul, sizeof nul - 1, &st, &err));
    CHECK(av_cstmt_read(STMT, strlen(STMT), &st, NULL));
    CHECK(st.log_rows == 8 && st.log_mem == 8 && st.log_pop == 8 && st.log_instw == 8);
    CHECK(st.nroots == 2 && st.roots[0] == 6 && st.roots[1] == 4 && st.ctr0 == 7);
    av_cstmt_free(&st);
}

TEST_MAIN(
    TEST_CASE(i_k_is_lean_skis_table),
    TEST_CASE(s_k_k_s_writes_three_cells_per_s),
    TEST_CASE(atoms_and_budgets_are_refused),
    TEST_CASE(a_table_needs_a_run),
    TEST_CASE(prefix_form_round_trips),
    TEST_CASE(the_witness_halts_where_copy_mode_does),
    TEST_CASE(a_jet_file_is_read_and_its_errors_refused),
    TEST_CASE(a_jet_instantiates_at_its_root),
    TEST_CASE(an_instantiation_needs_its_arguments),
    TEST_CASE(a_probe_binds_k_as_zero),
    TEST_CASE(a_probe_refuses_another_outcome),
    TEST_CASE(a_malformed_plan_is_refused),
    TEST_CASE(a_composed_table_pads_to_the_statements_heights),
    TEST_CASE(a_composed_run_instantiates_at_a_root),
    TEST_CASE(a_composed_witness_must_satisfy_the_statement),
    TEST_CASE(a_malformed_statement_is_refused),
)
