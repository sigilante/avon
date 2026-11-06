/**  test_nockdec.c
 *
 *  The transported Nock decrements (src/nockdec.c) on skinock's own terms,
 *  as scripts/PinDec.lean prints them, each registering only under its
 *  pinned digest: jets/pins/jetT-decF.dag (SKInock d89b96c), the Λ
 *  word, and jets/pins/jetT-hoonDecBodyF.dag (SKInock fe3c031), Hoon's
 *  ++dec arm.
 *
 *  The Λ word's digest.  On every encoded stack the jet fires in one step and reaches
 *  the normal form the term reaches without it, byte for byte: [n r] to
 *  [n-1 r], Err on [0 r], on a cell at the head and on an atom.  A head
 *  atom of 32 bits fires; one of 33 runs the term.  An argument that is
 *  not an encoded noun once reduced---a Form, bits with a trailing 0---runs
 *  the term.
 *
 *  Hoon's ++dec on the gate core [bat [n ctx]]: the atom n-1, Err on a
 *  zero sample, an atom and [bat atom], one step, the term's normal form,
 *  whatever bat and ctx hold and with either cell carrying code.  A cell
 *  sample, where the arm diverges, runs the term.  The bare arm
 *  (jets/pins/nockToSki-hoonDecBodyF.dag, SKInock 1ad32d5) does the same.
 *
 *  An argument that only reduces to one the jet answers for, a thunk, a
 *  core whose fields are redexes, an inner call, is reduced in place first
 *  and fires, after those contractions, to the unjetted normal form; one
 *  with no weak head normal form declines.  A tree copy of a term binds,
 *  and skinock's whole program hoon_dec_7 fires its bare arm, unshared or
 *  shared with the arm kept literal.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "../src/jets.h"
#include "test.h"

static bool hoon;                   /* the runs below: Hoon's ++dec, else the Λ word */
static bool bare;                   /* with hoon: the bare arm nockToSki hoonDecBodyF */
static bool tree;                   /* the term applied a tree copy, never hash-consed */

static char *file_src(const char *path, size_t *len) {
    FILE *f = test_open(path);
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    char *p = malloc((size_t)n + 1);
    *len = fread(p, 1, (size_t)n, f);
    p[*len] = '\0';
    fclose(f);
    return p;
}

static char *term_src(size_t *len) {
    return file_src(!hoon ? "jets/pins/jetT-decF.dag"
                    : bare ? "jets/pins/nockToSki-hoonDecBodyF.dag"
                           : "jets/pins/jetT-hoonDecBodyF.dag", len);
}

/*  ------------------------------------------- nouns, in skinock's encoding */

typedef struct { char *s; size_t n, cap; } text;

static void put(text *t, const char *s) {
    size_t k = strlen(s);
    if (t->n + k + 1 > t->cap) {
        t->cap = 2 * (t->n + k + 1);
        t->s = realloc(t->s, t->cap);
    }
    memcpy(t->s + t->n, s, k + 1);
    t->n += k;
}

/*  pairT x y, x and y written by the callbacks */
#define PAIR(t, X, Y) do { put(t, "S (S I (K ("); X; put(t, "))) (K ("); Y; put(t, "))"); } while (0)

/*  bits least significant first, then `pad` 0 bits past the last 1 */
static void bits(text *t, uint64_t n, int pad) {
    if (n == 0 && pad == 0) { put(t, "K"); return; }
    put(t, "K (");
    if (n == 0) PAIR(t, put(t, "K I"), bits(t, 0, pad - 1));
    else PAIR(t, put(t, n & 1 ? "K" : "K I"), bits(t, n >> 1, pad));
    put(t, ")");
}

static void atom(text *t, uint64_t n, int pad) {
    put(t, "S (K K) (S (K K) (S (K K) (S I (K (");
    bits(t, n, pad);
    put(t, ")))))");
}

/*  A noun: "a<n>", "a<n>+<pad>" (that many trailing 0 bits), "[h t]",
 *  "{h t k}" (a Form), or "(I x)" (a thunk); "<x>", S K K x, a thunk whose
 *  contraction allocates; "b<n>", the atom with its bit list a thunk; "@",
 *  S I I (S I I), a term with no weak head normal form; or "~", S K, a
 *  closed term that is no noun's encoding. */
static const char *noun(text *t, const char *p) {
    if (*p == '~') {
        put(t, "S K");
        return p + 1;
    }
    if (*p == '@') {
        put(t, "S I I (S I I)");
        return p + 1;
    }
    if (*p == '<') {
        put(t, "S K K (");
        p = noun(t, p + 1);
        put(t, ")");
        return p + 1;
    }
    if (*p == 'b') {
        char *e;
        uint64_t n = strtoull(p + 1, &e, 10);
        put(t, "S (K K) (S (K K) (S (K K) (S I (K (I (");
        bits(t, n, 0);
        put(t, "))))))");
        return e;
    }
    if (*p == 'a') {
        char *e;
        uint64_t n = strtoull(p + 1, &e, 10);
        int pad = 0;
        if (*e == '+') pad = (int)strtol(e + 1, &e, 10);
        atom(t, n, pad);
        return e;
    }
    if (*p == '(') {                                    /* (I x) */
        put(t, "I (");
        p = noun(t, p + 3);
        put(t, ")");
        return p + 1;
    }
    bool form = *p == '{';
    const char *q = p + 1;
    put(t, form ? "K (K (S (K K) (S (" : "K (S (K K) (S (K K) (");
    PAIR(t, q = noun(t, q), q = noun(t, q + 1));
    if (form) {
        put(t, ") (K (");
        q = noun(t, q + 1);
        put(t, ")))))");
    } else {
        put(t, ")))");
    }
    return q + 1;
}

/*  ------------------------------------------------------------- runs */

/*  t copied as a tree: every application node fresh, at each place it
 *  occurs.  The arena must hold the tree without collecting. */
static uint32_t unshare(av_arena *a, uint32_t t) {
    t = av_view(a, t);
    if (av_tag(a, t) != AV_APP) return t;
    uint32_t f = unshare(a, av_left(a, t)), x = unshare(a, av_right(a, t));
    return f == AV_NONE || x == AV_NONE ? AV_NONE : av_app(a, f, x);
}

typedef struct {
    av_status status;
    uint64_t steps, calls, declines, unbound, collections;
    long kept;
    char *nf;
} decrun;

static size_t crowd;                /* the arena left short of that many free nodes */

#define FUEL 50000000u              /* a cap: every run that ends here ends far within it */

#define NEED(cond) do { CHECK(cond); if (!(cond)) { av_arena_free(a); return out; } } while (0)

/*  jetT decF applied to the noun, or to jetT decF applied to it when
 *  nested; with the jet on or off; at most fuel contractions. */
static decrun dec_run(const char *n, bool on, bool nested, uint64_t fuel) {
    decrun out = { 0 };
    av_arena *a = av_arena_new(tree ? 1u << 21 : 1u << 18);     /* a tree copy never collects */
    size_t len;
    char *src = term_src(&len);
    const char *msg = NULL;
    uint32_t j = av_parse_dag(a, src, len, &msg);
    free(src);
    NEED(j != AV_NONE);
    av_root_push(a, &j);
    const char *err = NULL;
    uint32_t id = hoon ? av_hoon_dec_register(a, j, &err) : av_nock_dec_register(a, j, &err);
    NEED(id != AV_NONE);                    /* the pin holds */
    text t = { 0 };
    noun(&t, n);
    uint32_t x = av_parse(a, t.s, t.n, NULL);
    free(t.s);
    NEED(x != AV_NONE);
    uint32_t head = j;
    if (tree) {
        /* the term copied as a tree, as a backtick-prefix input loads,
         * its subterms never shared */
        head = unshare(a, j);
        NEED(head != AV_NONE && av_equal(a, head, j, 100000000) == 1);
    }
    uint32_t root = av_app(a, head, x);
    if (nested) root = av_app(a, head, root);
    av_root_pop(a);
    root = av_jets_match(a, root);
    NEED(root != AV_NONE);
    out.kept = av_pin_bind(a, root, id);
    while (crowd && a->cap - a->used >= crowd)
        (void)av_app(a, AV_NODE_S, AV_NODE_K);  /* garbage: the fire must collect */
    av_opts o = av_opts_default();
    o.nock_dec = on && !hoon;
    o.hoon_dec = on && hoon;
    o.max_steps = fuel;
    av_root_push(a, &root);
    av_result r = av_reduce(a, root, &o);
    av_root_pop(a);
    out.status = r.status;
    out.steps = r.steps;
    out.calls = hoon ? r.hoon_dec_calls : r.nock_dec_calls;
    out.declines = hoon ? r.hoon_dec_declines : r.nock_dec_declines;
    out.unbound = hoon ? r.hoon_dec_unbound : r.nock_dec_unbound;
    out.collections = a->collections;
    av_buf b = { 0 };
    if (r.term != AV_NONE && av_print(a, r.term, 100000000, &b)) out.nf = strdup(b.s);
    av_buf_free(&b);
    av_arena_free(a);
    return out;
}

/*  The noun's encoding, printed as the reducer prints a normal form. */
static char *enc(const char *n) {
    av_arena *a = av_arena_new(1u << 16);
    text t = { 0 };
    noun(&t, n);
    uint32_t x = av_parse(a, t.s, t.n, NULL);
    free(t.s);
    av_buf b = { 0 };
    char *s = x != AV_NONE && av_print(a, x, 100000000, &b) ? strdup(b.s) : NULL;
    av_buf_free(&b);
    av_arena_free(a);
    return s;
}

#define ERR "K (K (K I))"

/*  On and off, the same normal form; on, one fire in one step. */
static void fires_as_the_term(const char *n, const char *want) {
    decrun on = dec_run(n, true, false, FUEL), off = dec_run(n, false, false, FUEL);
    CHECK(on.kept == 1);
    CHECK(on.status == AV_NORMAL && off.status == AV_NORMAL);
    CHECK(on.steps == 1 && on.calls == 1 && on.declines == 0);
    CHECK(off.calls == 0 && off.steps > 1);
    CHECK(on.nf && off.nf && strcmp(on.nf, off.nf) == 0);
    CHECK(on.nf && want && strcmp(on.nf, want) == 0);
    if (!(on.nf && off.nf && strcmp(on.nf, off.nf) == 0)) fprintf(stderr, "    on %s\n", n);
    free(on.nf);
    free(off.nf);
}

TEST(the_pin_holds_the_term_and_refuses_another) {
    av_arena *a = av_arena_new(1u << 16);
    uint32_t p = av_parse(a, "S K K", 5, NULL);
    const char *err = NULL;
    CHECK(av_nock_dec_register(a, p, &err) == AV_NONE);
    CHECK(err && strstr(err, "not skinock's jetT decF"));
    av_arena_free(a);
    decrun r = dec_run("[a7 a0]", true, false, FUEL);    /* dec_run registers it pinned */
    CHECK(r.kept == 1);
    free(r.nf);
    /* registering it again is a no-op; as another pinned kind, refused */
    a = av_arena_new(1u << 18);
    size_t len;
    char *src = term_src(&len);
    const char *msg = NULL;
    uint32_t j = av_parse_dag(a, src, len, &msg);
    free(src);
    REQUIRE(j != AV_NONE);
    uint32_t id = av_nock_dec_register(a, j, &err);
    CHECK(id != AV_NONE && av_nock_dec_register(a, j, &err) == id);
    CHECK(p2_register(a, j, false, &err) == AV_NONE);
    av_arena_free(a);
}

TEST(a_stack_decrements_in_one_step) {
    char *w = enc("[a6 a0]");
    fires_as_the_term("[a7 a0]", w);
    free(w);
    w = enc("[a0 a0]");
    fires_as_the_term("[a1 a0]", w);
    free(w);
    w = enc("[a99 [a3 a4]]");
    fires_as_the_term("[a100 [a3 a4]]", w);
    free(w);
    w = enc("[a4 [[a1 a2] [[a3 a4] a5]]]");
    fires_as_the_term("[a5 [[a1 a2] [[a3 a4] a5]]]", w);
    free(w);
}

TEST(a_crash_is_err_in_one_step) {
    fires_as_the_term("[a0 a0]", ERR);            /* underflow */
    fires_as_the_term("[[a1 a2] a0]", ERR);       /* a cell at the head */
    fires_as_the_term("a5", ERR);                 /* an atom: no stack */
    fires_as_the_term("a0", ERR);
}

TEST(every_head_to_64_matches_the_term) {
    for (unsigned n = 0; n <= 64; n++) {
        char s[32], w[32];
        snprintf(s, sizeof s, "[a%u [a%u a1]]", n, n);
        snprintf(w, sizeof w, "[a%u [a%u a1]]", n ? n - 1 : 0, n);
        char *want = n ? enc(w) : strdup(ERR);
        fires_as_the_term(s, want);
        free(want);
    }
}

/*  The term counts up, so the unjetted run is out of reach at 32 bits: the
 *  answer is read back instead. */
TEST(a_32_bit_head_fires_and_a_33_bit_one_runs_the_term) {
    decrun r = dec_run("[a4294967295 a0]", true, false, FUEL);
    char *want = enc("[a4294967294 a0]");
    CHECK(r.status == AV_NORMAL && r.steps == 1 && r.calls == 1);
    CHECK(r.nf && want && strcmp(r.nf, want) == 0);
    free(r.nf);
    free(want);
    r = dec_run("[a4294967296 a0]", true, false, 200000);
    CHECK(r.status == AV_FUEL && r.calls == 0 && r.declines == 1);
    free(r.nf);
}

/*  Each runs the term, a decline counted, to the term's own normal form. */
static void declines_to_the_term(const char *n, bool nested) {
    decrun on = dec_run(n, true, nested, FUEL), off = dec_run(n, false, nested, FUEL);
    CHECK(on.status == AV_NORMAL && off.status == AV_NORMAL);
    if (on.status != AV_NORMAL) fprintf(stderr, "    status %d on %s\n", on.status, n);
    CHECK(on.declines >= 1);
    CHECK(on.nf && off.nf && strcmp(on.nf, off.nf) == 0);
    if (!(on.nf && off.nf && strcmp(on.nf, off.nf) == 0)) fprintf(stderr, "    on %s\n", n);
    free(on.nf);
    free(off.nf);
}

/*  An argument that reduces to one the jet answers for: reduced in place
 *  before the read, it fires, after the contractions that reduce it, to
 *  the term's normal form, in fewer steps. */
static void fires_once_reduced(const char *n, const char *want) {
    decrun on = dec_run(n, true, false, FUEL), off = dec_run(n, false, false, FUEL);
    CHECK(on.kept == 1);
    CHECK(on.status == AV_NORMAL && off.status == AV_NORMAL);
    CHECK(on.calls == 1 && on.declines == 0);
    CHECK(on.steps > 1 && on.steps < off.steps);
    CHECK(on.nf && off.nf && strcmp(on.nf, off.nf) == 0);
    CHECK(on.nf && want && strcmp(on.nf, want) == 0);
    if (!(on.calls == 1 && on.nf && off.nf && strcmp(on.nf, off.nf) == 0))
        fprintf(stderr, "    on %s: %llu calls, %llu declines\n", n,
                (unsigned long long)on.calls, (unsigned long long)on.declines);
    free(on.nf);
    free(off.nf);
}

TEST(a_lazy_stack_fires_once_reduced) {
    char *w = enc("[a2 a0]");
    fires_once_reduced("(I [a3 a0])", w);
    fires_once_reduced("[a3 (I a0)]", w);
    fires_once_reduced("<[<a3> <a0>]>", w);
    fires_once_reduced("[b3 a0]", w);
    free(w);
    fires_once_reduced("<[<[a1 a2]> a0]>", ERR);       /* a cell at the head, once reduced */
}

TEST(anything_but_an_encoded_noun_runs_the_term) {
    declines_to_the_term("[a3 {a1 a2 a0}]", false);     /* a Form in the rest */
    /* a trailing 0 bit in the head: the term counts up and never meets
     * it, as no canonical count equals it; the jet leaves it to the term */
    decrun r = dec_run("[a3+1 a0]", true, false, 300000);
    CHECK(r.status == AV_FUEL && r.calls == 0 && r.declines == 1);
    free(r.nf);
    declines_to_the_term("[a3 a0+2]", false);
    declines_to_the_term("[a3 <a0+2>]", false);
    /* no weak head normal form: the reduction runs out of fuel, the jet
     * declines, and the term, which forces it too, runs out after it */
    r = dec_run("[a3 @]", true, false, 300000);
    CHECK(r.status == AV_FUEL && r.calls == 0 && r.declines == 1);
    free(r.nf);
}

/*  The outer call's argument is the inner call: reduced before the read,
 *  the inner call fires, then the outer. */
TEST(a_call_over_a_call_fires_both) {
    decrun on = dec_run("[a3 a0]", true, true, FUEL), off = dec_run("[a3 a0]", false, true, FUEL);
    char *want = enc("[a1 a0]");
    CHECK(on.status == AV_NORMAL && on.declines == 0 && on.calls == 2 && on.steps == 2);
    CHECK(on.nf && off.nf && strcmp(on.nf, off.nf) == 0);
    CHECK(on.nf && want && strcmp(on.nf, want) == 0);
    CHECK(on.steps < off.steps);
    free(on.nf);
    free(off.nf);
    free(want);
}

TEST(a_collection_at_the_fire_keeps_the_answer) {
    char *lazy = enc("[a6 a0]");
    crowd = 2;                          /* short of an S contraction's two */
    decrun z = dec_run("<[<a7> <a0>]>", true, false, FUEL);    /* collects while it reduces */
    crowd = 0;
    CHECK(z.collections > 0);
    CHECK(z.status == AV_NORMAL && z.calls == 1 && z.declines == 0);
    CHECK(z.nf && lazy && strcmp(z.nf, lazy) == 0);
    free(z.nf);
    free(lazy);
    char *want = enc("[a40 [a7 [a8 a9]]]");
    decrun big = dec_run("[a41 [a7 [a8 a9]]]", true, false, FUEL);
    crowd = NOCK_DEC_NODES;
    decrun r = dec_run("[a41 [a7 [a8 a9]]]", true, false, FUEL);
    crowd = 0;
    CHECK(r.collections > big.collections);
    CHECK(r.status == AV_NORMAL && r.calls == 1);
    CHECK(r.nf && want && strcmp(r.nf, want) == 0);
    free(r.nf);
    free(big.nf);
    free(want);
}

TEST(the_reader_reads_only_an_encoded_stack) {
    av_arena *a = av_arena_new(1u << 16);
    struct { const char *n; int want; uint32_t k; } cs[] = {
        { "[a7 a0]", 1, 6 },       { "[a1 [a2 a3]]", 1, 0 },   { "[a0 a0]", 2, 0 },
        { "[[a1 a2] a0]", 2, 0 },  { "a9", 2, 0 },             { "[a3 {a1 a2 a0}]", 0, 0 },
        { "[a3+1 a0]", 0, 0 },     { "(I [a3 a0])", 0, 0 },    { "[a4294967296 a0]", 0, 0 },
        { "[a4294967295 a0]", 1, 4294967294u },
    };
    for (size_t i = 0; i < sizeof cs / sizeof cs[0]; i++) {
        text t = { 0 };
        noun(&t, cs[i].n);
        uint32_t x = av_parse(a, t.s, t.n, NULL), k = 0, rest = AV_NONE;
        if (x == AV_NONE) fprintf(stderr, "    no parse: %s: %s\n", cs[i].n, t.s);
        free(t.s);
        REQUIRE(x != AV_NONE);
        int got = av_nock_dec_read(a, x, &k, &rest);
        CHECK_EQ(got, cs[i].want);
        if (got == 1) CHECK_EQ(k, cs[i].k);
    }
    av_arena_free(a);
}

/*  ------------------------------------------------------- Hoon's ++dec */

TEST(hoons_pin_holds_its_term_and_refuses_the_others) {
    hoon = true;
    decrun r = dec_run("[a0 [a7 a0]]", true, false, FUEL);
    CHECK(r.kept == 1);
    free(r.nf);
    av_arena *a = av_arena_new(1u << 18);
    size_t len;
    char *src = term_src(&len);
    const char *msg = NULL, *err = NULL;
    uint32_t j = av_parse_dag(a, src, len, &msg);
    free(src);
    hoon = false;
    REQUIRE(j != AV_NONE);
    CHECK(av_nock_dec_register(a, j, &err) == AV_NONE);    /* not jetT decF */
    uint32_t id = av_hoon_dec_register(a, j, &err);
    CHECK(id != AV_NONE && av_hoon_dec_register(a, j, &err) == id);
    CHECK(p2_register(a, j, false, &err) == AV_NONE);
    av_arena_free(a);
}

TEST(a_core_decrements_in_one_step_whatever_bat_and_ctx_hold) {
    hoon = true;
    const char *cores[][2] = {
        { "[a0 [a7 a0]]", "a6" },                   { "[a0 [a1 a0]]", "a0" },
        { "[[a1 a2] [a100 [a3 a4]]]", "a99" },      { "[~ [a7 ~]]", "a6" },
        { "{[a1 a2] [a7 [a0 a0]] a3}", "a6" },      { "[a0 {a7 [a0 a0] a1}]", "a6" },
        { "{~ {a9 ~ ~} ~}", "a8" },
    };
    for (size_t i = 0; i < sizeof cores / sizeof cores[0]; i++) {
        char *w = enc(cores[i][1]);
        fires_as_the_term(cores[i][0], w);
        free(w);
    }
    for (unsigned n = 1; n <= 40; n++) {
        char s[48], w[16];
        snprintf(s, sizeof s, "[~ [a%u [a%u ~]]]", n, n);
        snprintf(w, sizeof w, "a%u", n - 1);
        char *want = enc(w);
        fires_as_the_term(s, want);
        free(want);
    }
    hoon = false;
}

TEST(a_core_with_no_decrement_is_err_in_one_step) {
    hoon = true;
    fires_as_the_term("[a0 [a0 a0]]", ERR);         /* underflow */
    fires_as_the_term("[~ [a0 ~]]", ERR);
    fires_as_the_term("a5", ERR);                   /* no sample */
    fires_as_the_term("[a0 a5]", ERR);
    fires_as_the_term("[~ a5]", ERR);
    fires_as_the_term("a3+1", ERR);                 /* whatever the atom's bits */
    fires_as_the_term("[~ a0+2]", ERR);
    hoon = false;
}

/*  The sample a cell: the arm diverges, and so does the term; the jet runs
 *  it.  Past 32 bits, or with a trailing 0, the jet runs the term too. */
TEST(a_core_the_jet_does_not_answer_for_runs_the_term) {
    hoon = true;
    const char *cores[] = { "[a0 [[a1 a2] a0]]", "[a0 [{a1 a2 a0} a0]]", "[a0 [a4294967296 a0]]",
                            "[a0 [a3+1 a0]]", "[a0 [a0+1 a0]]" };
    for (size_t i = 0; i < sizeof cores / sizeof cores[0]; i++) {
        decrun r = dec_run(cores[i], true, false, 300000);
        CHECK(r.status == AV_FUEL && r.calls == 0 && r.declines == 1);
        free(r.nf);
    }
    decrun r = dec_run("@", true, false, 300000);      /* no weak head normal form */
    CHECK(r.status == AV_FUEL && r.calls == 0 && r.declines == 1);
    free(r.nf);
    r = dec_run("[~ [@ ~]]", true, false, 300000);
    CHECK(r.status == AV_FUEL && r.calls == 0 && r.declines == 1);
    free(r.nf);
    r = dec_run("[a0 [a4294967295 a0]]", true, false, FUEL);
    char *want = enc("a4294967294");
    CHECK(r.status == AV_NORMAL && r.steps == 1 && r.calls == 1);
    CHECK(r.nf && want && strcmp(r.nf, want) == 0);
    free(r.nf);
    free(want);
    hoon = false;
}

/*  A core the arm meets lazily, as in a whole program, where a core is
 *  K (I (K Z)) W and its fields redexes too: reduced in place where the arm
 *  forces it, the core, its tail, the sample and its bits, never bat or
 *  ctx, which may have no normal form. */
static void lazy_cores(void) {
    const char *cores[][2] = {
        { "(I [a0 [a3 a0]])", "a2" },        { "<[a0 [a7 a0]]>", "a6" },
        { "[~ <[a7 ~]>]", "a6" },            { "[~ [<a7> ~]]", "a6" },
        { "<[~ <[<b100> ~]>]>", "a99" },     { "<{@ <{b9 @ @}> @}>", "a8" },
        { "[@ [<a1> @]]", "a0" },
    };
    for (size_t i = 0; i < sizeof cores / sizeof cores[0]; i++) {
        char *w = enc(cores[i][1]);
        fires_once_reduced(cores[i][0], w);
        free(w);
    }
    fires_once_reduced("<[~ <a5>]>", ERR);             /* [bat atom], once reduced */
    fires_once_reduced("[~ [<a0> ~]]", ERR);
}

TEST(a_lazy_core_fires_once_reduced) {
    hoon = true;
    lazy_cores();
    hoon = false;
}

/*  The bare arm, the term a compiled program carries: the same fires, the
 *  same declines, its own normal forms. */
TEST(the_bare_arm_fires_as_its_term) {
    hoon = bare = true;
    decrun r = dec_run("[a0 [a7 a0]]", true, false, FUEL);
    CHECK(r.kept == 1);
    free(r.nf);
    char *w = enc("a6");
    fires_as_the_term("[a0 [a7 a0]]", w);
    fires_as_the_term("{~ {a7 ~ ~} ~}", w);
    free(w);
    fires_as_the_term("[~ [a0 ~]]", ERR);
    fires_as_the_term("[~ a5]", ERR);
    lazy_cores();
    r = dec_run("[a0 [[a1 a2] a0]]", true, false, 300000);
    CHECK(r.status == AV_FUEL && r.calls == 0 && r.declines == 1);
    free(r.nf);
    hoon = bare = false;
}

/*  A term loaded as a tree, as from a backtick-prefix input, binds: the
 *  comparison with the pinned term is budgeted by its size as a tree. */
TEST(a_tree_copy_of_the_term_binds) {
    tree = true;
    char *w = enc("[a6 a0]");
    fires_as_the_term("[a7 a0]", w);
    free(w);
    hoon = true;
    for (int b = 0; b < 2; b++) {
        bare = b;
        w = enc("a6");
        fires_as_the_term("[a0 [a7 a0]]", w);
        free(w);
    }
    hoon = bare = tree = false;
}

/*  skinock's whole compiled program hoon_dec_7, release/nock/programs.txt's
 *  hoon_dec_12 with the sample 7, unshared, as a DAG (Lean's dagText): its
 *  ++dec arm is the bare term, applied lazily to an unreduced core.  Both of
 *  Hoon's terms registered, as jets/pins.conf has them; on, the arm fires
 *  once its argument is reduced, to the unjetted run's normal form.  The
 *  shared form (skinock's `share`) holds the arm only after its sharing
 *  betas, so no pin binds there; shared keeping the arm literal (skinock's
 *  `shareKeep`, hoon_dec_7.keep.dag, SKInock c5a3cb7), it binds and fires.
 *  All three are `nockstatement --dag unshared|shared|keep-hoon-dec` of the
 *  formula with the sample [1 7], at subject 0. */
static decrun program_run(const char *path, bool on) {
    decrun out = { 0 };
    av_arena *a = av_arena_new(1u << 18);
    size_t len;
    char *src = file_src(path, &len);
    const char *msg = NULL, *err = NULL;
    uint32_t t = av_parse_dag(a, src, len, &msg);
    free(src);
    NEED(t != AV_NONE);
    uint32_t id[2];
    hoon = true;
    av_root_push(a, &t);
    for (int b = 0; b < 2; b++) {
        bare = b;
        src = term_src(&len);
        uint32_t j = av_parse_dag(a, src, len, &msg);
        free(src);
        id[b] = j == AV_NONE ? AV_NONE : av_hoon_dec_register(a, j, &err);
    }
    av_root_pop(a);
    hoon = bare = false;
    NEED(id[0] != AV_NONE && id[1] != AV_NONE);
    t = av_jets_match(a, t);
    NEED(t != AV_NONE);
    out.kept = av_pin_bind(a, t, id[0]) + av_pin_bind(a, t, id[1]);
    av_opts o = av_opts_default();
    o.hoon_dec = on;
    o.max_steps = FUEL;
    av_root_push(a, &t);
    av_result r = av_reduce(a, t, &o);
    av_root_pop(a);
    out.status = r.status;
    out.steps = r.steps;
    out.calls = r.hoon_dec_calls;
    out.declines = r.hoon_dec_declines;
    av_buf b = { 0 };
    if (r.term != AV_NONE && av_print(a, r.term, 100000000, &b)) out.nf = strdup(b.s);
    av_buf_free(&b);
    av_arena_free(a);
    return out;
}

TEST(a_whole_program_fires_the_bare_arm) {
    decrun on = program_run("tests/data/hoon-dec/hoon_dec_7.dag", true),
           off = program_run("tests/data/hoon-dec/hoon_dec_7.dag", false);
    char *want = enc("a6");
    CHECK(on.kept == 1);
    CHECK(on.status == AV_NORMAL && off.status == AV_NORMAL);
    CHECK(on.calls == 1 && on.declines == 0);
    CHECK_EQ(off.steps, 12295u);
    CHECK_EQ(on.steps, 1011u);
    CHECK(on.nf && off.nf && strcmp(on.nf, off.nf) == 0);
    CHECK(on.nf && want && strcmp(on.nf, want) == 0);
    free(on.nf);
    free(off.nf);
    free(want);
    on = program_run("tests/data/hoon-dec/hoon_dec_7.shared.dag", true);
    off = program_run("tests/data/hoon-dec/hoon_dec_7.shared.dag", false);
    CHECK(on.kept == 0 && on.calls == 0 && on.steps == off.steps);
    CHECK(on.nf && off.nf && strcmp(on.nf, off.nf) == 0);
    free(on.nf);
    free(off.nf);
    on = program_run("tests/data/hoon-dec/hoon_dec_7.keep.dag", true);
    off = program_run("tests/data/hoon-dec/hoon_dec_7.keep.dag", false);
    want = enc("a6");
    CHECK(on.kept == 1);
    CHECK(on.status == AV_NORMAL && off.status == AV_NORMAL);
    CHECK(on.calls == 1 && on.declines == 0);
    CHECK_EQ(off.steps, 15387u);
    CHECK_EQ(on.steps, 4103u);
    CHECK(on.nf && off.nf && strcmp(on.nf, off.nf) == 0);
    CHECK(on.nf && want && strcmp(on.nf, want) == 0);
    free(on.nf);
    free(off.nf);
    free(want);
}

TEST(the_core_reader_reads_only_the_cells_and_the_sample) {
    av_arena *a = av_arena_new(1u << 16);
    struct { const char *n; int want; uint32_t k; } cs[] = {
        { "[a0 [a7 a0]]", 1, 6 },         { "[~ [a1 ~]]", 1, 0 },          { "{~ {a2 ~ ~} ~}", 1, 1 },
        { "[a0 [a0 a0]]", 2, 0 },         { "a9", 2, 0 },                  { "[~ a9]", 2, 0 },
        { "[a0 [[a1 a2] a0]]", 0, 0 },    { "[a0 [a3+1 a0]]", 0, 0 },      { "~", 0, 0 },
        { "[a0 ~]", 0, 0 },               { "[a0 [~ a0]]", 0, 0 },         { "(I [a0 [a3 a0]])", 0, 0 },
        { "[a0 [a4294967296 a0]]", 0, 0 }, { "[a0 [a4294967295 a0]]", 1, 4294967294u },
        { "a3+1", 2, 0 },          { "[~ a0+2]", 2, 0 },            { "[a0 [a0+1 a0]]", 0, 0 },
    };
    for (size_t i = 0; i < sizeof cs / sizeof cs[0]; i++) {
        text t = { 0 };
        noun(&t, cs[i].n);
        uint32_t x = av_parse(a, t.s, t.n, NULL), k = 0;
        free(t.s);
        REQUIRE(x != AV_NONE);
        int got = av_hoon_dec_read(a, x, &k);
        CHECK_EQ(got, cs[i].want);
        if (got != cs[i].want) fprintf(stderr, "    on %s\n", cs[i].n);
        if (got == 1) CHECK_EQ(k, cs[i].k);
    }
    av_arena_free(a);
}

TEST_MAIN(
    TEST_CASE(the_pin_holds_the_term_and_refuses_another),
    TEST_CASE(the_reader_reads_only_an_encoded_stack),
    TEST_CASE(a_stack_decrements_in_one_step),
    TEST_CASE(a_crash_is_err_in_one_step),
    TEST_CASE(every_head_to_64_matches_the_term),
    TEST_CASE(a_32_bit_head_fires_and_a_33_bit_one_runs_the_term),
    TEST_CASE(anything_but_an_encoded_noun_runs_the_term),
    TEST_CASE(a_lazy_stack_fires_once_reduced),
    TEST_CASE(a_call_over_a_call_fires_both),
    TEST_CASE(a_collection_at_the_fire_keeps_the_answer),
    TEST_CASE(hoons_pin_holds_its_term_and_refuses_the_others),
    TEST_CASE(the_core_reader_reads_only_the_cells_and_the_sample),
    TEST_CASE(a_core_decrements_in_one_step_whatever_bat_and_ctx_hold),
    TEST_CASE(a_core_with_no_decrement_is_err_in_one_step),
    TEST_CASE(a_core_the_jet_does_not_answer_for_runs_the_term),
    TEST_CASE(a_lazy_core_fires_once_reduced),
    TEST_CASE(the_bare_arm_fires_as_its_term),
    TEST_CASE(a_tree_copy_of_the_term_binds),
    TEST_CASE(a_whole_program_fires_the_bare_arm),
)
