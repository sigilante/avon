/**  test_p2.c
 *
 *  Poseidon2 over BabyBear (src/p2.c): the specification's three test
 *  vectors, and inputs at or above p permuting as their residues do, as
 *  the jet's 31-bit elements may be.  The statements' readers.  And the
 *  native jet (docs/DESIGN.md §6.12), with a stand-in for P's term: a
 *  state is read only in exactly stateN's form; P at the head of one fires
 *  in one step, to the permuted state; any other argument runs the term;
 *  a jet node whose term is not the registered one is unbound.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "../src/jets.h"
#include "test.h"

#define P 2013265921u

TEST(the_test_vectors) { CHECK(av_p2_selftest()); }

TEST(inputs_permute_as_their_residues) {
    uint32_t a[16], b[16];
    for (uint32_t i = 0; i < 16; i++) {
        a[i] = i % 2 ? P + i : 0x7fffffffu - i;     /* 31-bit values at or above p */
        b[i] = a[i] % P;
    }
    av_p2_permute(a);
    av_p2_permute(b);
    CHECK(memcmp(a, b, sizeof a) == 0);
    for (int i = 0; i < 16; i++) CHECK(a[i] < P);
}

static bool reads(const char *text) {
    av_cstmt st;
    const char *err = NULL;
    bool ok = av_cstmt_read(text, strlen(text), &st, &err);
    if (ok) av_cstmt_free(&st);
    return ok;
}

/*  A `p2pre` statement: its header names h, J and the root; its `log` line
 *  five heights in [8, 20]; the blank cells exactly the bits and region.
 *  (A one-bit toy: the reader checks the form, not the circuit.) */
#define HEAD_OK "p2pre 7 99 4\n"
#define LOG_OK  "log 14 15 9 9 8\n"
#define REST    "bits 1\nroots 6\nnil 7\n6 7 8\nK\nI\nA 0 1\nW\nW\nS\nA 5 5\nN\n"

TEST(a_p2pre_statement_is_read) {
    CHECK(reads(HEAD_OK "W 1\n" LOG_OK REST));
    av_cstmt st;
    const char *src = HEAD_OK "W 1\n" LOG_OK REST;
    if (av_cstmt_read(src, strlen(src), &st, NULL)) {
        CHECK(st.p2);
        CHECK_EQ(st.p2_j, 99);
        CHECK_EQ(st.p2_root, 4);
        CHECK_EQ(st.log_pin, 9);
        CHECK_EQ(st.log_p2, 8);
        av_cstmt_free(&st);
    }
}

TEST(malformed_p2pre_statements_are_refused) {
    CHECK(!reads("p2pre 7 99\nW 1\n" LOG_OK REST));             /* no root */
    CHECK(!reads("p2pre 7 99 4 5\nW 1\n" LOG_OK REST));         /* an extra field */
    CHECK(!reads(HEAD_OK "W 1\nlog 14 15 9 9\n" REST));          /* four heights */
    CHECK(!reads(HEAD_OK "W 1\nlog 14 15 9 9 21\n" REST));       /* a height past 20 */
    CHECK(!reads(HEAD_OK "W 1\n" REST));                          /* no log line */
    CHECK(!reads(HEAD_OK "W 1\n" LOG_OK "bits 1\nroots 6\nnil 7\n6 7 8\nK\nI\nA 0 1\nK\nW\nS\nA 5 5\nN\n"));
                                                                   /* a bit cell not blank */
}

/*  A `p2commit` statement's header: `p2commit c0 … c7 PATTERN J ROOT`,
 *  the pattern 496 entries of `.`, `0`, `1`.  head is the header's words
 *  before the pattern, tail after it; pat_len entries, the first `bad`. */
static bool reads_commit(const char *head, size_t pat_len, char first, const char *tail) {
    char buf[1200];
    size_t n = (size_t)snprintf(buf, sizeof buf, "%s ", head);
    for (size_t i = 0; i < pat_len && n < sizeof buf - 200; i++) buf[n++] = i == 0 ? first : (i % 3 ? '.' : '1');
    snprintf(buf + n, sizeof buf - n, " %s\nW 1\n" LOG_OK REST, tail);
    return reads(buf);
}

TEST(a_p2commit_statement_is_read) {
    CHECK(reads_commit("p2commit 1 2 3 4 5 6 7 8", 496, '0', "99 4"));
    char buf[1200];
    size_t n = (size_t)snprintf(buf, sizeof buf, "p2commit 1 2 3 4 5 6 7 8 ");
    for (size_t i = 0; i < 496; i++) buf[n++] = '.';
    snprintf(buf + n, sizeof buf - n, " 99 4\nW 1\n" LOG_OK REST);
    av_cstmt st;
    if (av_cstmt_read(buf, strlen(buf), &st, NULL)) {
        CHECK(st.p2);
        CHECK_EQ(st.p2_j, 99);
        CHECK_EQ(st.p2_root, 4);
        av_cstmt_free(&st);
    } else {
        CHECK(false);
    }
}

TEST(malformed_p2commit_statements_are_refused) {
    CHECK(!reads_commit("p2commit 1 2 3 4 5 6 7 8", 495, '0', "99 4"));     /* a short pattern */
    CHECK(!reads_commit("p2commit 1 2 3 4 5 6 7 8", 497, '0', "99 4"));     /* a long one */
    CHECK(!reads_commit("p2commit 1 2 3 4 5 6 7 8", 496, 'x', "99 4"));     /* a bad entry */
    CHECK(!reads_commit("p2commit 1 2 3 4 5 6 7", 496, '0', "99 4"));       /* seven elements */
    CHECK(!reads_commit("p2commit 1 2 3 4 5 6 7 8 9", 496, '0', "99 4"));   /* nine */
    CHECK(!reads_commit("p2commit 1 2 3 4 5 6 7 x", 496, '0', "99 4"));     /* not a number */
    CHECK(!reads_commit("p2commit 1 2 3 4 5 6 7 8", 496, '0', "99"));       /* no root */
    CHECK(!reads_commit("p2commit 1 2 3 4 5 6 7 8", 496, '0', "99 4 5"));   /* an extra word */
    CHECK(!reads_commit("p2commit 1 2 3 4 5 6 7 8", 496, '0', "99  4"));    /* an empty word */
    CHECK(!reads_commit("p2commit 1 2 3 4 5 6 7 8", 496, '0', "99 4 "));    /* a trailing space */
    CHECK(!reads_commit("p2commit 1 2 3 4 5 6 7 8", 496, '0', "99\t4"));    /* a tab */
    CHECK(!reads_commit("p2commit 1 2 3 4 5 6 7\t8", 496, '0', "99 4"));
    CHECK(!reads_commit(" p2commit 1 2 3 4 5 6 7 8", 496, '0', "99 4"));    /* a leading space */
    /* a CR before the newline is a line end, as for every line read */
    CHECK(reads_commit("p2commit 1 2 3 4 5 6 7 8", 496, '0', "99 4\r"));
}

/*  ---------------------------------------------------------- the jet */

/*  Text for pairT a b, a and b already printed; and for stateN vs, with
 *  hooks to spoil it: the bit at (elt, bit) printed as `bad`, element elt
 *  given `nbits` bits, or the list cut to `nelts`. */
static char *pair_text(const char *x, bool xapp, const char *y, bool yapp) {
    size_t n = strlen(x) + strlen(y) + 32;
    char *s = malloc(n);
    snprintf(s, n, "S (S I (K %s%s%s)) (K %s%s%s)", xapp ? "(" : "", x, xapp ? ")" : "",
             yapp ? "(" : "", y, yapp ? ")" : "");
    return s;
}

typedef struct { int elt, bit; const char *bad; int nbits_elt, nbits; int nelts; } spoil;

static char *state_text(const uint32_t vs[16], spoil sp) {
    char *st = strdup("K");
    bool stapp = false;
    int nelts = sp.nelts ? sp.nelts : 16;
    for (int i = nelts - 1; i >= 0; i--) {
        int nb = sp.nbits && i == sp.nbits_elt ? sp.nbits : 31;
        char *e = strdup("K");
        bool eapp = false;
        for (int j = nb - 1; j >= 0; j--) {
            const char *b = vs[i] >> j & 1u ? "K" : "K I";
            if (sp.bad && i == sp.elt && j == sp.bit) b = sp.bad;
            char *n = pair_text(b, strchr(b, ' ') != NULL, e, eapp);
            free(e);
            e = n;
            eapp = true;
        }
        char *n = pair_text(e, true, st, stapp);
        free(e);
        free(st);
        st = n;
        stapp = true;
    }
    return st;
}

static const uint32_t VS[16] = { 0, 1, 2, 0x7fffffffu, P, P - 1, 12345, 1u << 30,
                                 7, 99991, 3, 5, 0x55555555u, 0x2aaaaaaau, 42, 1000000007u };

static bool read_text(const char *text, uint32_t out[16]) {
    av_arena *a = av_arena_new(1u << 16);
    uint32_t t = av_parse(a, text, strlen(text), NULL);
    bool ok = t != AV_NONE && av_p2_state_read(a, t, out);
    av_arena_free(a);
    return ok;
}

TEST(a_state_is_read_back) {
    char *text = state_text(VS, (spoil){ 0 });
    uint32_t out[16];
    CHECK(read_text(text, out));
    CHECK(memcmp(out, VS, sizeof out) == 0);
    free(text);
}

TEST(anything_but_a_state_is_not_read) {
    const spoil bad[] = {
        { .elt = 3, .bit = 7, .bad = "I" },             /* a bit neither K nor K I */
        { .elt = 0, .bit = 0, .bad = "K K" },
        { .elt = 15, .bit = 30, .bad = "S" },
        { .nbits_elt = 5, .nbits = 30 },                /* an element of 30 bits */
        { .nbits_elt = 5, .nbits = 32 },                /* of 32 */
        { .nelts = 15 },                                /* fifteen elements */
    };
    for (size_t i = 0; i < sizeof bad / sizeof *bad; i++) {
        char *text = state_text(VS, bad[i]);
        uint32_t out[16];
        CHECK(!read_text(text, out));
        free(text);
    }
    uint32_t vs17[16];
    memcpy(vs17, VS, sizeof vs17);
    char *text = state_text(vs17, (spoil){ 0 });
    size_t n = strlen(text) + 64;
    char *more = malloc(n);
    /* seventeen: one more element in front */
    snprintf(more, n, "S (S I (K (S (S I (K K)) (K K)))) (K (%s))", text);
    uint32_t out[16];
    CHECK(!read_text(more, out));
    /* a pair spelled with K in I's place */
    char *swapped = strdup(text);
    swapped[5] = 'K';                                   /* "S (S I" -> "S (S K" */
    CHECK(strncmp(text, "S (S I", 6) == 0);
    CHECK(!read_text(swapped, out));
    free(swapped);
    free(more);
    free(text);
}

typedef struct {
    av_status status;
    uint64_t steps, p2_calls, p2_declines, collections;
    long kept;
    char *nf;
} jetrun;

static uint32_t arena_cap = 1u << 16;

/*  "S K K", a stand-in for P, registered as the jet, applied to arg; with
 *  forge, the jet node wraps "S K S" instead, as a digest collision would
 *  have it. */
static jetrun jet_run(const char *arg, bool on, bool forge) {
    jetrun out = { 0 };
    av_arena *a = av_arena_new(arena_cap);
    uint32_t p = av_parse(a, "S K K", 5, NULL);
    const char *err = NULL;
    CHECK(av_p2_register(a, p, &err) == AV_NONE);       /* the pin: not P */
    uint32_t id = p2_register(a, p, false, &err);
    CHECK(id != AV_NONE);
    size_t n = strlen(arg) + 32;
    char *src = malloc(n);
    snprintf(src, n, "%s (%s)", forge ? "S K S" : "S K K", arg);
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    free(src);
    CHECK(t != AV_NONE);
    t = av_jets_match(a, t);
    CHECK(t != AV_NONE);
    if (forge) {                    /* wrap the head as the jet, by hand */
        uint32_t f = av_res(a, av_left(a, t));
        uint32_t j = av_app(a, f, f);
        a->nodes[j] = (av_node){ (AV_JET << AV_TAG_SHIFT) | id, f };
        t = av_app(a, j, av_right(a, t));
    }
    out.kept = av_p2_bind(a, t, id);
    av_opts o = av_opts_default();
    o.p2 = on;
    av_root_push(a, &t);
    av_result r = av_reduce(a, t, &o);
    av_root_pop(a);
    out.status = r.status;
    out.steps = r.steps;
    out.p2_calls = r.p2_calls;
    out.p2_declines = r.p2_declines;
    out.collections = a->collections;
    av_buf b = { 0 };
    if (r.term != AV_NONE && av_print(a, r.term, 10000000, &b)) out.nf = strdup(b.s);
    av_buf_free(&b);
    av_arena_free(a);
    return out;
}

TEST(the_jet_permutes_a_state_in_one_step) {
    char *text = state_text(VS, (spoil){ 0 });
    uint32_t want[16];
    memcpy(want, VS, sizeof want);
    av_p2_permute(want);
    char *wtext = state_text(want, (spoil){ 0 });
    jetrun r = jet_run(text, true, false);
    CHECK(r.kept == 1);
    CHECK(r.status == AV_NORMAL);
    CHECK(r.steps == 1 && r.p2_calls == 1);
    CHECK(r.nf && strcmp(r.nf, wtext) == 0);
    free(r.nf);
    /* off, the stand-in's own term runs: S K K is I */
    r = jet_run(text, false, false);
    CHECK(r.p2_calls == 0 && r.steps == 2);
    CHECK(r.nf && strcmp(r.nf, text) == 0);
    free(r.nf);
    free(wtext);
    free(text);
}

TEST(a_collection_at_the_fire_keeps_the_answer) {
    char *text = state_text(VS, (spoil){ 0 });
    uint32_t want[16];
    memcpy(want, VS, sizeof want);
    av_p2_permute(want);
    char *wtext = state_text(want, (spoil){ 0 });
    jetrun big = jet_run(text, true, false);
    arena_cap = 64;                 /* the parse fills it; the fire collects */
    jetrun r = jet_run(text, true, false);
    arena_cap = 1u << 16;
    CHECK(r.collections > big.collections);
    CHECK(r.status == AV_NORMAL && r.p2_calls == 1);
    CHECK(r.nf && strcmp(r.nf, wtext) == 0);
    free(r.nf);
    free(big.nf);
    free(wtext);
    free(text);
}

TEST(any_other_argument_runs_the_term) {
    char *text = state_text(VS, (spoil){ 0 });
    size_t n = strlen(text) + 8;
    char *thunk = malloc(n);
    snprintf(thunk, n, "I (%s)", text);                 /* a state, not as it stands */
    jetrun r = jet_run(thunk, true, false);
    CHECK(r.status == AV_NORMAL && r.p2_calls == 0 && r.p2_declines == 1);
    CHECK(r.nf && strcmp(r.nf, text) == 0);
    free(r.nf);
    char *bad = state_text(VS, (spoil){ .elt = 2, .bit = 2, .bad = "I" });
    r = jet_run(bad, true, false);
    CHECK(r.status == AV_NORMAL && r.p2_calls == 0);
    free(r.nf);
    free(bad);
    free(thunk);
    free(text);
}

TEST(a_chain_fires_its_inner_call_only) {
    char *text = state_text(VS, (spoil){ 0 });
    size_t n = strlen(text) + 16;
    char *inner = malloc(n);
    snprintf(inner, n, "S K K (%s)", text);             /* P x, its jet node matched */
    uint32_t want[16];
    memcpy(want, VS, sizeof want);
    av_p2_permute(want);
    char *wtext = state_text(want, (spoil){ 0 });
    jetrun r = jet_run(inner, true, false);
    CHECK(r.status == AV_NORMAL && r.p2_calls == 1 && r.p2_declines == 1);
    CHECK(r.nf && strcmp(r.nf, wtext) == 0);            /* the stand-in is I */
    free(r.nf);
    free(wtext);
    free(inner);
    free(text);
}

/*  P (P x) with one P node, shared, P a stand-in with a redex of its own,
 *  I (S K K): the outer call declines and runs a fresh copy of P's term,
 *  so the node's own term is never rewritten, stays P's, and the inner
 *  call still fires. */
TEST(a_shared_node_keeps_the_jet_after_a_decline) {
    char *text = state_text(VS, (spoil){ 0 });
    av_arena *a = av_arena_new(1u << 16);
    uint32_t p = av_parse(a, "I (S K K)", 9, NULL);
    const char *err = NULL;
    uint32_t id = p2_register(a, p, false, &err);
    CHECK(id != AV_NONE);
    uint32_t x = av_parse(a, text, strlen(text), NULL);
    uint32_t q = av_parse(a, "I (S K K)", 9, NULL);
    uint32_t t = av_app(a, q, av_app(a, q, x));         /* one node, twice */
    t = av_jets_match(a, t);
    CHECK(av_res(a, av_left(a, t)) == av_res(a, av_left(a, av_right(a, t))));
    CHECK(av_p2_bind(a, t, id) == 1);
    av_opts o = av_opts_default();
    o.p2 = true;
    av_root_push(a, &t);
    av_result r = av_reduce(a, t, &o);
    av_root_pop(a);
    CHECK(r.status == AV_NORMAL);
    CHECK(r.p2_calls == 1 && r.p2_declines == 1 && r.p2_unbound == 0);
    uint32_t want[16];
    memcpy(want, VS, sizeof want);
    av_p2_permute(want);
    char *wtext = state_text(want, (spoil){ 0 });
    av_buf b = { 0 };
    CHECK(av_print(a, r.term, 10000000, &b) && strcmp(b.s, wtext) == 0);
    av_buf_free(&b);
    av_arena_free(a);
    free(wtext);
    free(text);
}

TEST(a_jet_node_over_another_term_is_unbound) {
    char *text = state_text(VS, (spoil){ 0 });
    jetrun r = jet_run(text, true, true);
    CHECK(r.kept == 0);
    CHECK(r.p2_calls == 0);
    /* S K S x reduces to x */
    CHECK(r.nf && strcmp(r.nf, text) == 0);
    free(r.nf);
    free(text);
}

TEST_MAIN(
    TEST_CASE(the_test_vectors),
    TEST_CASE(a_p2commit_statement_is_read),
    TEST_CASE(malformed_p2commit_statements_are_refused),
    TEST_CASE(inputs_permute_as_their_residues),
    TEST_CASE(a_p2pre_statement_is_read),
    TEST_CASE(malformed_p2pre_statements_are_refused),
    TEST_CASE(a_state_is_read_back),
    TEST_CASE(anything_but_a_state_is_not_read),
    TEST_CASE(the_jet_permutes_a_state_in_one_step),
    TEST_CASE(a_collection_at_the_fire_keeps_the_answer),
    TEST_CASE(any_other_argument_runs_the_term),
    TEST_CASE(a_chain_fires_its_inner_call_only),
    TEST_CASE(a_shared_node_keeps_the_jet_after_a_decline),
    TEST_CASE(a_jet_node_over_another_term_is_unbound),
)
