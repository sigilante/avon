/**  test_p2.c
 *
 *  Poseidon2 over BabyBear (src/p2.c): the specification's three test
 *  vectors, and inputs at or above p permuting as their residues do, as
 *  the jet's 31-bit elements may be.
 */

#include <stdint.h>
#include <string.h>

#include "avon.h"
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

TEST_MAIN(
    TEST_CASE(the_test_vectors),
    TEST_CASE(a_p2commit_statement_is_read),
    TEST_CASE(malformed_p2commit_statements_are_refused),
    TEST_CASE(inputs_permute_as_their_residues),
    TEST_CASE(a_p2pre_statement_is_read),
    TEST_CASE(malformed_p2pre_statements_are_refused),
)
