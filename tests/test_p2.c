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

TEST_MAIN(
    TEST_CASE(the_test_vectors),
    TEST_CASE(inputs_permute_as_their_residues),
    TEST_CASE(a_p2pre_statement_is_read),
    TEST_CASE(malformed_p2pre_statements_are_refused),
)
