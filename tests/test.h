/**  test.h
 *
 *  The unit-test runner: one executable per tests/test_*.c file.  Declare
 *  cases with TEST(name), list them in TEST_MAIN, and check with CHECK or
 *  CHECK_EQ.  A failed check reports its line and fails the case; the
 *  executable exits nonzero if any case failed.  REQUIRE is CHECK that
 *  also ends the case, for a precondition the rest depends on.
 */

#ifndef TEST_H
#define TEST_H

#include <inttypes.h>
#include <stdio.h>

static int test_failed_;

#define TEST(name) static void name(void)

#define CHECK(cond)                                                       \
    do {                                                                  \
        if (!(cond)) {                                                    \
            fprintf(stderr, "  %s:%d: CHECK(%s)\n", __FILE__, __LINE__,   \
                    #cond);                                               \
            test_failed_ = 1;                                             \
        }                                                                 \
    } while (0)

#define CHECK_EQ(got, want)                                               \
    do {                                                                  \
        intmax_t g_ = (intmax_t)(got), w_ = (intmax_t)(want);             \
        if (g_ != w_) {                                                   \
            fprintf(stderr, "  %s:%d: %s == %jd, want %jd\n", __FILE__,   \
                    __LINE__, #got, g_, w_);                              \
            test_failed_ = 1;                                             \
        }                                                                 \
    } while (0)

#define REQUIRE(cond)                                                     \
    do {                                                                  \
        if (!(cond)) {                                                    \
            fprintf(stderr, "  %s:%d: REQUIRE(%s)\n", __FILE__, __LINE__, \
                    #cond);                                               \
            test_failed_ = 1;                                             \
            return;                                                       \
        }                                                                 \
    } while (0)

typedef struct { const char *name; void (*fn)(void); } test_case;

#define TEST_CASE(name) { #name, name }

#define TEST_MAIN(...)                                                    \
    int main(void) {                                                      \
        static const test_case cases[] = { __VA_ARGS__ };                 \
        size_t n = sizeof cases / sizeof cases[0], bad = 0;               \
        for (size_t i = 0; i < n; i++) {                                  \
            test_failed_ = 0;                                             \
            cases[i].fn();                                                \
            if (test_failed_) {                                           \
                fprintf(stderr, "FAIL %s: %s\n", __FILE__, cases[i].name);\
                bad++;                                                    \
            }                                                             \
        }                                                                 \
        printf("%s: %zu/%zu passed\n", __FILE__, n - bad, n);             \
        return bad != 0;                                                  \
    }

#endif /* TEST_H */
