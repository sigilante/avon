/**  test.h
 *
 *  The unit-test runner: one executable per tests/test_*.c file.  Declare
 *  cases with TEST(name), list them in TEST_MAIN, and check with CHECK or
 *  CHECK_EQ.  A failed check reports its line and fails the case; the
 *  executable exits nonzero if any case failed.  REQUIRE is CHECK that
 *  also ends the case, for a precondition the rest depends on.  A case
 *  that makes no check fails, and a fixture test_open cannot open fails
 *  the suite: a missing fixture cannot pass by skipping.
 */

#ifndef TEST_H
#define TEST_H

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

static int test_failed_;
static unsigned long test_checks_;

#define TEST(name) static void name(void)

#define CHECK(cond)                                                       \
    do {                                                                  \
        test_checks_++;                                                   \
        if (!(cond)) {                                                    \
            fprintf(stderr, "  %s:%d: CHECK(%s)\n", __FILE__, __LINE__,   \
                    #cond);                                               \
            test_failed_ = 1;                                             \
        }                                                                 \
    } while (0)

#define CHECK_EQ(got, want)                                               \
    do {                                                                  \
        intmax_t g_ = (intmax_t)(got), w_ = (intmax_t)(want);             \
        test_checks_++;                                                   \
        if (g_ != w_) {                                                   \
            fprintf(stderr, "  %s:%d: %s == %jd, want %jd\n", __FILE__,   \
                    __LINE__, #got, g_, w_);                              \
            test_failed_ = 1;                                             \
        }                                                                 \
    } while (0)

#define REQUIRE(cond)                                                     \
    do {                                                                  \
        test_checks_++;                                                   \
        if (!(cond)) {                                                    \
            fprintf(stderr, "  %s:%d: REQUIRE(%s)\n", __FILE__, __LINE__, \
                    #cond);                                               \
            test_failed_ = 1;                                             \
            return;                                                       \
        }                                                                 \
    } while (0)

/*  Open a file the suite reads, or end the suite failed: a missing fixture
 *  must fail, never let a case check less. */
static inline FILE *test_open(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) {
        fprintf(stderr, "FAIL: cannot open %s\n", path);
        exit(1);
    }
    return f;
}

typedef struct { const char *name; void (*fn)(void); } test_case;

#define TEST_CASE(name) { #name, name }

#define TEST_MAIN(...)                                                    \
    int main(void) {                                                      \
        static const test_case cases[] = { __VA_ARGS__ };                 \
        size_t n = sizeof cases / sizeof cases[0], bad = 0;               \
        for (size_t i = 0; i < n; i++) {                                  \
            test_failed_ = 0;                                             \
            test_checks_ = 0;                                             \
            cases[i].fn();                                                \
            if (!test_checks_) {                                          \
                fprintf(stderr, "  %s: no checks\n", cases[i].name);     \
                test_failed_ = 1;                                         \
            }                                                             \
            if (test_failed_) {                                           \
                fprintf(stderr, "FAIL %s: %s\n", __FILE__, cases[i].name);\
                bad++;                                                    \
            }                                                             \
        }                                                                 \
        printf("%s: %zu/%zu passed\n", __FILE__, n - bad, n);             \
        return bad != 0;                                                  \
    }

#endif /* TEST_H */
