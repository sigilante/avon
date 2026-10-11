/**  test_front0.c
 *
 *  Reading the SKIjack-0 front end's result without the front end: results
 *  built here as Scott data and read by probing.  The probes share --fuel;
 *  a name holding a control character or a space, or longer than 65,536
 *  characters, is refused.  front0_check.sh runs the front end itself,
 *  against skijack.
 */

#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "test.h"

/*  ------------------------------------------------- Scott data, built here */

static bool has(av_arena *a, uint32_t e, uint32_t v) {
    if (e == v) return true;
    if (av_tag(a, e) != AV_APP) return false;
    return has(a, av_left(a, e), v) || has(a, av_right(a, e), v);
}

/*  [v] e, by S, K and I. */
static uint32_t abstract(av_arena *a, uint32_t v, uint32_t e) {
    if (e == v) return AV_NODE_I;
    if (!has(a, e, v)) return av_app(a, AV_NODE_K, e);
    return av_app(a, av_app(a, AV_NODE_S, abstract(a, v, av_left(a, e))),
                  abstract(a, v, av_right(a, e)));
}

static uint32_t var(av_arena *a, unsigned i) {
    char nm[8];
    int n = snprintf(nm, sizeof nm, "v%u", i);
    return av_leaf(a, nm, (size_t)n);
}

/*  Constructor i of n, with k fields: \x1..xk m0..m(n-1). m_i x1..xk. */
static uint32_t ctor(av_arena *a, unsigned n, unsigned i, unsigned k) {
    uint32_t body = var(a, k + i);
    for (unsigned j = 0; j < k; j++) body = av_app(a, body, var(a, j));
    for (unsigned j = n + k; j-- > 0;) body = abstract(a, var(a, j), body);
    return body;
}

typedef struct { uint32_t rok, onil, ocons, nnil, ncons, code, lo, hi, ts; } ctors;

static ctors make_ctors(av_arena *a) {
    return (ctors){
        .rok = ctor(a, 2, 0, 1), .onil = ctor(a, 2, 0, 0), .ocons = ctor(a, 2, 1, 3),
        .nnil = ctor(a, 2, 0, 0), .ncons = ctor(a, 2, 1, 2), .code = ctor(a, 1, 0, 7),
        .lo = ctor(a, 2, 0, 0), .hi = ctor(a, 2, 1, 0), .ts = ctor(a, 5, 0, 0),
    };
}

static uint32_t app3(av_arena *a, uint32_t f, uint32_t x, uint32_t y, uint32_t z) {
    return av_app(a, av_app(a, av_app(a, f, x), y), z);
}

/*  The name of n characters, each ch, as one shared code. */
static uint32_t name_of(av_arena *a, const ctors *c, unsigned ch, size_t n) {
    uint32_t code = c->code;
    for (int b = 6; b >= 0; b--) code = av_app(a, code, (ch >> b & 1) ? c->hi : c->lo);
    uint32_t name = c->nnil;
    for (size_t i = 0; i < n; i++) name = av_app(a, av_app(a, c->ncons, code), name);
    return name;
}

/*  ROk (OCons name TS (OCons name2 TS ONil)), the names as given. */
static uint32_t result(av_arena *a, const ctors *c, uint32_t name, uint32_t name2) {
    uint32_t outs = app3(a, c->ocons, name2, c->ts, c->onil);
    outs = app3(a, c->ocons, name, c->ts, outs);
    return av_app(a, c->rok, outs);
}

/*  Read ROk (OCons (n1 of ch1) TS (OCons (n2 of ch2) TS ONil)) in a fresh
 *  arena: a read reduces the result's shared nodes in place, so a second
 *  read in the same arena would cost less. */
static int read_names(unsigned ch1, size_t n1, unsigned ch2, size_t n2, uint64_t fuel,
                      char *out, size_t cap, uint64_t *steps, const char **err) {
    av_arena *a = av_arena_new(1u << 16);
    ctors c = make_ctors(a);
    uint32_t t = result(a, &c, name_of(a, &c, ch1, n1), name_of(a, &c, ch2, n2));
    memset(out, 0, cap);
    FILE *f = fmemopen(out, cap, "w");
    if (!f) { CHECK(f != NULL); av_arena_free(a); return -2; }
    av_opts o = av_opts_default();
    o.max_steps = fuel;
    *err = NULL;
    int rc = av_front0_read(a, t, &o, f, steps, NULL, err);
    fclose(f);
    av_arena_free(a);
    return rc;
}

/*  ------------------------------------------------------------------ cases */

TEST(a_result_reads_to_lines) {
    char out[256];
    uint64_t steps = 0;
    const char *err;
    CHECK_EQ(read_names('a', 2, 'b', 1, UINT64_MAX, out, sizeof out, &steps, &err), 0);
    CHECK(strncmp(out, "aa\t", 3) == 0);
    CHECK(strstr(out, "\nb\t") != NULL);
    CHECK(steps > 0);
}

/*  The whole read is bounded by --fuel: before, each probe had all of it,
 *  so a read of many probes ran on past it. */
TEST(the_probes_share_the_fuel) {
    char out[256];
    uint64_t all = 0, steps = 0;
    const char *err;
    CHECK_EQ(read_names('a', 20, 'b', 20, UINT64_MAX, out, sizeof out, &all, &err), 0);
    /* as for any run, fuel spent to the last step reports FUEL */
    CHECK_EQ(read_names('a', 20, 'b', 20, all + 1, out, sizeof out, &steps, &err), 0);
    CHECK_EQ(steps, all);
    CHECK_EQ(read_names('a', 20, 'b', 20, all, out, sizeof out, &steps, &err), -1);
    CHECK(err && strcmp(err, "FUEL") == 0);
    CHECK(steps <= all);
}

/*  A newline in a name would forge a line of the output. */
TEST(a_name_with_a_control_character_or_a_space_is_refused) {
    const unsigned bad[] = { '\n', '\t', ' ', 0x7f, 0 };
    for (size_t i = 0; i < sizeof bad / sizeof *bad; i++) {
        char out[256];
        uint64_t steps;
        const char *err;
        CHECK_EQ(read_names('a', 1, bad[i], 1, UINT64_MAX, out, sizeof out, &steps, &err), -1);
        CHECK(err && strstr(err, "control character"));
        CHECK(strncmp(out, "a\t", 2) == 0);                  /* the first line, and */
        CHECK(strchr(out, '\n') == strrchr(out, '\n'));     /* no other */
    }
}

TEST(a_name_past_65536_characters_is_refused) {
    size_t cap = 1u << 18;
    char *out = malloc(cap);
    REQUIRE(out != NULL);
    uint64_t steps;
    const char *err;
    CHECK_EQ(read_names('a', 65536, 'b', 1, UINT64_MAX, out, cap, &steps, &err), 0);
    CHECK_EQ(read_names('a', 65537, 'b', 1, UINT64_MAX, out, cap, &steps, &err), -1);
    CHECK(err && strstr(err, "65536"));
    free(out);
}

TEST_MAIN(
    TEST_CASE(a_result_reads_to_lines),
    TEST_CASE(the_probes_share_the_fuel),
    TEST_CASE(a_name_with_a_control_character_or_a_space_is_refused),
    TEST_CASE(a_name_past_65536_characters_is_refused),
)
