/**  test_front0.c
 *
 *  Reading the SKIjack-0 front end's result without the front end: results
 *  built here as Scott data and read by probing.  The probes share --fuel;
 *  a name holding a control character or a space, or longer than 65,536
 *  characters, is refused.  A refusal reads as `RErr`, or with its class,
 *  a numeral, as `RErr n`.  front1's ROk carries its templates too, read
 *  only by --emit, which writes them as the loader reads them; unread, they
 *  are never made.  front0_check.sh runs the front end itself, against
 *  skijack.
 */

#include <stdlib.h>
#include <string.h>
#include <unistd.h>

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

typedef struct { uint32_t rok, onil, ocons, nnil, ncons, code, lo, hi, ts, rerr0, rerr1, rerr2,
                         zero, suc; } ctors;

static ctors make_ctors(av_arena *a) {
    return (ctors){
        .rok = ctor(a, 2, 0, 1), .onil = ctor(a, 2, 0, 0), .ocons = ctor(a, 2, 1, 3),
        .nnil = ctor(a, 2, 0, 0), .ncons = ctor(a, 2, 1, 2), .code = ctor(a, 1, 0, 7),
        .lo = ctor(a, 2, 0, 0), .hi = ctor(a, 2, 1, 0), .ts = ctor(a, 5, 0, 0),
        .rerr0 = ctor(a, 2, 1, 0), .rerr1 = ctor(a, 2, 1, 1), .rerr2 = ctor(a, 2, 1, 2),
        .zero = ctor(a, 2, 0, 0), .suc = ctor(a, 2, 1, 1),
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

/*  Read a refusal: RErr with no field (fields 0), with the numeral n
 *  (fields 1), or with two fields, each the numeral n (fields 2). */
static int read_refusal(unsigned fields, unsigned n, char *out, size_t cap, const char **err) {
    av_arena *a = av_arena_new(1u << 16);
    ctors c = make_ctors(a);
    uint32_t num = c.zero;
    for (unsigned i = 0; i < n; i++) num = av_app(a, c.suc, num);
    uint32_t t = fields == 0 ? c.rerr0
               : fields == 1 ? av_app(a, c.rerr1, num)
               : av_app(a, av_app(a, c.rerr2, num), num);
    memset(out, 0, cap);
    FILE *f = fmemopen(out, cap, "w");
    if (!f) { CHECK(f != NULL); av_arena_free(a); return -2; }
    av_opts o = av_opts_default();
    uint64_t steps;
    *err = NULL;
    int rc = av_front0_read(a, t, &o, f, &steps, NULL, err);
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

/*  SKIjack-0's refusal carries no class and reads as before; the full
 *  language's carries its class, a numeral, printed after it. */
TEST(a_refusal_reads_with_its_class_if_it_has_one) {
    char out[64];
    const char *err;
    CHECK_EQ(read_refusal(0, 0, out, sizeof out, &err), 1);
    CHECK(strcmp(out, "RErr\n") == 0);
    CHECK_EQ(read_refusal(1, 0, out, sizeof out, &err), 1);
    CHECK(strcmp(out, "RErr 0\n") == 0);
    CHECK_EQ(read_refusal(1, 6, out, sizeof out, &err), 1);
    CHECK(strcmp(out, "RErr 6\n") == 0);
    CHECK_EQ(read_refusal(1, 255, out, sizeof out, &err), 1);
    CHECK(strcmp(out, "RErr 255\n") == 0);
    CHECK_EQ(read_refusal(1, 256, out, sizeof out, &err), -1);
    CHECK(err && strstr(err, "past 255"));
    CHECK_EQ(read_refusal(2, 1, out, sizeof out, &err), -1);
    CHECK(err && strstr(err, "wrong number of fields"));
    CHECK(out[0] == '\0');
}

/*  ------------------------------------------------------- templates */

/*  front1's ROk outs tpls: B (named B, its term S (K S) K) and two
 *  templates, B's, f g x to f (g x), and S K I's, x to K x x with K a
 *  reference (TV 1, past the one formal).  tpls_field replaces the
 *  templates when not AV_NONE. */
static uint32_t rok_tpls(av_arena *a, uint32_t tpls_field) {
    uint32_t ts = ctor(a, 5, 0, 0), tk = ctor(a, 5, 1, 0), ti = ctor(a, 5, 2, 0);
    uint32_t tv = ctor(a, 5, 3, 1), ta = ctor(a, 5, 4, 1), ap = ctor(a, 1, 0, 2);
    uint32_t zero = ctor(a, 2, 0, 0), suc = ctor(a, 2, 1, 1);
    uint32_t tmnil = ctor(a, 2, 0, 0), tmcons = ctor(a, 2, 1, 2);
    uint32_t tpnil = ctor(a, 2, 0, 0), tpcons = ctor(a, 2, 1, 2), tpl = ctor(a, 1, 0, 4);
    uint32_t onil = ctor(a, 2, 0, 0), ocons = ctor(a, 2, 1, 3), rok = ctor(a, 2, 0, 2);
#define APP(e, f) av_app(a, ta, av_app(a, av_app(a, ap, (e)), (f)))
    uint32_t one = av_app(a, suc, zero), two = av_app(a, suc, one), three = av_app(a, suc, two);
    uint32_t bkey = APP(APP(ts, APP(tk, ts)), tk);
    uint32_t bbody = APP(av_app(a, tv, zero), APP(av_app(a, tv, one), av_app(a, tv, two)));
    uint32_t wkey = APP(APP(ts, tk), ti);
    uint32_t wbody = APP(APP(av_app(a, tv, one), av_app(a, tv, zero)), av_app(a, tv, zero));
#undef APP
    ctors c = make_ctors(a);
    uint32_t outs = app3(a, ocons, name_of(a, &c, 'B', 1), bkey, onil);
    uint32_t t1 = av_app(a, av_app(a, av_app(a, av_app(a, tpl, bkey), three), bbody), tmnil);
    uint32_t t2 = av_app(a, av_app(a, av_app(a, av_app(a, tpl, wkey), one), wbody),
                         av_app(a, av_app(a, tmcons, tk), tmnil));
    uint32_t tpls = av_app(a, av_app(a, tpcons, t1), av_app(a, av_app(a, tpcons, t2), tpnil));
    return av_app(a, av_app(a, rok, outs), tpls_field != AV_NONE ? tpls_field : tpls);
}

static char *slurp_file(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    static char buf[4096];
    size_t n = fread(buf, 1, sizeof buf - 1, f);
    fclose(f);
    buf[n] = '\0';
    return buf;
}

/*  --emit writes the templates as the loader reads them, each key and
 *  reference once, and every name's term; loaded, B's fires in one step. */
TEST(emitted_templates_load_and_fire) {
    char dir[64] = "/tmp/avon-emit-XXXXXX";
    REQUIRE(mkdtemp(dir) != NULL);
    av_arena *a = av_arena_new(1u << 16);
    uint32_t t = rok_tpls(a, AV_NONE);
    char out[256] = { 0 };
    FILE *f = fmemopen(out, sizeof out, "w");
    REQUIRE(f != NULL);
    av_opts o = av_opts_default();
    uint64_t steps;
    long n = 0;
    const char *err = NULL;
    CHECK_EQ(av_front0_read_emit(a, t, &o, f, dir, &n, &steps, NULL, &err), 0);
    fclose(f);
    av_arena_free(a);
    CHECK_EQ(n, 2);
    CHECK(strncmp(out, "B\tskijack-2:", 12) == 0);
    char path[128];
    snprintf(path, sizeof path, "%s/templates.tsv", dir);
    const char *tt = slurp_file(path);
    REQUIRE(tt != NULL);
    CHECK(strstr(tt, "\tfront1\t-\t3\t0,1,2\t`v0 `v1 v2\n") != NULL);
    CHECK(strstr(tt, "\tfront1\t-\t1\t0\t``#86be9a55762d316a3026c2836d044f5f v0 v0\n") != NULL);
    snprintf(path, sizeof path, "%s/template_terms.tsv", dir);
    const char *rt = slurp_file(path);
    REQUIRE(rt != NULL);
    CHECK(strcmp(rt, "skijack-2:86be9a55762d316a3026c2836d044f5f\t1\tdag 0=K @0\n") == 0);
    snprintf(path, sizeof path, "%s/terms.tsv", dir);
    const char *nt = slurp_file(path);
    REQUIRE(nt != NULL);
    CHECK(strstr(nt, "\tdag 0=S 1=K 2=1.0 3=0.2 4=3.1 @4\n") != NULL);
    /* loaded: both kept, and B f g x is one instance */
    a = av_arena_new(1u << 12);
    const char *src = "S (K S) K f g x";
    uint32_t p = av_parse(a, src, strlen(src), NULL);
    av_tmplset *ts = av_templates_load(a, dir, &err);
    REQUIRE(ts != NULL);
    p = av_jets_match(a, p);
    CHECK(av_templates_bind(a, ts, p));
    long acc, ref, skip, unb;
    av_templates_counts(ts, &acc, &ref, &skip, &unb);
    CHECK_EQ(acc, 2);
    CHECK_EQ(ref, 0);
    av_templates_free(ts);
    av_opts so = av_opts_default();
    so.templates = true;
    av_root_push(a, &p);
    av_result r = av_reduce(a, p, &so);
    av_root_pop(a);
    CHECK_EQ(r.status, AV_NORMAL);
    CHECK_EQ(r.steps, 1);
    av_arena_free(a);
    static const char *const fns[3] = { "templates.tsv", "template_terms.tsv", "terms.tsv" };
    for (int i = 0; i < 3; i++) {
        snprintf(path, sizeof path, "%s/%s", dir, fns[i]);
        unlink(path);
    }
    rmdir(dir);
}

/*  Without --emit the templates are never read, so never made: a field
 *  that diverges, S I I (S I I), reads as before.  A one-field ROk, as
 *  SKIjack-0's front end gives, has none to emit. */
TEST(templates_unread_are_never_made) {
    av_arena *a = av_arena_new(1u << 16);
    const char *om = "S I I (S I I)";
    uint32_t omega = av_parse(a, om, strlen(om), NULL);
    uint32_t t = rok_tpls(a, omega);
    char out[256] = { 0 };
    FILE *f = fmemopen(out, sizeof out, "w");
    REQUIRE(f != NULL);
    av_opts o = av_opts_default();
    o.max_steps = 100000;
    uint64_t steps;
    const char *err = NULL;
    CHECK_EQ(av_front0_read(a, t, &o, f, &steps, NULL, &err), 0);
    fclose(f);
    av_arena_free(a);
    CHECK(strncmp(out, "B\tskijack-2:", 12) == 0);
    char dir[64] = "/tmp/avon-emit-XXXXXX";
    REQUIRE(mkdtemp(dir) != NULL);
    a = av_arena_new(1u << 16);
    ctors c = make_ctors(a);
    t = result(a, &c, name_of(a, &c, 'a', 1), name_of(a, &c, 'b', 1));
    f = fmemopen(out, sizeof out, "w");
    REQUIRE(f != NULL);
    err = NULL;
    CHECK_EQ(av_front0_read_emit(a, t, &o, f, dir, NULL, &steps, NULL, &err), -1);
    CHECK(err && strstr(err, "no templates") != NULL);
    fclose(f);
    av_arena_free(a);
    char path[128];
    static const char *const fns[3] = { "templates.tsv", "template_terms.tsv", "terms.tsv" };
    for (int i = 0; i < 3; i++) {
        snprintf(path, sizeof path, "%s/%s", dir, fns[i]);
        unlink(path);
    }
    rmdir(dir);
}

TEST_MAIN(
    TEST_CASE(a_result_reads_to_lines),
    TEST_CASE(the_probes_share_the_fuel),
    TEST_CASE(a_name_with_a_control_character_or_a_space_is_refused),
    TEST_CASE(a_name_past_65536_characters_is_refused),
    TEST_CASE(a_refusal_reads_with_its_class_if_it_has_one),
    TEST_CASE(emitted_templates_load_and_fire),
    TEST_CASE(templates_unread_are_never_made),
)
