/**  test_entropy.c
 *
 *  Entropy for kernels (docs/DESIGN.md §9.1), on tests/kernel/
 *  entropy.ascii.ski: a pier booted with --entropy answers boot's request
 *  and each [0 id] in a poke's effects list, in order, a reply's own
 *  requests too, with [0 [id bits]], bit 8i + j bit j of byte i; replay
 *  gives the same bits, and a FILE reopened draws from where it stopped;
 *  one event draws 16 replies at most; an outside event tagged 0 is
 *  refused, a tag reaching 0 past the probes' fuel too; a file that runs
 *  out leaves its event applied, the failure reported beside it; boot's
 *  reply, if a crash took it, comes with the first poke; a pier keeps to
 *  one source of bits; a collection in the event hook loses no request;
 *  and a pier booted without --entropy passes every effect through.  Run
 *  from the repository root.
 */

#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#include "avon.h"
#include "test.h"

#define DIR "tests/kernel/"

static uint8_t *slurp(const char *path, size_t *len) {
    FILE *f = test_open(path);
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *p = malloc((size_t)n + 1);
    *len = fread(p, 1, (size_t)n, f);
    fclose(f);
    return p;
}

static uint8_t *bytes_of(const char *name, size_t *len) {
    char path[256];
    snprintf(path, sizeof path, DIR "%s.skit", name);
    return slurp(path, len);
}

static av_opts share_opts(void) {
    av_opts o = av_opts_default();
    o.strategy = AV_SHARE;
    o.max_steps = 100000000;
    return o;
}

/*  Peek path NAME (entropy.pathN) of p's kernel, read as a numeral. */
static uint64_t peek(av_pier *p, const char *name) {
    av_kernel *k = av_pier_kernel(p);
    size_t n;
    uint8_t *b = bytes_of(name, &n);
    uint32_t path = b ? av_cue(k->a, b, n, NULL) : AV_NONE;
    free(b);
    uint32_t ans;
    av_result r;
    if (path == AV_NONE || av_kernel_peek(k, path, &ans, &r) != AV_WHNF) return UINT64_MAX;
    av_opts o = av_opts_default();
    o.strategy = AV_COPY;
    o.no_collect = true;
    o.max_steps = 1000000;
    uint64_t v = UINT64_MAX;
    av_root_push(k->a, &ans);
    if (!av_read_nat(k->a, ans, 100000, &o, &v, NULL)) v = UINT64_MAX;
    av_root_pop(k->a);
    return v;
}

static uint64_t replies(av_pier *p) { return av_pier_replies(p, NULL); }
static uint64_t events(av_pier *p) { return av_pier_kernel(p)->events; }

static unsigned ones(const uint8_t *b, size_t from) {
    unsigned n = 0;
    for (size_t i = from; i < from + AV_ENY_BYTES; i++) n += (unsigned)__builtin_popcount(b[i]);
    return n;
}

/*  What the kernel answers on every path: a replay must give the same.
 *  (Not its structural hash: in share mode a peek writes its thunks.) */
typedef struct { uint64_t v[4]; } answers;

static answers answers_of(av_pier *p) {
    static const char *const paths[4] = { "entropy.path0", "entropy.path1", "entropy.path2",
                                          "entropy.path3" };
    answers a;
    for (int i = 0; i < 4; i++) a.v[i] = peek(p, paths[i]);
    return a;
}

static bool same(answers x, answers y) { return memcmp(&x, &y, sizeof x) == 0; }

static void write_file(const char *path, const uint8_t *b, size_t n) {
    FILE *f = fopen(path, "wb");
    CHECK(f && fwrite(b, 1, n, f) == n);
    if (f) fclose(f);
}

static long file_size(const char *path) {
    struct stat st;
    return stat(path, &st) == 0 ? (long)st.st_size : -1;
}

/*  A fresh pier at DIR/pier from the entropy kernel's pill. */
static bool answer_boot = true;

static av_pier *boot(const char *dir, const char *eny_file, bool eny) {
    char pier[160];
    snprintf(pier, sizeof pier, "%s/pier", dir);
    size_t np;
    uint8_t *pill = bytes_of("entropy.pill", &np);
    uint8_t subject[256];
    av_arena *s = av_arena_new(0);
    av_buf sb = { 0 };
    CHECK(av_jam(s, AV_NODE_I, 16, &sb, NULL) && sb.len <= sizeof subject);
    size_t ns = sb.len;
    memcpy(subject, sb.s, ns);
    av_buf_free(&sb);
    av_arena_free(s);
    av_opts o = share_opts();
    const char *err = NULL;
    unsigned flags = (eny ? AV_PIER_ENTROPY : 0u) | (eny_file ? AV_PIER_ENTROPY_FILE : 0u);
    av_pier *p = pill ? av_pier_new_ex(pier, pill, np, subject, ns, &o, flags, &err) : NULL;
    free(pill);
    CHECK(p != NULL);
    if (p && eny && answer_boot) CHECK(av_pier_entropy(p, eny_file, &err));
    return p;
}

static av_status poke(av_pier *p, const char *name, const char **err) {
    size_t n;
    uint8_t *b = bytes_of(name, &n);
    uint32_t eff;
    av_result r;
    av_status st = b ? av_pier_poke(p, b, n, &eff, &r, err) : AV_SIZE;
    free(b);
    return st;
}

static void rm_rf(const char *dir) {
    char cmd[256];
    snprintf(cmd, sizeof cmd, "/bin/rm -rf %s", dir);
    CHECK(system(cmd) == 0);
}

/*  Boot, ask once, ask twice; replay; draw on from where the file
 *  stopped; refuse a forged reply; stop a greedy kernel at the cap. */
TEST(requests_are_answered_in_order_and_replayed) {
    char dir[] = "/tmp/avon-eny-XXXXXX";
    CHECK(mkdtemp(dir) != NULL);
    char file[160], pier[160], logp[192];
    snprintf(file, sizeof file, "%s/bytes", dir);
    snprintf(pier, sizeof pier, "%s/pier", dir);
    snprintf(logp, sizeof logp, "%s/events.log", pier);
    uint8_t b[1024];
    for (size_t i = 0; i < sizeof b; i++) b[i] = (uint8_t)(i * 37 + 11);
    write_file(file, b, sizeof b);
    const char *err = NULL;

    av_pier *p = boot(dir, file, true);
    if (!p) return;
    CHECK_EQ(replies(p), 1);                                /* boot's request */
    CHECK_EQ(events(p), 1);
    CHECK_EQ(peek(p, "entropy.path0"), 1);
    CHECK_EQ(peek(p, "entropy.path2"), 0);                  /* its id */
    CHECK_EQ(peek(p, "entropy.path1"), ones(b, 0));
    CHECK_EQ(peek(p, "entropy.path3"), b[0] & 1u);

    CHECK_EQ(poke(p, "entropy.ask5", &err), AV_WHNF);
    CHECK_EQ(replies(p), 1);
    CHECK_EQ(events(p), 3);
    CHECK_EQ(peek(p, "entropy.path2"), 5);
    CHECK_EQ(peek(p, "entropy.path1"), ones(b, 16));

    /* two requests with an ordinary effect between them: two replies, in
     * order, the second the newest */
    CHECK_EQ(poke(p, "entropy.ask7twice", &err), AV_WHNF);
    CHECK_EQ(replies(p), 2);
    CHECK_EQ(events(p), 6);
    CHECK_EQ(peek(p, "entropy.path0"), 4);
    CHECK_EQ(peek(p, "entropy.path2"), 8);
    CHECK_EQ(peek(p, "entropy.path1"), ones(b, 48));
    CHECK_EQ(peek(p, "entropy.path3"), b[48] & 1u);
    answers want = answers_of(p);
    av_pier_free(p);

    /* replay: the same kernel, from the log alone */
    av_opts o = share_opts();
    p = av_pier_open(pier, &o, &err);
    CHECK(p != NULL);
    if (!p) return;
    CHECK_EQ(events(p), 6);
    CHECK(same(answers_of(p), want));

    /* the file again: drawn from byte 64, after the four replies logged */
    CHECK(av_pier_entropy(p, file, &err));
    CHECK_EQ(poke(p, "entropy.ask5", &err), AV_WHNF);
    CHECK_EQ(peek(p, "entropy.path1"), ones(b, 64));
    CHECK_EQ(peek(p, "entropy.path3"), b[64] & 1u);

    /* a forged reply is refused, and leaves no record */
    long before = file_size(logp);
    CHECK(poke(p, "entropy.forged", &err) != AV_WHNF);
    CHECK(err && strstr(err, "tag 0") != NULL);
    CHECK_EQ(file_size(logp), before);
    CHECK_EQ(events(p), 8);

    /* a greedy kernel asks on every reply: 16 drawn, one left */
    CHECK_EQ(poke(p, "entropy.greedy", &err), AV_WHNF);
    uint64_t left = 0;
    CHECK_EQ(av_pier_replies(p, &left), AV_ENY_MAX);
    CHECK_EQ(left, 1);
    CHECK_EQ(events(p), 8 + 1 + AV_ENY_MAX);
    CHECK_EQ(peek(p, "entropy.path0"), 5 + AV_ENY_MAX);
    want = answers_of(p);
    av_pier_free(p);
    p = av_pier_open(pier, &o, &err);
    CHECK(p != NULL);
    if (p) {
        CHECK(same(answers_of(p), want));
        av_pier_free(p);
    }
    rm_rf(dir);
}

/*  Bit 8i + j of the list is bit j of byte i, least significant first. */
TEST(bits_are_least_significant_first) {
    char dir[] = "/tmp/avon-eny-XXXXXX";
    CHECK(mkdtemp(dir) != NULL);
    char file[160];
    snprintf(file, sizeof file, "%s/bytes", dir);
    uint8_t b[32] = { 0 };
    b[0] = 0x01;                        /* boot's reply: the first bit set */
    b[16] = 0x80;                       /* ask5's: bits 7 and 127 set */
    b[31] = 0x80;
    write_file(file, b, sizeof b);
    const char *err = NULL;
    av_pier *p = boot(dir, file, true);
    if (!p) return;
    CHECK_EQ(peek(p, "entropy.path3"), 1);
    CHECK_EQ(peek(p, "entropy.path1"), 1);
    CHECK_EQ(poke(p, "entropy.ask5", &err), AV_WHNF);
    CHECK_EQ(peek(p, "entropy.path3"), 0);
    CHECK_EQ(peek(p, "entropy.path1"), 2);

    /* the file is spent: the event applies, its request unanswered, and
     * the failure is reported beside it, so no caller retries it */
    CHECK_EQ(poke(p, "entropy.ask5", &err), AV_WHNF);
    CHECK_EQ(replies(p), 0);
    CHECK(av_pier_entropy_error(p) && strstr(av_pier_entropy_error(p), "run out") != NULL);
    CHECK_EQ(events(p), 4);
    av_pier_free(p);
    rm_rf(dir);
}

/*  Without --entropy the pier reads no effect: a request is just an
 *  effect, a tag 0 just an event, and entropy cannot be chosen later. */
TEST(a_pier_without_entropy_passes_effects_through) {
    char dir[] = "/tmp/avon-eny-XXXXXX";
    CHECK(mkdtemp(dir) != NULL);
    const char *err = NULL;
    av_pier *p = boot(dir, NULL, false);
    if (!p) return;
    CHECK_EQ(poke(p, "entropy.ask5", &err), AV_WHNF);
    CHECK_EQ(replies(p), 0);
    CHECK_EQ(events(p), 1);
    CHECK_EQ(peek(p, "entropy.path0"), 0);
    CHECK_EQ(poke(p, "entropy.forged", &err), AV_WHNF);
    CHECK_EQ(peek(p, "entropy.path0"), 1);                  /* the kernel took it */
    CHECK(!av_pier_entropy(p, NULL, &err));                 /* not booted with it */
    av_pier_free(p);
    rm_rf(dir);
}

/*  Outside events the kernel might read as replies are refused: a tag
 *  that reaches 0 only after more steps than a probe takes (the share-mode
 *  kernel would reach it), and anything not shown a cell with a nonzero
 *  tag. */
TEST(a_forgery_past_the_probes_fuel_is_refused) {
    char dir[] = "/tmp/avon-eny-XXXXXX";
    CHECK(mkdtemp(dir) != NULL);
    const char *err = NULL;
    av_pier *p = boot(dir, NULL, true);
    if (!p) return;
    CHECK(poke(p, "entropy.slowzero", &err) != AV_WHNF);
    CHECK(poke(p, "entropy.notacell", &err) != AV_WHNF);
    CHECK_EQ(events(p), 1);
    CHECK_EQ(peek(p, "entropy.path0"), 1);
    av_pier_free(p);
    rm_rf(dir);
}

/*  A crash after the opt-in, before boot's reply: the first poke answers
 *  boot's request first. */
TEST(boots_reply_survives_a_crash) {
    char dir[] = "/tmp/avon-eny-XXXXXX";
    CHECK(mkdtemp(dir) != NULL);
    char pier[160];
    snprintf(pier, sizeof pier, "%s/pier", dir);
    const char *err = NULL;
    answer_boot = false;
    av_pier *p = boot(dir, NULL, true);
    answer_boot = true;
    if (!p) return;
    CHECK_EQ(events(p), 0);
    av_pier_free(p);                                        /* the crash */
    av_opts o = share_opts();
    p = av_pier_open(pier, &o, &err);
    CHECK(p != NULL);
    if (!p) return;
    CHECK_EQ(poke(p, "entropy.ask5", &err), AV_WHNF);
    CHECK_EQ(replies(p), 2);                                /* boot's, then ask5's */
    CHECK_EQ(events(p), 3);
    CHECK_EQ(peek(p, "entropy.path0"), 2);
    CHECK_EQ(peek(p, "entropy.path2"), 5);
    av_pier_free(p);
    rm_rf(dir);
}

/*  A file pier never draws from getentropy, nor the reverse. */
TEST(a_pier_keeps_one_source) {
    char dir[] = "/tmp/avon-eny-XXXXXX";
    CHECK(mkdtemp(dir) != NULL);
    char file[160], pier[160];
    snprintf(file, sizeof file, "%s/bytes", dir);
    snprintf(pier, sizeof pier, "%s/pier", dir);
    uint8_t b[64] = { 0 };
    write_file(file, b, sizeof b);
    const char *err = NULL;
    av_pier *p = boot(dir, file, true);
    if (!p) return;
    av_pier_free(p);
    av_opts o = share_opts();
    p = av_pier_open(pier, &o, &err);
    CHECK(p != NULL);
    if (!p) return;
    CHECK(poke(p, "entropy.ask5", &err) != AV_WHNF);        /* no file given */
    CHECK(err && strstr(err, "from a file") != NULL);
    CHECK_EQ(events(p), 1);
    av_pier_free(p);
    rm_rf(dir);

    char dir2[] = "/tmp/avon-eny-XXXXXX";
    CHECK(mkdtemp(dir2) != NULL);
    p = boot(dir2, NULL, true);
    if (!p) return;
    CHECK(!av_pier_entropy(p, file, &err));                 /* a getentropy pier */
    av_pier_free(p);
    rm_rf(dir2);
}

/*  The event hook may reduce, and so collect: the effects it was given
 *  must still be read afterwards. */
static void collect_hook(void *ctx, uint64_t event, uint64_t steps, uint32_t effects, bool reply) {
    (void)event; (void)steps; (void)effects;
    if (!reply) CHECK(av_collect(av_pier_kernel(ctx)->a, 0, NULL, NULL, NULL));
}

TEST(a_collection_in_the_hook_loses_no_request) {
    char dir[] = "/tmp/avon-eny-XXXXXX";
    CHECK(mkdtemp(dir) != NULL);
    const char *err = NULL;
    av_pier *p = boot(dir, NULL, true);
    if (!p) return;
    av_pier_on_event(p, collect_hook, p);
    CHECK_EQ(poke(p, "entropy.ask7twice", &err), AV_WHNF);
    CHECK_EQ(replies(p), 2);
    CHECK_EQ(peek(p, "entropy.path2"), 8);
    av_pier_free(p);
    rm_rf(dir);
}

TEST_MAIN(
    TEST_CASE(requests_are_answered_in_order_and_replayed),
    TEST_CASE(bits_are_least_significant_first),
    TEST_CASE(a_pier_without_entropy_passes_effects_through),
    TEST_CASE(a_forgery_past_the_probes_fuel_is_refused),
    TEST_CASE(boots_reply_survives_a_crash),
    TEST_CASE(a_pier_keeps_one_source),
    TEST_CASE(a_collection_in_the_hook_loses_no_request),
)
