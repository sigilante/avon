/**  test_pma.c
 *
 *  Stage 9's acceptance (docs/DESIGN.md §19.1): a persistent arena
 *  reopens to the bytes it committed -- after in-place share-mode updates
 *  and after collections, which only dirty tracking carries -- without
 *  reading its nodes; a commit writes the chunks an event changed; a
 *  crash at each point of a commit reopens to the state before it or
 *  after it, and a damaged journal is refused before it is applied; a pier on it replays the rest of its log; an arena with jets
 *  is refused, and a damaged image fails its check.
 */

#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

#include "avon.h"
#include "test.h"

static char *tmpdir(void) {
    char *d = strdup("/tmp/avon-pma-XXXXXX");
    CHECK(mkdtemp(d) != NULL);
    return d;
}

static void rmrf(const char *d) {
    char cmd[256];
    snprintf(cmd, sizeof cmd, "/bin/rm -rf %s", d);
    CHECK(system(cmd) == 0);
}

static char *printed(av_arena *a, uint32_t t) {
    av_buf b = { 0 };
    CHECK(av_print(a, t, 100000000, &b));
    return b.s;
}

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec / 1e9;
}

/*  Church 2^2^2 applied to I and an atom: share mode rewrites nodes in
 *  place all through it. */
static uint32_t work(av_arena *a, unsigned k) {
    char src[256];
    snprintf(src, sizeof src, "(S (K (S I I)) (S (S (K S) K) (K (S I I)))) (K (S (K X) (S I I)))%s",
             k ? "" : "");
    uint32_t t = av_leaf(a, "X", 1);
    const char *two = "S (S (K S) K) I";
    uint32_t c2 = av_parse(a, two, strlen(two), NULL);
    for (unsigned i = 0; i < k; i++) t = av_app(a, av_app(a, c2, av_leaf(a, "F", 1)), t);
    (void)src;
    return t;
}

TEST(an_image_reopens_to_what_was_committed) {
    char *d = tmpdir();
    char img[128];
    snprintf(img, sizeof img, "%s/img", d);
    av_arena *a = av_arena_new(64);
    const char *src = "S (K Foo) (S I I) Bar";
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    const char *err = NULL;
    CHECK(av_pma_attach(a, img, &err));
    CHECK(!av_pma_attach(a, img, &err));                   /* one image */
    CHECK(av_pma_commit(a, t, 7, &err));
    uint32_t used = a->used;
    av_arena_free(a);

    uint32_t root;
    uint64_t events;
    a = av_pma_open(img, &root, &events, &err);
    CHECK(a != NULL);
    if (a) {
        CHECK_EQ(events, 7);
        CHECK_EQ(a->used, used);
        char *s = printed(a, root);
        CHECK(strcmp(s, src) == 0);
        free(s);
        CHECK(av_pma_verify(a, root, &err));
        uint32_t r2;
        uint64_t e2;
        CHECK(av_pma_open(img, &r2, &e2, &err) == NULL);    /* one process at a time */
        CHECK(err && strstr(err, "in use"));
        /* leaves intern as before: Foo is the same node */
        CHECK_EQ(av_leaf(a, "Foo", 3), av_right(a, av_right(a, av_left(a, av_left(a, root)))));
        av_arena_free(a);
    }
    rmrf(d);
    free(d);
}

/*  The image as committed equals the arena, byte for byte: read from the
 *  file, since the image is locked while the arena holds it. */
static void image_matches(av_arena *a, const char *img, uint32_t t, uint64_t events) {
    char np[160];
    snprintf(np, sizeof np, "%s/nodes", img);
    FILE *f = fopen(np, "rb");
    CHECK(f != NULL);
    if (!f) return;
    long hdr = sysconf(_SC_PAGESIZE);
    uint8_t h[40];
    CHECK(fread(h, 1, sizeof h, f) == sizeof h);
    uint32_t used = (uint32_t)h[16] | (uint32_t)h[17] << 8 | (uint32_t)h[18] << 16 | (uint32_t)h[19] << 24;
    uint32_t root = (uint32_t)h[24] | (uint32_t)h[25] << 8 | (uint32_t)h[26] << 16 | (uint32_t)h[27] << 24;
    uint64_t ev = 0;
    for (int i = 7; i >= 0; i--) ev = ev << 8 | h[28 + i];
    CHECK_EQ(used, a->used);
    CHECK_EQ(root, t);
    CHECK_EQ(ev, events);
    size_t n = (size_t)a->used * sizeof(av_node);
    uint8_t *img_nodes = malloc(n);
    fseek(f, hdr, SEEK_SET);
    CHECK(fread(img_nodes, 1, n, f) == n);
    fclose(f);
    CHECK(memcmp(img_nodes, a->nodes, n) == 0);
    free(img_nodes);
}

/*  In-place writes -- share mode rewriting committed nodes -- with no
 *  collection to mark everything, then with collections: after each
 *  commit the image is the arena, byte for byte. */
TEST(dirty_tracking_carries_every_write) {
    char *d = tmpdir();
    char img[128];
    snprintf(img, sizeof img, "%s/img", d);
    av_arena *a = av_arena_new(64);
    const char *err = NULL;
    CHECK(av_pma_attach(a, img, &err));
    /* four parts, each 2 2 2 2 I X: I applied 65,536 times, under a root
     * committed before any is reduced */
    const char *c2 = "S (S (K S) K) I";
    uint32_t part[4], root = av_leaf(a, "Q", 1);
    for (int i = 0; i < 4; i++) {
        uint32_t two = av_parse(a, c2, strlen(c2), NULL);
        uint32_t t = av_app(a, av_app(a, av_app(a, two, two), two), two);
        part[i] = av_app(a, av_app(a, t, AV_NODE_I), av_leaf(a, "X", 1));
        root = av_app(a, root, part[i]);
    }
    av_root_push(a, &root);
    CHECK(av_pma_commit(a, root, 0, &err));
    for (int round = 1; round <= 4; round++) {
        uint32_t t = root;                                  /* part round - 1 */
        for (int i = 4; i > round; i--) t = av_left(a, t);
        t = av_right(a, t);
        av_opts o = av_opts_default();
        o.strategy = AV_SHARE;                              /* writes in place */
        o.no_collect = round <= 2;                          /* rounds 1, 2: tracking alone */
        uint64_t c0 = a->collections;
        av_result r = av_reduce(a, t, &o);
        CHECK_EQ(r.status, AV_NORMAL);
        av_app(a, root, av_leaf(a, "Y", 1));                /* and new nodes */
        if (round >= 3) CHECK(av_collect(a, 0, NULL, NULL, NULL));
        if (round <= 2) CHECK_EQ(a->collections, c0);
        CHECK(av_pma_commit(a, root, (uint64_t)round, &err));
        image_matches(a, img, root, (uint64_t)round);
        if (round == 1)
            printf("  round 1, no collection: %llu contractions in place, %llu chunks committed\n",
                   (unsigned long long)r.steps, (unsigned long long)av_pma_last_chunks(a));
    }
    char *want = printed(a, root);
    CHECK(strcmp(want, "Q X X X X") == 0);                  /* every part reduced */
    av_root_pop(a);
    av_arena_free(a);
    uint32_t r0;
    uint64_t events;
    a = av_pma_open(img, &r0, &events, &err);
    CHECK(a != NULL);
    if (a) {
        char *got = printed(a, r0);
        CHECK(strcmp(got, want) == 0);
        free(got);
        av_arena_free(a);
    }
    free(want);
    rmrf(d);
    free(d);
}

/*  A small change to a big arena writes a few chunks, and a reopen does
 *  not read the nodes: it is far faster than loading a snapshot. */
TEST(a_commit_writes_what_changed_and_an_open_reads_nothing) {
    char *d = tmpdir();
    char img[128], snap[128];
    snprintf(img, sizeof img, "%s/img", d);
    snprintf(snap, sizeof snap, "%s/snap", d);
    av_arena *a = av_arena_new(1u << 20);
    uint32_t t = av_leaf(a, "Z", 1);
    for (unsigned i = 0; i < 4000000; i++)                  /* 32 MB of nodes */
        t = av_app(a, i % 3 ? AV_NODE_K : AV_NODE_S, t);
    av_root_push(a, &t);
    const char *err = NULL;
    CHECK(av_pma_attach(a, img, &err));
    CHECK(av_pma_commit(a, t, 0, &err));
    uint64_t all = av_pma_last_chunks(a);
    uint32_t u = av_app(a, t, AV_NODE_I);                   /* an event's worth */
    CHECK(av_pma_commit(a, u, 1, &err));
    uint64_t one = av_pma_last_chunks(a), bytes = av_pma_last_bytes(a);
    printf("  first commit %llu chunks; the next, one node later, %llu chunk(s), %llu bytes\n",
           (unsigned long long)all, (unsigned long long)one, (unsigned long long)bytes);
    CHECK(all > 7000);
    CHECK(one <= 2);
    CHECK(av_snapshot_save(a, u, snap, &err));
    av_root_pop(a);
    av_arena_free(a);

    uint32_t root;
    uint64_t events;
    double t0 = now();
    a = av_pma_open(img, &root, &events, &err);
    double t1 = now();
    CHECK(a != NULL);
    uint32_t sroot;
    double t2 = now();
    av_arena *s = av_snapshot_load(snap, &sroot, &err);
    double t3 = now();
    CHECK(s != NULL);
    printf("  reopen %.3f ms; the same state from a snapshot %.3f ms\n",
           (t1 - t0) * 1e3, (t3 - t2) * 1e3);
    CHECK(t1 - t0 < (t3 - t2) / 10);
    if (a) {
        CHECK_EQ(root, u);
        av_arena_free(a);
    }
    av_arena_free(s);
    rmrf(d);
    free(d);
}

/*  A crash at each point of a commit: before the journal's rename the
 *  image is the old state; from the rename on, opening completes it. */
TEST(a_crash_mid_commit_reopens_whole) {
    for (int point = 1; point <= 4; point++) {
        char *d = tmpdir();
        char img[128];
        snprintf(img, sizeof img, "%s/img", d);
        av_arena *a = av_arena_new(64);
        uint32_t t = work(a, 4);
        av_root_push(a, &t);
        const char *err = NULL;
        CHECK(av_pma_attach(a, img, &err));
        CHECK(av_pma_commit(a, t, 0, &err));
        char *old = printed(a, t);
        pid_t pid = fork();
        if (pid == 0) {                                     /* the child crashes */
            av_opts o = av_opts_default();
            o.strategy = AV_SHARE;
            av_result r = av_reduce(a, t, &o);
            av_pma_crash_at = point;
            av_pma_commit(a, r.term, 1, &err);
            _exit(0);                                       /* not reached */
        }
        int status = 0;
        waitpid(pid, &status, 0);
        CHECK(WIFEXITED(status) && WEXITSTATUS(status) == 77);
        av_opts o = av_opts_default();                      /* the new state, here */
        o.strategy = AV_SHARE;
        av_result r = av_reduce(a, t, &o);
        char *fresh = printed(a, r.term);
        av_root_pop(a);
        av_arena_free(a);

        uint32_t root;
        uint64_t events;
        a = av_pma_open(img, &root, &events, &err);
        CHECK(a != NULL);
        if (a) {
            char *got = printed(a, root);
            CHECK(av_pma_verify(a, root, &err));
            if (point == 1) CHECK(events == 0 && strcmp(got, old) == 0);
            else CHECK(events == 1 && strcmp(got, fresh) == 0);
            free(got);
            av_arena_free(a);
        }
        char jp[160];
        snprintf(jp, sizeof jp, "%s/journal", img);
        CHECK(access(jp, F_OK) != 0);                       /* recovered and removed */
        snprintf(jp, sizeof jp, "%s/journal.tmp", img);
        CHECK(access(jp, F_OK) != 0);
        free(old);
        free(fresh);
        rmrf(d);
        free(d);
    }
}

static uint8_t *slurp(const char *path, size_t *len) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *p = malloc((size_t)n + 1);
    *len = fread(p, 1, (size_t)n, f);
    fclose(f);
    return p;
}

static void spit(const char *path, const uint8_t *b, size_t n) {
    FILE *f = fopen(path, "wb");
    REQUIRE(f != NULL);
    CHECK(fwrite(b, 1, n, f) == n);
    fclose(f);
}

/*  A journal of many blocks, left by a crash after its rename: open
 *  refuses it with a byte changed or with its end cut off, leaving it in
 *  place, and applies it whole once it is restored. */
TEST(a_journal_of_many_blocks_is_checked_then_applied) {
    char *d = tmpdir();
    char img[128], jp[160];
    snprintf(img, sizeof img, "%s/img", d);
    snprintf(jp, sizeof jp, "%s/journal", img);
    av_arena *a = av_arena_new(1u << 18);
    uint32_t t = av_leaf(a, "Z", 1);
    av_root_push(a, &t);
    const char *err = NULL;
    CHECK(av_pma_attach(a, img, &err));
    CHECK(av_pma_commit(a, t, 0, &err));
    pid_t pid = fork();
    if (pid == 0) {
        for (unsigned i = 0; i < 100000; i++) t = av_app(a, i % 3 ? AV_NODE_K : AV_NODE_S, t);
        av_pma_crash_at = 2;
        av_pma_commit(a, t, 1, &err);
        _exit(0);                                           /* not reached */
    }
    int status = 0;
    waitpid(pid, &status, 0);
    CHECK(WIFEXITED(status) && WEXITSTATUS(status) == 77);
    for (unsigned i = 0; i < 100000; i++) t = av_app(a, i % 3 ? AV_NODE_K : AV_NODE_S, t);
    char *want = printed(a, t);
    av_root_pop(a);
    av_arena_free(a);

    size_t n;
    uint8_t *j = slurp(jp, &n);
    REQUIRE(j != NULL);
    CHECK(n > 10 * 65536);                                 /* 800 KB of nodes */
    uint32_t root;
    uint64_t events;
    j[n / 2] ^= 1;                                          /* one byte changed */
    spit(jp, j, n);
    a = av_pma_open(img, &root, &events, &err);
    CHECK(a == NULL && err && strstr(err, "verify"));
    CHECK(access(jp, F_OK) == 0);
    j[n / 2] ^= 1;
    spit(jp, j, n - 1000);                                  /* its end cut off */
    err = NULL;
    a = av_pma_open(img, &root, &events, &err);
    CHECK(a == NULL && err && strstr(err, "verify"));
    spit(jp, j, n);                                         /* whole again */
    a = av_pma_open(img, &root, &events, &err);
    REQUIRE(a != NULL);
    CHECK_EQ(events, 1);
    CHECK(av_pma_verify(a, root, &err));
    char *got = printed(a, root);
    CHECK(strcmp(got, want) == 0);
    CHECK(access(jp, F_OK) != 0);
    free(got);
    free(want);
    free(j);
    av_arena_free(a);
    rmrf(d);
    free(d);
}

TEST(jets_and_damage_are_refused) {
    char *d = tmpdir();
    char img[128];
    snprintf(img, sizeof img, "%s/img", d);
    av_arena *a = av_arena_new(64);
    const char *src = "S (S (K S) (S (K K) (S (K S) (S (K (S I)) K)))) (K K)";
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    const char *err = NULL;
    CHECK(av_pma_attach(a, img, &err));
    CHECK(av_pma_commit(a, t, 0, &err));
    CHECK(av_jet_register(a, t, 0, 1000, &err) != AV_NONE);
    CHECK(!av_pma_commit(a, t, 1, &err));
    CHECK(err && strstr(err, "jets"));
    av_arena_free(a);

    /* a node pointing past the image: opening is cheap and does not see
     * it; the check does */
    char np[160];
    snprintf(np, sizeof np, "%s/nodes", img);
    FILE *f = fopen(np, "r+b");
    CHECK(f != NULL);
    long hdr = sysconf(_SC_PAGESIZE);
    fseek(f, hdr + 8 * 5, SEEK_SET);                        /* node 5's left */
    uint32_t bad = 0x0fffffff;
    fwrite(&bad, 4, 1, f);
    fclose(f);
    uint32_t root;
    uint64_t events;
    a = av_pma_open(img, &root, &events, &err);
    CHECK(a != NULL);
    if (a) {
        CHECK(!av_pma_verify(a, root, &err));
        av_arena_free(a);
    }
    /* a damaged header is refused at open */
    f = fopen(np, "r+b");
    fseek(f, 20, SEEK_SET);
    fputc(0x7f, f);
    fclose(f);
    CHECK(av_pma_open(img, &root, &events, &err) == NULL);
    rmrf(d);
    free(d);
}

/*  ------------------------------------------------------ the pier on it */

static uint64_t state(av_pier *p) {
    av_kernel *k = av_pier_kernel(p);
    av_opts o = av_opts_default();
    o.strategy = AV_COPY;
    o.no_collect = true;
    uint64_t n = UINT64_MAX;
    CHECK(av_read_nat(k->a, av_kernel_state(k), 100000, &o, &n, NULL));
    return n;
}

TEST(a_pier_on_the_arena_commits_every_event) {
    char *d = tmpdir();
    char pier[128];
    snprintf(pier, sizeof pier, "%s/pier", d);
    size_t np, nt;
    uint8_t *pill = slurp("tests/kernel/pill.skit", &np);
    uint8_t *tick = slurp("tests/kernel/events.tick.skit", &nt);
    av_arena *s = av_arena_new(0);
    av_buf sb = { 0 };
    const char *err = NULL;
    CHECK(av_jam(s, AV_NODE_I, 100, &sb, &err));
    av_arena_free(s);
    av_opts o = av_opts_default();
    o.strategy = AV_SHARE;
    o.max_steps = 1000000;
    av_pier *p = av_pier_new_pma(pier, pill, np, (const uint8_t *)sb.s, sb.len, &o, &err);
    CHECK(p != NULL);
    if (!p) return;
    uint64_t bytes[1000], gcs = 0;
    for (int i = 0; i < 1000; i++) {
        uint32_t eff;
        av_result r;
        uint64_t c0 = av_pier_kernel(p)->a->collections;
        CHECK_EQ(av_pier_poke(p, tick, nt, &eff, &r, &err), AV_WHNF);
        bytes[i] = av_pma_last_bytes(av_pier_kernel(p)->a);
        if (av_pier_kernel(p)->a->collections != c0) { gcs++; bytes[i] = 0; }   /* all dirty */
    }
    uint64_t lo = UINT64_MAX, hi = 0;
    for (int i = 10; i < 1000; i++)
        if (bytes[i]) { if (bytes[i] < lo) lo = bytes[i]; if (bytes[i] > hi) hi = bytes[i]; }
    printf("  a pier on the arena: a Tick's commit writes %llu to %llu bytes, event 11 to 1000,"
           " but for %llu after a collection, which write the live arena\n",
           (unsigned long long)lo, (unsigned long long)hi, (unsigned long long)gcs);
    CHECK(hi <= 4 * 4096 + 512);                            /* a few chunks and the header */
    CHECK_EQ(state(p), 1000);
    av_pier_free(p);

    p = av_pier_open(pier, &o, &err);
    CHECK(p != NULL);
    if (p) {
        CHECK_EQ(av_pier_kernel(p)->events, 1000);
        CHECK_EQ(state(p), 1000);
        av_pier_free(p);
    }

    /* a crash between an event's log record and its commit: the reopen
     * replays it */
    pid_t pid = fork();
    if (pid == 0) {
        av_pier *q = av_pier_open(pier, &o, &err);
        uint32_t eff;
        av_result r;
        av_pma_crash_at = 1;
        if (q) av_pier_poke(q, tick, nt, &eff, &r, &err);
        _exit(0);
    }
    int st = 0;
    waitpid(pid, &st, 0);
    CHECK(WIFEXITED(st) && WEXITSTATUS(st) == 77);
    p = av_pier_open(pier, &o, &err);
    CHECK(p != NULL);
    if (p) {
        CHECK_EQ(av_pier_kernel(p)->events, 1001);
        CHECK_EQ(state(p), 1001);
        av_pier_free(p);
    }
    p = av_pier_open(pier, &o, &err);                       /* and it was committed */
    if (p) {
        CHECK_EQ(av_pier_kernel(p)->events, 1001);
        av_pier_free(p);
    }

    /* an image that will not commit after an event applied: the event is
     * a success, the failure beside it, and the next commit carries it
     * (AUDIT.md item 6) */
    char img[160];
    snprintf(img, sizeof img, "%s/pma", pier);
    p = av_pier_open(pier, &o, &err);
    REQUIRE(p != NULL);
    uint32_t eff;
    av_result r;
    CHECK(chmod(img, 0500) == 0);                           /* no journal can be made */
    CHECK_EQ(av_pier_poke(p, tick, nt, &eff, &r, &err), AV_WHNF);
    CHECK(av_pier_commit_error(p) != NULL);
    CHECK_EQ(av_pier_kernel(p)->events, 1002);
    CHECK(chmod(img, 0700) == 0);
    CHECK_EQ(av_pier_poke(p, tick, nt, &eff, &r, &err), AV_WHNF);
    CHECK(av_pier_commit_error(p) == NULL);
    CHECK_EQ(state(p), 1003);
    av_pier_free(p);
    p = av_pier_open(pier, &o, &err);
    REQUIRE(p != NULL);
    CHECK_EQ(av_pier_kernel(p)->events, 1003);
    CHECK_EQ(state(p), 1003);
    av_pier_free(p);
    av_buf_free(&sb);
    free(pill);
    free(tick);
    rmrf(d);
    free(d);
}

TEST_MAIN(
    TEST_CASE(an_image_reopens_to_what_was_committed),
    TEST_CASE(dirty_tracking_carries_every_write),
    TEST_CASE(a_commit_writes_what_changed_and_an_open_reads_nothing),
    TEST_CASE(a_crash_mid_commit_reopens_whole),
    TEST_CASE(a_journal_of_many_blocks_is_checked_then_applied),
    TEST_CASE(jets_and_damage_are_refused),
    TEST_CASE(a_pier_on_the_arena_commits_every_event),
)
