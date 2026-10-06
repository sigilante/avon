/**  test_kernel.c
 *
 *  Stage 7's acceptance (docs/DESIGN.md §9, §11, §20): against the
 *  reference host's loop (tests/kernel/export.py, from skijack's
 *  test_examples), a kernel survives pokes, answers a peek, and `load`
 *  moves a state onto a new battery, count for count in copy mode; a
 *  kernel installs code its compiler emitted and runs it, with the
 *  unquoter's jet as without; a pill boots; per-poke cost in share mode
 *  stays flat over a thousand events; and a pier reloads from its
 *  snapshot and log to the same state, after a crash as without.  Run
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
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *p = malloc((size_t)n + 1);
    *len = fread(p, 1, (size_t)n, f);
    p[*len] = 0;
    fclose(f);
    return p;
}

static uint32_t load(av_arena *a, const char *name) {
    char path[256];
    snprintf(path, sizeof path, DIR "%s.skit", name);
    size_t len;
    uint8_t *b = slurp(path, &len);
    uint32_t t = b ? av_cue(a, b, len, NULL) : AV_NONE;
    free(b);
    return t;
}

static char *expected(const char *name) {
    size_t len;
    char *text = (char *)slurp(DIR "expected.tsv", &len);
    char *out = NULL;
    for (char *line = text, *nl; text && *line; line = nl) {
        nl = strchr(line, '\n');
        if (nl) *nl++ = '\0';
        char *tab = strchr(line, '\t');
        if (tab && (*tab = '\0', strcmp(line, name) == 0)) out = strdup(tab + 1);
    }
    free(text);
    return out;
}

static uint64_t expected_n(const char *name) {
    char *v = expected(name);
    uint64_t n = v ? strtoull(v, NULL, 10) : UINT64_MAX;
    free(v);
    return n;
}

static av_opts copy_opts(void) {
    av_opts o = av_opts_default();
    o.strategy = AV_COPY;
    o.max_steps = 200000;
    return o;
}

static uint64_t nat(av_arena *a, uint32_t t) {
    av_opts o = copy_opts();
    o.no_collect = true;
    uint64_t n = UINT64_MAX;
    CHECK(av_read_nat(a, t, 100000, &o, &n, NULL));
    return n;
}

/*  One poke, as the reference loop reads it: its count, the state it
 *  leaves, its effects' constructor, and the effect's payload. */
static void poke_as_expected(av_kernel *k, uint32_t event, const char *prefix) {
    char key[128];
    uint32_t eff;
    av_result r;
    CHECK_EQ(av_kernel_poke(k, event, &eff, &r), AV_WHNF);
    av_root_push(k->a, &eff);
    av_opts po = copy_opts();
    po.no_collect = true;
    av_peeled pe;
    CHECK(av_peel(k->a, eff, 2, &po, &pe, NULL));
    char effect[64] = "-";
    if (pe.nfields > 0) {
        av_peeled log;
        CHECK(av_peel(k->a, pe.field[0], 1, &po, &log, NULL));
        snprintf(effect, sizeof effect, "Log:%llu", (unsigned long long)nat(k->a, log.field[0]));
    }
    av_root_pop(k->a);
    uint64_t state = nat(k->a, av_kernel_state(k));
    snprintf(key, sizeof key, "%s.steps", prefix);
    if (k->o.strategy == AV_COPY && !k->o.install_jets) CHECK_EQ(r.steps, expected_n(key));
    snprintf(key, sizeof key, "%s.state", prefix);
    CHECK_EQ(state, expected_n(key));
    snprintf(key, sizeof key, "%s.effects", prefix);
    char *want = expected(key);
    CHECK(want && strcmp(want, pe.ctor ? "Cons" : "Nil") == 0);
    free(want);
    snprintf(key, sizeof key, "%s.effect", prefix);
    want = expected(key);
    CHECK(want && strcmp(want, effect) == 0);
    if (want && strcmp(want, effect)) fprintf(stderr, "  %s: %s, want %s\n", prefix, effect, want);
    free(want);
}

TEST(the_selectors_are_the_abis) {
    av_arena *a = av_arena_new(0);
    uint32_t hd = load(a, "hd"), tl = load(a, "tl");
    uint32_t x = av_leaf(a, "x", 1);
    /* 2@x is hd x and 3@x is tl x: the same terms the reference applies */
    CHECK(av_equal(a, av_axis(a, 2, x), av_app(a, hd, x), 1000) == 1);
    CHECK(av_equal(a, av_axis(a, 3, x), av_app(a, tl, x), 1000) == 1);
    /* 10@x = hd (tl (hd x)) */
    CHECK(av_equal(a, av_axis(a, 10, x), av_app(a, hd, av_app(a, tl, av_app(a, hd, x))), 1000) == 1);
    av_arena_free(a);
}

/*  test_examples's sequence: Tick, Poke 5, Tick; peek; load. */
TEST(the_events_kernel_runs_as_the_reference_does) {
    av_arena *a = av_arena_new(1u << 16);
    uint32_t k0 = load(a, "events.kernel");
    av_root_push(a, &k0);
    av_opts o = copy_opts();
    CHECK(av_is_kernel(a, k0, &o));
    av_kernel k;
    av_kernel_adopt(&k, a, k0, &o);
    poke_as_expected(&k, load(a, "events.tick"), "events.poke1");
    poke_as_expected(&k, load(a, "events.poke5"), "events.poke2");
    uint32_t state2 = av_kernel_state(&k);
    av_root_push(a, &state2);
    poke_as_expected(&k, load(a, "events.tick"), "events.poke3");
    uint32_t ans;
    av_result r;
    CHECK_EQ(av_kernel_peek(&k, load(a, "events.zero"), &ans, &r), AV_WHNF);
    CHECK_EQ(r.steps, expected_n("events.peek.steps"));
    CHECK_EQ(nat(a, ans), expected_n("events.peek.value"));
    /* load: the first kernel's battery over poke 2's state */
    av_kernel old;
    av_kernel_adopt(&old, a, av_pull(a, AV_AXIS_LOAD, k0, state2), &o);
    CHECK_EQ(nat(a, av_kernel_state(&old)), expected_n("events.load.state"));
    poke_as_expected(&old, load(a, "events.tick"), "events.load.poke");
    av_kernel_free(&old);
    av_kernel_free(&k);
    av_root_pop(a);
    av_root_pop(a);
    av_arena_free(a);
}

/*  Tick, Run <double>, Run <triple>, Tick: the kernel installs what the
 *  compiler emitted and runs it -- with UQ reduced, and with UQ's jet
 *  installing natively, every fire checked. */
TEST(a_kernel_installs_compiled_code_and_runs_it) {
    for (int jet = 0; jet < 2; jet++) {
        av_arena *a = av_arena_new(1u << 16);
        av_opts o = copy_opts();
        o.max_steps = 5000000;
        if (jet) {
            const char *err = NULL;
            uint32_t uq = load(a, "install.uq");
            CHECK(av_unquote_register(a, uq, &err));
            o.install_jets = true;
            o.jet_check = 1;
        }
        uint32_t k0 = av_jets_match(a, load(a, "install.kernel"));
        av_kernel k;
        av_kernel_adopt(&k, a, k0, &o);
        poke_as_expected(&k, load(a, "install.tick"), "install.poke1");
        poke_as_expected(&k, load(a, "install.rundouble"), "install.poke2");
        poke_as_expected(&k, load(a, "install.runtriple"), "install.poke3");
        poke_as_expected(&k, load(a, "install.tick"), "install.poke4");
        /* the unquoter at the head: UQ <double> applied to the state, 7 */
        uint32_t t = av_app(a, av_app(a, load(a, "install.uq"), load(a, "install.qdouble")),
                            av_kernel_state(&k));
        t = av_jets_match(a, t);
        av_root_push(a, &t);
        av_opts ro = o;
        ro.whnf_only = false;
        av_result r = av_reduce(a, t, &ro);
        CHECK_EQ(r.status, AV_NORMAL);
        CHECK(!r.jet_fault);
        static uint64_t unjetted;
        static char nf[4096];
        av_buf b = { 0 };
        CHECK(av_print(a, r.term, 100000, &b));
        if (jet) CHECK(b.s && strcmp(b.s, nf) == 0);      /* the same normal form */
        else snprintf(nf, sizeof nf, "%s", b.s ? b.s : "");
        av_buf_free(&b);
        if (!jet) {
            unjetted = r.steps;
            CHECK_EQ(r.jet_calls, 0);
        } else {
            printf("  UQ <double> 7 to normal form: %llu contractions, %llu with the "
                   "unquoter's jet (%llu fires, checked)\n", (unsigned long long)unjetted,
                   (unsigned long long)r.steps, (unsigned long long)r.jet_calls);
            CHECK(r.jet_calls >= 1);
            CHECK(r.steps < unjetted);
        }
        av_root_pop(a);
        av_kernel_free(&k);
        av_arena_free(a);
    }
}

TEST(install_is_the_live_term_the_datum_encodes) {
    av_arena *a = av_arena_new(1u << 16);
    av_opts o = copy_opts();
    const char *err = NULL;
    uint32_t live = av_install(a, load(a, "install.qdouble"), &o, &err);
    CHECK(live != AV_NONE);
    CHECK(av_equal(a, live, load(a, "install.double"), 1000000) == 1);
    /* Avon's own encoding, installed, is the term */
    const char *src = "S (K (S I)) (S (K K) I)";
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    CHECK(av_equal(a, av_install(a, av_encode(a, t), &o, &err), t, 1000) == 1);
    /* a term that is no unquoter is not admitted */
    CHECK(!av_unquote_register(a, AV_NODE_I, &err));
    CHECK(av_unquote_register(a, load(a, "install.uq"), &err));
    av_arena_free(a);
}

TEST(a_pill_boots_to_a_kernel) {
    av_arena *a = av_arena_new(1u << 16);
    av_opts o = copy_opts();
    av_kernel k;
    bool is_kernel;
    uint32_t value;
    av_result r;
    CHECK_EQ(av_kernel_boot(&k, a, load(a, "pill"), AV_NODE_I, &o, &is_kernel, &value, &r), AV_WHNF);
    CHECK(is_kernel);
    uint32_t eff;
    if (is_kernel) {
        CHECK_EQ(av_kernel_poke(&k, load(a, "events.tick"), &eff, &r), AV_WHNF);
        CHECK_EQ(nat(a, av_kernel_state(&k)), 1);
        av_kernel_free(&k);
    }
    /* K I is no kernel: applied once and reduced */
    uint32_t ki = av_app(a, AV_NODE_K, AV_NODE_I);
    CHECK_EQ(av_kernel_boot(&k, a, ki, AV_NODE_I, &o, &is_kernel, &value, &r), AV_WHNF);
    CHECK(!is_kernel);
    CHECK(value != AV_NONE && av_equal(a, value, AV_NODE_I, 10) == 1);
    av_arena_free(a);
}

/*  §9: under share mode each state is computed once, so a Tick costs the
 *  same however many came before; copy mode pays for the history. */
TEST(share_mode_pokes_stay_flat) {
    av_arena *a = av_arena_new(1u << 12);            /* small: it collects */
    av_opts o = av_opts_default();
    o.strategy = AV_SHARE;
    o.max_steps = 1000000;
    av_kernel k;
    av_kernel_adopt(&k, a, load(a, "events.kernel"), &o);
    uint32_t tick = load(a, "events.tick");
    av_root_push(a, &tick);
    uint64_t steps[1000];
    for (int i = 0; i < 1000; i++) {
        uint32_t eff;
        av_result r;
        CHECK_EQ(av_kernel_poke(&k, tick, &eff, &r), AV_WHNF);
        steps[i] = r.steps;
    }
    uint64_t lo = UINT64_MAX, hi = 0;
    for (int i = 10; i < 1000; i++) {
        if (steps[i] < lo) lo = steps[i];
        if (steps[i] > hi) hi = steps[i];
    }
    printf("  share mode: pokes 1-3 cost %llu, %llu, %llu; pokes 11-1000 between %llu and %llu;"
           " %llu collections\n", (unsigned long long)steps[0], (unsigned long long)steps[1],
           (unsigned long long)steps[2], (unsigned long long)lo, (unsigned long long)hi,
           (unsigned long long)a->collections);
    CHECK_EQ(lo, hi);
    CHECK(a->collections > 0);
    CHECK_EQ(nat(a, av_kernel_state(&k)), 1000);
    av_root_pop(a);
    av_kernel_free(&k);
    av_arena_free(a);
}

/*  ------------------------------------------------------------ the pier */

static uint8_t *bytes_of(const char *name, size_t *len) {
    char path[256];
    snprintf(path, sizeof path, DIR "%s.skit", name);
    return slurp(path, len);
}

static uint8_t *jam_of(av_arena *a, uint32_t t, size_t *len) {
    av_buf b = { 0 };
    const char *msg = NULL;
    if (!av_jam(a, t, 100000000, &b, &msg)) return NULL;
    *len = b.len;
    return (uint8_t *)b.s;
}

static uint64_t pier_state(av_pier *p) {
    av_kernel *k = av_pier_kernel(p);
    return nat(k->a, av_kernel_state(k));
}

static char *kernel_hash(av_pier *p) {
    static char h[27];
    av_kernel *k = av_pier_kernel(p);
    CHECK(av_structural_hash(k->a, k->k, h));
    return h;
}

TEST(a_pier_reloads_to_the_same_state) {
    char dir[] = "/tmp/avon-pier-XXXXXX";
    CHECK(mkdtemp(dir) != NULL);
    char pier[128];
    snprintf(pier, sizeof pier, "%s/pier", dir);
    av_opts o = copy_opts();
    size_t np, nt, n5, ni = 0;
    uint8_t *pill = bytes_of("pill", &np), *tick = bytes_of("events.tick", &nt);
    uint8_t *poke5 = bytes_of("events.poke5", &n5);
    av_arena *s = av_arena_new(0);
    uint8_t *subject = jam_of(s, AV_NODE_I, &ni);
    av_arena_free(s);
    const char *err = NULL;

    av_pier *p = av_pier_new(pier, pill, np, subject, ni, &o, &err);
    CHECK(p != NULL);
    if (!p) return;
    CHECK(av_pier_new(pier, pill, np, subject, ni, &o, &err) == NULL);   /* one per dir */
    uint32_t eff;
    av_result r;
    CHECK_EQ(av_pier_poke(p, tick, nt, &eff, &r, &err), AV_WHNF);
    CHECK_EQ(av_pier_poke(p, poke5, n5, &eff, &r, &err), AV_WHNF);
    CHECK(av_pier_snapshot(p, &err));                       /* at 2 */
    CHECK_EQ(av_pier_poke(p, tick, nt, &eff, &r, &err), AV_WHNF);
    CHECK_EQ(pier_state(p), 7);
    char want[27];
    strcpy(want, kernel_hash(p));
    av_pier_free(p);                                        /* a crash, after 3 */

    /* a record torn by the crash: dropped */
    char logp[160];
    snprintf(logp, sizeof logp, "%s/events.log", pier);
    FILE *f = fopen(logp, "ab");
    fputs("poke 4 5b4a", f);
    fclose(f);

    p = av_pier_open(pier, &o, &err);
    CHECK(p != NULL);
    if (!p) return;
    CHECK_EQ(av_pier_kernel(p)->events, 3);
    CHECK_EQ(pier_state(p), 7);
    CHECK(strcmp(kernel_hash(p), want) == 0);               /* snapshot 2, replayed 3 */
    CHECK_EQ(av_pier_poke(p, tick, nt, &eff, &r, &err), AV_WHNF);
    CHECK_EQ(pier_state(p), 8);

    /* an event that does not reduce is not kept */
    av_arena *e = av_arena_new(0);
    const char *om = "S I I (S I I)";
    size_t nom;
    uint8_t *omega = jam_of(e, av_parse(e, om, strlen(om), NULL), &nom);
    av_arena_free(e);
    CHECK_EQ(av_pier_poke(p, omega, nom, &eff, &r, &err), AV_FUEL);
    CHECK_EQ(av_pier_kernel(p)->events, 4);

    /* load: the install kernel's battery over this state; its Run event
     * then doubles the state */
    size_t nk, nr;
    av_arena *b = av_arena_new(0);
    uint8_t *ipill = jam_of(b, av_app(b, AV_NODE_K, load(b, "install.kernel")), &nk);
    av_arena_free(b);
    uint8_t *run2 = bytes_of("install.rundouble", &nr);
    CHECK(av_pier_load(p, ipill, nk, subject, ni, &err));
    CHECK_EQ(pier_state(p), 8);
    CHECK_EQ(av_pier_poke(p, run2, nr, &eff, &r, &err), AV_WHNF);
    CHECK_EQ(pier_state(p), 16);
    strcpy(want, kernel_hash(p));
    av_pier_free(p);

    p = av_pier_open(pier, &o, &err);                       /* snapshot 2, replay 3..6 */
    CHECK(p != NULL);
    if (p) {
        CHECK_EQ(av_pier_kernel(p)->events, 6);
        CHECK_EQ(pier_state(p), 16);
        CHECK(strcmp(kernel_hash(p), want) == 0);
        av_pier_free(p);
    }
    free(pill); free(tick); free(poke5); free(subject); free(omega); free(ipill); free(run2);
    char cmd[256];
    snprintf(cmd, sizeof cmd, "/bin/rm -rf %s", dir);
    CHECK(system(cmd) == 0);
}

static long file_size(const char *path) {
    struct stat st;
    return stat(path, &st) == 0 ? (long)st.st_size : -1;
}

/*  A logged event is one the kernel took: a reopen replays it with no fuel
 *  limit, whatever this run's --fuel, and drops nothing but a torn record;
 *  an event that cannot replay stops the open and stays in the log. */
TEST(a_logged_event_replays_whatever_the_fuel) {
    char dir[] = "/tmp/avon-replay-XXXXXX";
    CHECK(mkdtemp(dir) != NULL);
    char pier[128], logp[160];
    snprintf(pier, sizeof pier, "%s/pier", dir);
    snprintf(logp, sizeof logp, "%s/events.log", pier);
    av_opts o = copy_opts();
    size_t np, nt, n5, ni = 0;
    uint8_t *pill = bytes_of("pill", &np), *tick = bytes_of("events.tick", &nt);
    uint8_t *poke5 = bytes_of("events.poke5", &n5);
    av_arena *s = av_arena_new(0);
    uint8_t *subject = jam_of(s, AV_NODE_I, &ni);
    av_arena_free(s);
    const char *err = NULL;
    av_pier *p = av_pier_new(pier, pill, np, subject, ni, &o, &err);
    REQUIRE(p != NULL);
    uint32_t eff;
    av_result r;
    CHECK_EQ(av_pier_poke(p, tick, nt, &eff, &r, &err), AV_WHNF);
    CHECK_EQ(av_pier_poke(p, poke5, n5, &eff, &r, &err), AV_WHNF);
    av_pier_free(p);
    long logged = file_size(logp);
    CHECK(logged > 0);

    av_opts starved = o;
    starved.max_steps = 5;                                  /* each event took more */
    p = av_pier_open(pier, &starved, &err);
    REQUIRE(p != NULL);
    CHECK_EQ(av_pier_kernel(p)->events, 2);
    CHECK_EQ(pier_state(p), 6);
    CHECK_EQ(av_pier_poke(p, tick, nt, &eff, &r, &err), AV_FUEL);   /* the live fuel holds */
    CHECK_EQ(av_pier_kernel(p)->events, 2);
    av_pier_free(p);
    CHECK_EQ(file_size(logp), logged);

    /* a logged event that does not reach weak head normal form */
    av_arena *e = av_arena_new(0);
    const char *om = "S I I (S I I)";
    size_t nom;
    uint8_t *omega = jam_of(e, av_parse(e, om, strlen(om), NULL), &nom);
    av_arena_free(e);
    FILE *f = fopen(logp, "ab");
    REQUIRE(f != NULL);
    fputs("poke 3 ", f);
    for (size_t i = 0; i < nom; i++) fprintf(f, "%02x", omega[i]);
    fputc('\n', f);
    fclose(f);
    logged = file_size(logp);
    av_opts small = o;
    small.max_nodes = 1u << 16;                             /* omega grows: SIZE, not forever */
    CHECK(av_pier_open(pier, &small, &err) == NULL);
    CHECK(err != NULL && strstr(err, "does not replay") != NULL);
    CHECK_EQ(file_size(logp), logged);                      /* refused, and kept */

    free(pill); free(tick); free(poke5); free(subject); free(omega);
    char cmd[256];
    snprintf(cmd, sizeof cmd, "/bin/rm -rf %s", dir);
    CHECK(system(cmd) == 0);
}

/*  A pier holds the kernel's entropy: its directory is the caller's alone,
 *  0700, its files 0600, and a directory someone else could read or write
 *  is refused. */
TEST(a_pier_is_closed_to_others) {
    char dir[] = "/tmp/avon-mode-XXXXXX";
    CHECK(mkdtemp(dir) != NULL);
    char pier[128], logp[160], open_dir[128], empty[128];
    snprintf(pier, sizeof pier, "%s/pier", dir);
    snprintf(logp, sizeof logp, "%s/events.log", pier);
    snprintf(open_dir, sizeof open_dir, "%s/open", dir);
    snprintf(empty, sizeof empty, "%s/empty", dir);
    av_opts o = copy_opts();
    size_t np, ni = 0;
    uint8_t *pill = bytes_of("pill", &np);
    av_arena *s = av_arena_new(0);
    uint8_t *subject = jam_of(s, AV_NODE_I, &ni);
    av_arena_free(s);
    const char *err = NULL;
    mode_t old = umask(0);                                  /* the widest umask */
    av_pier *p = av_pier_new(pier, pill, np, subject, ni, &o, &err);
    umask(old);
    REQUIRE(p != NULL);
    av_pier_free(p);
    struct stat st;
    CHECK(stat(pier, &st) == 0 && (st.st_mode & 0777) == 0700);
    CHECK(stat(logp, &st) == 0 && (st.st_mode & 0777) == 0600);

    CHECK(mkdir(open_dir, 0700) == 0 && chmod(open_dir, 0755) == 0);
    CHECK(av_pier_new(open_dir, pill, np, subject, ni, &o, &err) == NULL);
    CHECK(err != NULL && strstr(err, "0700") != NULL);
    CHECK(mkdir(empty, 0700) == 0);                         /* empty, the caller's, 0700 */
    p = av_pier_new(empty, pill, np, subject, ni, &o, &err);
    CHECK(p != NULL);
    av_pier_free(p);

    free(pill); free(subject);
    char cmd[256];
    snprintf(cmd, sizeof cmd, "/bin/rm -rf %s", dir);
    CHECK(system(cmd) == 0);
}

TEST_MAIN(
    TEST_CASE(the_selectors_are_the_abis),
    TEST_CASE(the_events_kernel_runs_as_the_reference_does),
    TEST_CASE(a_kernel_installs_compiled_code_and_runs_it),
    TEST_CASE(install_is_the_live_term_the_datum_encodes),
    TEST_CASE(a_pill_boots_to_a_kernel),
    TEST_CASE(share_mode_pokes_stay_flat),
    TEST_CASE(a_pier_reloads_to_the_same_state),
    TEST_CASE(a_logged_event_replays_whatever_the_fuel),
    TEST_CASE(a_pier_is_closed_to_others),
)
