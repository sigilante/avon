/**  test_drivers.c
 *
 *  Drivers in a pier, on the kernels of tests/drivers/: a run stopped where
 *  it would answer a request live, the pier freed as a crash would leave
 *  it, and reopened, ends as the run in memory does, its output the same
 *  bytes in two parts; the step count and a file's entropy go on from where
 *  the stopped run left them; a finished run reopened performs nothing; a
 *  log whose answers are another run's is refused; a poke past its fuel
 *  leaves the log, but boot's answer stays with the arguments; and a
 *  drivers pier is driven once an open, never poked, loaded or snapshot,
 *  while a plain pier is never driven.  Run from the repository root.
 */

#include <fcntl.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#include "avon.h"
#include "test.h"

#define DIR "tests/drivers/"

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

static void rm_rf(const char *dir) {
    char cmd[256];
    snprintf(cmd, sizeof cmd, "/bin/rm -rf %s", dir);
    CHECK(system(cmd) == 0);
}

static void write_file(const char *path, const void *b, size_t n) {
    FILE *f = fopen(path, "wb");
    CHECK(f && fwrite(b, 1, n, f) == n);
    if (f) fclose(f);
}

/*  A world: standard input from a file, output and error to files of
 *  their own, in a fresh directory. */
typedef struct {
    char dir[64], pier[96], out[96], err[96];
    int  fd[3];
} world;

static void world_open(world *w, const void *in, size_t nin) {
    strcpy(w->dir, "/tmp/avon-drv-XXXXXX");
    CHECK(mkdtemp(w->dir) != NULL);
    char inp[96];
    snprintf(inp, sizeof inp, "%s/in", w->dir);
    snprintf(w->pier, sizeof w->pier, "%s/pier", w->dir);
    snprintf(w->out, sizeof w->out, "%s/out", w->dir);
    snprintf(w->err, sizeof w->err, "%s/err", w->dir);
    write_file(inp, in, nin);
    w->fd[0] = open(inp, O_RDONLY);
    w->fd[1] = open(w->out, O_WRONLY | O_CREAT | O_TRUNC, 0600);
    w->fd[2] = open(w->err, O_WRONLY | O_CREAT | O_TRUNC, 0600);
    CHECK(w->fd[0] >= 0 && w->fd[1] >= 0 && w->fd[2] >= 0);
}

static void world_close(world *w) {
    for (int i = 0; i < 3; i++) close(w->fd[i]);
    rm_rf(w->dir);
}

static uint8_t *output(const world *w, size_t *n) { return slurp(w->out, n); }

static av_opts opts(av_strategy s) {
    av_opts o = av_opts_default();
    o.strategy = s;
    o.max_steps = 100000000;
    return o;
}

static char *const echo_argv[] = { "echo", NULL };

static av_run run_of(const world *w, const char *eny_file) {
    av_run d = { .fd = { w->fd[0], w->fd[1], w->fd[2] }, .argc = 1, .argv = echo_argv };
    d.entropy_file = eny_file;
    d.entropy = eny_file != NULL;
    return d;
}

/*  The kernel NAME run in memory on input in: its output and status. */
static uint8_t *in_memory(const char *name, av_strategy s, const void *in, size_t nin,
                          const char *eny_file, size_t *nout, int *status) {
    world w;
    world_open(&w, in, nin);
    char path[128];
    snprintf(path, sizeof path, DIR "%s.skit", name);
    size_t n;
    uint8_t *b = slurp(path, &n);
    av_arena *a = av_arena_new(1u << 16);
    uint32_t t = av_cue(a, b, n, NULL);
    free(b);
    av_opts o = opts(s);
    av_kernel k;
    av_kernel_adopt(&k, a, t, &o);
    av_run d = run_of(&w, eny_file);
    av_result r;
    const char *err = NULL;
    CHECK_EQ(av_run_kernel(&k, &d, &r, &err), AV_WHNF);
    *status = d.status;
    av_kernel_free(&k);
    av_arena_free(a);
    uint8_t *out = output(&w, nout);
    world_close(&w);
    return out;
}

static av_pier *new_pier(const world *w, const char *name, av_strategy s, const char *eny_file,
                         av_run *d) {
    char path[128];
    snprintf(path, sizeof path, DIR "%s.skit", name);
    size_t n;
    uint8_t *b = slurp(path, &n);
    av_opts o = opts(s);
    const char *err = NULL;
    unsigned flags = eny_file ? AV_PIER_ENTROPY_FILE : 0u;
    av_pier *p = av_pier_new_drivers(w->pier, b, n, &o, flags, d, &err);
    free(b);
    CHECK(p != NULL);
    return p;
}

/*  Stop after `stop` pokes, free the pier, reopen it and finish: the same
 *  status and output as in memory, for every stopping point the run has. */
static void stop_and_resume(const char *name, av_strategy s, const void *in, size_t nin,
                            const char *eny_file) {
    size_t nwant;
    int want;
    uint8_t *ref = in_memory(name, s, in, nin, eny_file, &nwant, &want);
    for (uint64_t stop = 1;; stop++) {
        world w;
        world_open(&w, in, nin);
        av_run d = run_of(&w, eny_file);
        av_pier *p = new_pier(&w, name, s, eny_file, &d);
        d.max_pokes = stop;
        av_result r;
        const char *err = NULL;
        CHECK_EQ(av_pier_drive(p, &d, &r, &err), AV_WHNF);
        bool stopped = d.stopped;
        av_pier_free(p);                        /* the crash */
        av_opts o = opts(s);
        p = av_pier_open(w.pier, &o, &err);
        CHECK(p != NULL && av_pier_is_drivers(p));
        av_run e = run_of(&w, eny_file);
        CHECK_EQ(av_pier_drive(p, &e, &r, &err), AV_WHNF);
        CHECK(!e.stopped);
        CHECK_EQ(e.status, want);
        CHECK_EQ(e.pokes, stopped ? e.pokes : d.pokes);
        av_pier_free(p);
        size_t nout;
        uint8_t *out = output(&w, &nout);
        CHECK_EQ(nout, nwant);
        CHECK(nout == nwant && memcmp(out, ref, nout) == 0);
        free(out);
        world_close(&w);
        if (!stopped) break;                    /* the run ended before the stop */
    }
    free(ref);
}

TEST(a_stopped_run_resumes_to_the_same_output) {
    char in[200];
    for (size_t i = 0; i < sizeof in; i++) in[i] = (char)('a' + i % 26);
    stop_and_resume("echo", AV_COPY, in, sizeof in, NULL);
    stop_and_resume("echo", AV_SHARE, in, sizeof in, NULL);
    stop_and_resume("echo", AV_SHARE, "", 0, NULL);
}

/*  The step count answers the pokes' contractions since boot, replayed
 *  ones too: copy mode's is the reference host's 52. */
TEST(the_step_count_goes_on_across_a_reopen) {
    stop_and_resume("steps", AV_COPY, "", 0, NULL);
    stop_and_resume("steps", AV_SHARE, "", 0, NULL);
    size_t n;
    int status;
    free(in_memory("steps", AV_COPY, "", 0, NULL, &n, &status));
    CHECK_EQ(status, 52);
}

TEST(a_files_entropy_draws_on_across_a_reopen) {
    stop_and_resume("bits", AV_SHARE, "", 0, DIR "bits.eny");
    stop_and_resume("bits", AV_COPY, "", 0, DIR "bits.eny");
}

/*  A finished run reopened replays to its exit and performs nothing. */
TEST(a_finished_run_reopened_performs_nothing) {
    world w;
    world_open(&w, "hello\n", 6);
    av_run d = run_of(&w, NULL);
    av_pier *p = new_pier(&w, "echo", AV_SHARE, NULL, &d);
    av_result r;
    const char *err = NULL;
    CHECK_EQ(av_pier_drive(p, &d, &r, &err), AV_WHNF);
    av_pier_free(p);
    size_t n1, n2;
    free(output(&w, &n1));
    av_opts o = opts(AV_SHARE);
    p = av_pier_open(w.pier, &o, &err);
    CHECK(p != NULL);
    av_run e = run_of(&w, NULL);
    CHECK_EQ(av_pier_drive(p, &e, &r, &err), AV_WHNF);
    CHECK_EQ(e.status, d.status);
    CHECK_EQ(e.pokes, d.pokes);
    CHECK_EQ(e.steps, d.steps);
    CHECK(e.replaying);                         /* it never went live */
    free(output(&w, &n2));
    CHECK_EQ(n2, n1);                           /* nothing written again */
    av_pier_free(p);
    world_close(&w);
}

/*  echo's log under show's kernel: the first request show makes is not
 *  the one the log answers. */
TEST(a_log_of_another_run_is_refused) {
    world w, v;
    world_open(&w, "hello\n", 6);
    world_open(&v, "", 0);
    av_run d = run_of(&w, NULL), e = run_of(&v, NULL);
    av_pier *p = new_pier(&w, "echo", AV_SHARE, NULL, &d);
    av_result r;
    const char *err = NULL;
    CHECK_EQ(av_pier_drive(p, &d, &r, &err), AV_WHNF);
    av_pier_free(p);
    av_pier *q = new_pier(&v, "show", AV_SHARE, NULL, &e);
    av_pier_free(q);
    /* show's pier, its log echo's: a read's answer where show asks for a
     * variable */
    char from[128], to[128];
    snprintf(from, sizeof from, "%s/events.log", w.pier);
    snprintf(to, sizeof to, "%s/events.log", v.pier);
    size_t n;
    uint8_t *log = slurp(from, &n);
    write_file(to, log, n);
    free(log);
    av_opts o = opts(AV_SHARE);
    q = av_pier_open(v.pier, &o, &err);
    CHECK(q != NULL);
    av_run f = run_of(&v, NULL);
    CHECK_EQ(av_pier_drive(q, &f, &r, &err), AV_SIZE);
    CHECK(err && strstr(err, "another request"));
    av_pier_free(q);
    world_close(&w);
    world_close(&v);
}

static size_t log_records(const char *pier) {
    char path[128];
    snprintf(path, sizeof path, "%s/events.log", pier);
    size_t n, lines = 0;
    uint8_t *b = slurp(path, &n);
    for (size_t i = 0; i < n; i++) lines += b[i] == '\n';
    free(b);
    return lines;
}

/*  A poke that runs out of fuel did not apply: its answer leaves the log,
 *  and a reopen with more fuel goes on from the answer before.  Boot's
 *  answer stays, so a pier whose first poke ran out still opens. */
TEST(a_poke_past_its_fuel_leaves_the_log) {
    bool cut = false;
    for (uint64_t fuel = 1; fuel < 100000 && !cut; fuel = fuel * 3 / 2 + 1) {
        world w;
        world_open(&w, "hello\n", 6);
        av_run d = run_of(&w, NULL);
        av_opts o = opts(AV_SHARE);
        o.max_steps = fuel;
        size_t n;
        uint8_t *b = slurp(DIR "echo.skit", &n);
        const char *err = NULL;
        av_pier *p = av_pier_new_drivers(w.pier, b, n, &o, 0, &d, &err);
        free(b);
        CHECK(p != NULL);
        if (!p) { world_close(&w); break; }
        av_result r;
        av_status st = av_pier_drive(p, &d, &r, &err);
        av_pier_free(p);
        if (st == AV_WHNF) { world_close(&w); break; }  /* fuel enough: nothing ran out */
        /* the drivers record and an answer per applied poke, boot's
         * answer whether or not its poke applied */
        CHECK_EQ(log_records(w.pier), 1 + (d.pokes ? d.pokes : 1));
        cut = d.pokes >= 1;
        av_opts more = opts(AV_SHARE);
        p = av_pier_open(w.pier, &more, &err);
        CHECK(p != NULL);
        if (!p) { world_close(&w); break; }
        av_run e = run_of(&w, NULL);
        CHECK_EQ(av_pier_drive(p, &e, &r, &err), AV_WHNF);
        CHECK_EQ(e.status, 0);
        av_pier_free(p);
        world_close(&w);
    }
    CHECK(cut);                                 /* some fuel ran out past boot */
}

TEST(a_drivers_pier_is_driven_once_and_only_driven) {
    world w;
    world_open(&w, "", 0);
    av_run d = run_of(&w, NULL);
    av_pier *p = new_pier(&w, "echo", AV_SHARE, NULL, &d);
    const char *err = NULL;
    uint32_t eff;
    av_result r;
    CHECK_EQ(av_pier_poke(p, (const uint8_t *)"x", 1, &eff, &r, &err), AV_SIZE);
    CHECK(!av_pier_snapshot(p, &err));
    CHECK(!av_pier_load(p, (const uint8_t *)"x", 1, (const uint8_t *)"x", 1, &err));
    CHECK(!av_pier_entropy(p, NULL, &err));
    CHECK_EQ(av_pier_drive(p, &d, &r, &err), AV_WHNF);
    CHECK_EQ(av_pier_drive(p, &d, &r, &err), AV_SIZE);
    av_pier_free(p);
    /* a plain pier is not driven */
    size_t n;
    uint8_t *pill = slurp("tests/kernel/entropy.pill.skit", &n);
    av_arena *s = av_arena_new(0);
    av_buf sb = { 0 };
    CHECK(av_jam(s, AV_NODE_I, 16, &sb, NULL));
    av_arena_free(s);
    char plain[128];
    snprintf(plain, sizeof plain, "%s/plain", w.dir);
    av_opts o = opts(AV_SHARE);
    p = av_pier_new(plain, pill, n, (const uint8_t *)sb.s, sb.len, &o, &err);
    free(pill);
    av_buf_free(&sb);
    CHECK(p != NULL && !av_pier_is_drivers(p));
    av_run e = run_of(&w, NULL);
    CHECK_EQ(av_pier_drive(p, &e, &r, &err), AV_SIZE);
    av_pier_free(p);
    world_close(&w);
}

TEST_MAIN(
    TEST_CASE(a_stopped_run_resumes_to_the_same_output),
    TEST_CASE(the_step_count_goes_on_across_a_reopen),
    TEST_CASE(a_files_entropy_draws_on_across_a_reopen),
    TEST_CASE(a_finished_run_reopened_performs_nothing),
    TEST_CASE(a_log_of_another_run_is_refused),
    TEST_CASE(a_poke_past_its_fuel_leaves_the_log),
    TEST_CASE(a_drivers_pier_is_driven_once_and_only_driven),
)
