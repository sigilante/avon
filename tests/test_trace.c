/**  test_trace.c
 *
 *  Frame traces (docs/DESIGN.md §22): the observer of copy mode's head run
 *  for the pure S calculus with the passenger X.
 *
 *  - Hand-traced runs give their lines: a z-step then a halt with X at the
 *    head (HALT-X), a y-step, an OPEN, a HALT-B.
 *  - An OPEN at the horizon's last step is OPEN, not FUEL.
 *  - Every line's positions, d, D and front arity equal a recount from the
 *    frame dumped at that step, through a long run.
 *  - The records are the strict future minima of the printed lengths, and
 *    the confirmed ones those with n + CONF <= H.
 *  - A dumped frame read back in the DAG form is the frame.
 *  - A term with K or I is refused; a malformed DAG term is refused; a
 *    long run stays linear.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "avon.h"
#include "test.h"

#define R10 "S (S (S S)) (S (S S)) (S S) S"

typedef struct {
    av_status status;
    uint64_t  steps;
    char     *text;                 /* everything the trace printed */
    size_t    len;
} traced;

/*  src traced to the horizon H; dumps at the given steps (and at a halt). */
static traced trace(const char *src, uint64_t H, size_t conf, const uint64_t *dumps,
                    size_t nd, bool *refused) {
    traced out = { 0 };
    av_arena *a = av_arena_new(1u << 12);
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    CHECK(t != AV_NONE);
    FILE *f = tmpfile();
    av_trace *tr = av_trace_new(a, "X", true, f);
    CHECK(tr != NULL);
    bool ok = av_trace_check(tr, a, t);
    if (refused) *refused = !ok;
    if (ok) {
        if (nd) CHECK(av_trace_dump_at(tr, dumps, nd));
        av_trace_dump_halt(tr, true);
        av_opts o = av_opts_default();
        o.strategy = AV_COPY;
        o.whnf_only = true;
        o.no_collect = true;
        o.max_steps = H;
        o.trace = tr;
        av_result r = av_reduce(a, t, &o);
        av_trace_summary sum;
        CHECK(av_trace_end(tr, a, r.status, r.steps, r.term, conf, conf > 0, &sum));
        out.status = r.status;
        out.steps = r.steps;
    }
    av_trace_flush(tr);
    av_trace_free(tr);
    av_arena_free(a);
    long n = ftell(f);
    rewind(f);
    out.text = malloc((size_t)n + 1);
    out.len = fread(out.text, 1, (size_t)n, f);
    out.text[out.len] = '\0';
    fclose(f);
    return out;
}

TEST(hand_traced_runs_give_their_lines) {
    struct { const char *src, *want; } cases[] = {
        /* [S, S, X]: X at the z-seat; the step leaves [X, S X], a halt */
        { "S S S X", "0 3 1 0 0 z 0\n. WHNF 1 HALT-X\n" },
        /* [SS, SS, X]: a z-step, then [S, X, SS X]: X at the y-seat, its
         * stack the mint SS X (sigma 1, below 2), so D = 0 */
        { "S (S S) (S S) X", "0 3 1 0 0 z 1\n1 3 2 1 0 y 0\n. WHNF 2 HALT-X\n" },
        /* the census's own run of S(SS)(SS)S . X: OPEN at step 4 */
        { "S (S S) (S S) S X",
          "0 4 1 0 0 - 1\n1 4 1 0 0 - 0\n2 3 1 0 0 z 2\n3 4 2 1 0 z 0\n4 3 3 2 0 o 0\n"
          ". WHNF 5 OPEN\n" },
        /* [S, S X, S]: no X-headed item; the halt [S, S X S] holds X buried */
        { "S S (S X) S", "0 3 - - - - 0\n. WHNF 1 HALT-B\n" },
    };
    for (size_t i = 0; i < sizeof cases / sizeof *cases; i++) {
        traced r = trace(cases[i].src, 600, 0, NULL, 0, NULL);
        /* the lines up to the end line; the halt's dump follows */
        char *end = strstr(r.text, ". ");
        CHECK(end != NULL);
        if (end) {
            char *nl = strchr(end, '\n');
            size_t n = nl ? (size_t)(nl - r.text) + 1 : r.len;
            CHECK(n == strlen(cases[i].want) && memcmp(r.text, cases[i].want, n) == 0);
            if (!(n == strlen(cases[i].want) && memcmp(r.text, cases[i].want, n) == 0))
                fprintf(stderr, "  %s:\n%.*s", cases[i].src, (int)n, r.text);
        }
        free(r.text);
    }
}

/*  An OPEN at the horizon's last step: the census's run of S(SS)(SS)S . X
 *  opens at step 4, so at H = 5 the opening contraction spends the last
 *  fuel.  The exit is OPEN, as the census's, and no records follow; at
 *  H = 4 the run never sees the open, and the exit is FUEL. */
TEST(an_open_at_the_last_step_is_open) {
    const char *src = "S (S S) (S S) S X";
    traced r = trace(src, 5, 1, NULL, 0, NULL);
    CHECK(r.status == AV_FUEL && r.steps == 5);
    CHECK(strstr(r.text, "4 3 3 2 0 o 0\n. FUEL 5 OPEN\n") != NULL);
    CHECK(strstr(r.text, "\nR") == NULL && strstr(r.text, "\nK") == NULL);
    free(r.text);
    r = trace(src, 4, 1, NULL, 0, NULL);
    CHECK(strstr(r.text, ". FUEL 4 FUEL\n") != NULL);
    CHECK(strstr(r.text, "\nR") != NULL);
    free(r.text);
}

/*  ------------------------------------------- a recount from the dumps */

typedef struct { uint32_t l, r; char leaf; } dnode;     /* leaf: 'S', 'X', or 0 */

static int xheaded(const dnode *t, uint32_t i) {
    while (!t[i].leaf) i = t[i].l;
    return t[i].leaf == 'X';
}

static void recount(const dnode *t, const uint32_t *fr, size_t L, char *line) {
    /* fr[0] at the x-seat; the line as the trace prints it */
    size_t np = 0, p = 0;
    char pos[1024] = "";
    for (size_t i = 0; i < L; i++)
        if (xheaded(t, fr[i])) {
            size_t q = strlen(pos);
            snprintf(pos + q, sizeof pos - q, "%s%zu", np ? "," : "", L - i);
            np++;
            if (np == 1) p = i;
        }
    if (!np) strcpy(pos, "-");
    char ev = '-';
    if (np) {
        size_t q = L - p;                       /* the front-most */
        ev = q == L ? 'o' : q == L - 1 ? 'y' : q == L - 2 ? 'z' : '-';
    }
    unsigned fa = 0;
    for (uint32_t u = fr[0]; !t[u].leaf; u = t[u].l) fa++;
    char dD[32] = " - -";
    if (np == 1) {
        unsigned D = 0;
        for (size_t i = 0; i < L; i++) {
            if (i == p) continue;
            unsigned s = 0;
            for (uint32_t u = fr[i]; !t[u].leaf; u = t[u].l) s += (unsigned)xheaded(t, t[u].r);
            if (i < p ? s >= 1 : s >= 2) D++;
        }
        snprintf(dD, sizeof dD, " %zu %u", L - p - 1, D);
    }
    snprintf(line, 1200, "%zu %s%s %c %u", L, pos, dD, ev, fa);
}

TEST(every_line_equals_a_recount_from_its_frame) {
    /* r10 X, a ride: every step dumped, every line recounted */
    enum { H = 300 };
    uint64_t steps[H];
    for (uint64_t i = 0; i < H; i++) steps[i] = i;
    traced r = trace(R10 " X", H, 0, steps, H, NULL);
    CHECK_EQ(r.status, AV_FUEL);
    dnode *t = calloc(1u << 20, sizeof *t);
    char (*lines)[1200] = calloc(H, sizeof *lines);
    size_t checked = 0;
    char *save = NULL;
    for (char *ln = strtok_r(r.text, "\n", &save); ln; ln = strtok_r(NULL, "\n", &save)) {
        if (ln[0] == 'd') {
            unsigned id, l, rr;
            char c;
            if (sscanf(ln, "d %u=%u.%u", &id, &l, &rr) == 3) t[id] = (dnode){ l, rr, 0 };
            else if (sscanf(ln, "d %u=%c", &id, &c) == 2) t[id] = (dnode){ 0, 0, c };
        } else if (ln[0] == 'f') {
            unsigned long step;
            int off;
            sscanf(ln, "f %lu%n", &step, &off);
            uint32_t fr[4096];
            size_t L = 0;
            char *q = ln + off;
            unsigned v;
            int k;
            while (L < 4096 && sscanf(q, " %u%n", &v, &k) == 1) { fr[L++] = v; q += k; }
            char want[1200];
            recount(t, fr, L, want);
            if (step < H) {
                CHECK(strcmp(lines[step], want) == 0);
                if (strcmp(lines[step], want) != 0)
                    fprintf(stderr, "  step %lu: trace '%s', recount '%s'\n", step, lines[step], want);
                checked++;
            }
        } else if (ln[0] >= '0' && ln[0] <= '9') {
            unsigned long step;
            int off;
            sscanf(ln, "%lu%n", &step, &off);
            if (step < H) snprintf(lines[step], sizeof *lines, "%s", ln + off + 1);
        }
    }
    CHECK_EQ(checked, H);
    free(lines);
    free(t);
    free(r.text);
}

TEST(records_are_the_strict_future_minima) {
    enum { H = 400, CONF = 150 };
    traced r = trace(R10 " X", H, CONF, NULL, 0, NULL);
    CHECK_EQ(r.status, AV_FUEL);
    unsigned L[H];
    size_t n = 0;
    char *R = NULL, *C = NULL, *save = NULL;
    for (char *ln = strtok_r(r.text, "\n", &save); ln; ln = strtok_r(NULL, "\n", &save)) {
        if (ln[0] >= '0' && ln[0] <= '9' && n < H) {
            unsigned long step;
            unsigned len;
            sscanf(ln, "%lu %u", &step, &len);
            L[n++] = len;
        } else if (ln[0] == 'R') R = ln;
        else if (ln[0] == 'C') C = ln;
    }
    CHECK_EQ(n, H);
    char want_r[8192] = "R", want_c[8192] = "C";
    unsigned minL = UINT32_MAX;
    bool rec[H] = { 0 };
    for (size_t i = H; i-- > 0;)
        if (L[i] < minL) { rec[i] = true; minL = L[i]; }
    for (size_t i = 0; i < H; i++) {
        if (!rec[i]) continue;
        size_t q = strlen(want_r);
        snprintf(want_r + q, sizeof want_r - q, " %zu", i);
        if (i + CONF <= H) {
            q = strlen(want_c);
            snprintf(want_c + q, sizeof want_c - q, " %zu", i);
        }
    }
    CHECK(R && strcmp(R, want_r) == 0);
    CHECK(C && strcmp(C, want_c) == 0);
    free(r.text);
}

/*  A window wider than the horizon confirms nothing, however wide: n + CONF
 *  is never formed, so SIZE_MAX cannot wrap into confirming every record. */
TEST(a_window_past_the_horizon_confirms_nothing) {
    const size_t wide[] = { 401, (size_t)1 << 40, SIZE_MAX - 1, SIZE_MAX };
    for (size_t k = 0; k < sizeof wide / sizeof *wide; k++) {
        traced r = trace(R10 " X", 400, wide[k], NULL, 0, NULL);
        CHECK_EQ(r.status, AV_FUEL);
        CHECK(strstr(r.text, "\nR ") != NULL);          /* records exist */
        CHECK(strstr(r.text, "\nC\n") != NULL);         /* none confirmed */
        CHECK(strstr(r.text, "\nK ") == NULL);
        free(r.text);
    }
}

TEST(census_dumps_are_the_frames_the_census_reads) {
    /* r10 X rides: no confirmed record has an X-headed item at or below
     * L-3 or at L-1, so the census reads frame n+1 of every one, for its
     * mint -- and nothing else is dumped */
    enum { H = 600, CONF = 150 };
    av_arena *a = av_arena_new(1u << 12);
    uint32_t t = av_parse(a, R10 " X", strlen(R10 " X"), NULL);
    av_trace *tr = av_trace_new(a, "X", false, NULL);
    CHECK(av_trace_check(tr, a, t));
    av_opts o = av_opts_default();
    o.strategy = AV_COPY;
    o.whnf_only = true;
    o.no_collect = true;
    o.max_steps = H;
    o.trace = tr;
    av_result r = av_reduce(a, t, &o);
    CHECK_EQ(r.status, AV_FUEL);
    uint64_t *rec = NULL, *cen = NULL;
    size_t nr = av_trace_record_steps(tr, CONF, &rec);
    size_t nc = av_trace_census_steps(tr, CONF, &cen);
    CHECK(nr > 0 && nr % 2 == 0);
    CHECK_EQ(nc, nr / 2);
    for (size_t i = 0; i < nc && i < nr / 2; i++) CHECK_EQ(cen[i], rec[2 * i + 1]);
    free(rec);
    free(cen);
    av_trace_free(tr);
    av_arena_free(a);
    /* the frozen cases, a deep item read at n and an item at L-1 read at
     * n+1, are checked by tests/hider/parity.py verdict on every frozen
     * term of size <= 12, whose verdicts need exactly these frames */
}

TEST(a_dumped_frame_reads_back_in_the_dag_form) {
    uint64_t at[1] = { 40 };
    traced r = trace(R10 " X", 100, 0, at, 1, NULL);
    /* the node table and frame 40 as one DAG line: S applied to the items */
    size_t cap = r.len * 4 + 4096;
    char *dagline = malloc(cap);
    size_t k = (size_t)snprintf(dagline, cap, "dag");
    char *save = NULL, *frame = NULL;
    for (char *ln = strtok_r(r.text, "\n", &save); ln; ln = strtok_r(NULL, "\n", &save)) {
        if (ln[0] == 'd') k += (size_t)snprintf(dagline + k, cap - k, " %s", ln + 2);
        else if (ln[0] == 'f') frame = ln;
    }
    CHECK(frame != NULL);
    /* S's node is in the table; fold the items onto it */
    unsigned long step;
    int off;
    sscanf(frame, "f %lu%n", &step, &off);
    unsigned prev = 0, v, next = 1000000;
    int n;
    char *q = frame + off;
    while (sscanf(q, " %u%n", &v, &n) == 1) {
        k += (size_t)snprintf(dagline + k, cap - k, " %u=%u.%u", next, prev, v);
        prev = next++;
        q += n;
    }
    snprintf(dagline + k, cap - k, " @%u", prev);
    av_arena *a = av_arena_new(1u << 12);
    const char *msg = NULL;
    uint32_t t = av_parse_dag(a, dagline, strlen(dagline), &msg);
    CHECK(t != AV_NONE);
    /* the state reached at step 40 by stepping, against it */
    uint32_t src = av_parse(a, R10 " X", strlen(R10 " X"), NULL);
    av_opts o = av_opts_default();
    o.strategy = AV_COPY;
    o.whnf_only = true;
    o.no_collect = true;
    o.max_steps = 40;
    av_result res = av_reduce(a, src, &o);
    CHECK_EQ(res.status, AV_FUEL);
    CHECK_EQ(av_equal(a, t, res.term, 10000000), 1);
    av_arena_free(a);
    free(dagline);
    free(r.text);
}

TEST(k_and_i_are_refused) {
    bool refused = false;
    traced r = trace("S K S X", 10, 0, NULL, 0, &refused);
    CHECK(refused);
    free(r.text);
    traced s = trace("S S S X", 10, 0, NULL, 0, &refused);
    CHECK(!refused);
    free(s.text);
}

/*  The DAG form refuses what it cannot read exactly: ids at or past
 *  2^64-1 (they would wrap or alias the table's empty key), text after
 *  the root, a second root, an id defined twice, a forward reference. */
TEST(malformed_dag_terms_are_refused) {
    const char *bad[] = {
        "dag 18446744073709551615=S @18446744073709551615",
        "dag 99999999999999999999999=S @99999999999999999999999",
        "dag 18446744073709551616=S 0=K 1=0.0 @0",
        "dag 1=S @1 2=K @2",
        "dag 1=S 2=1.1 @2\nS K\n",
        "dag 1=S 2=1.1 @2 junk",
        "dag 1=S 1=K @1",
        "dag 1=2.1 @1",
        "dag 1=S",
        "dag ",
    };
    av_arena *a = av_arena_new(1u << 12);
    for (size_t i = 0; i < sizeof bad / sizeof *bad; i++) {
        const char *msg = NULL;
        uint32_t t = av_parse_dag(a, bad[i], strlen(bad[i]), &msg);
        CHECK(t == AV_NONE && msg != NULL);
        if (t != AV_NONE) fprintf(stderr, "  accepted: %s\n", bad[i]);
    }
    const char *good[] = {
        "dag 18446744073709551614=S @18446744073709551614",
        "dag 1=S 2=1.1 @2\n\n",
    };
    for (size_t i = 0; i < sizeof good / sizeof *good; i++) {
        const char *msg = NULL;
        CHECK(av_parse_dag(a, good[i], strlen(good[i]), &msg) != AV_NONE);
    }
    av_arena_free(a);
}

TEST(a_long_run_stays_linear) {
    clock_t t0 = clock();
    traced r = trace(R10 " X", 100000, 150, NULL, 0, NULL);
    double s = (double)(clock() - t0) / CLOCKS_PER_SEC;
    CHECK_EQ(r.status, AV_FUEL);
    CHECK_EQ(r.steps, 100000);
    CHECK(s < 20.0);                /* under sanitizers; well under a second released */
    free(r.text);
}

TEST_MAIN(
    TEST_CASE(hand_traced_runs_give_their_lines),
    TEST_CASE(an_open_at_the_last_step_is_open),
    TEST_CASE(every_line_equals_a_recount_from_its_frame),
    TEST_CASE(records_are_the_strict_future_minima),
    TEST_CASE(a_window_past_the_horizon_confirms_nothing),
    TEST_CASE(census_dumps_are_the_frames_the_census_reads),
    TEST_CASE(a_dumped_frame_reads_back_in_the_dag_form),
    TEST_CASE(k_and_i_are_refused),
    TEST_CASE(malformed_dag_terms_are_refused),
    TEST_CASE(a_long_run_stays_linear)
)
