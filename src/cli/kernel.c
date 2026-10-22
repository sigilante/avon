/**  kernel.c
 *
 *  avon boot | poke | peek | load: a kernel in a pier directory.
 */

#include "cli.h"

static uint8_t *read_file(const char *path, size_t *len) {
    FILE *f = fopen(path, "rb");
    if (!f) { perror(path); return NULL; }
    char *b = slurp(f, len);
    fclose(f);
    return (uint8_t *)b;
}

/*  The default initial subject: skijack's standard subject is unbuilt,
 *  so until it is, a program is applied to I. */
static uint8_t *default_subject(size_t *len) {
    av_arena *a = av_arena_new(0);
    av_buf b = { 0 };
    const char *msg = NULL;
    uint8_t *out = a && av_jam(a, AV_NODE_I, 100, &b, &msg) ? (uint8_t *)b.s : NULL;
    if (out) *len = b.len;
    av_arena_free(a);
    return out;
}

static void print_term(av_arena *a, uint32_t t, size_t budget) {
    av_buf b = { 0 };
    bool whole = av_print(a, t, budget, &b);
    printf("%s%s\n", b.s ? b.s : "", whole ? "" : " ...");
    av_buf_free(&b);
}

/*  A value as data: its normal form, reduced in copy mode, which writes
 *  nothing the kernel shares; the term as it stands if there is none
 *  within a million contractions. */
static void print_value(av_arena *a, uint32_t t, size_t budget) {
    av_opts o = av_opts_default();
    o.strategy = AV_COPY;
    o.max_steps = 1000000;
    av_root_push(a, &t);
    av_result r = av_reduce(a, t, &o);
    av_root_pop(a);
    if (r.status == AV_NORMAL) print_term(a, r.term, budget);
    else { printf("(no normal form within 1,000,000) "); print_term(a, t, budget); }
}

/*  Each event a poke applies, as it applies: the outside event, then its
 *  entropy replies. */
typedef struct { av_pier *p; size_t budget; } event_out;

static void print_event(void *ctx, uint64_t event, uint64_t steps, uint32_t effects, bool reply) {
    const event_out *eo = ctx;
    printf("event %llu, %s%llu contractions; effects: ", (unsigned long long)event,
           reply ? "an entropy reply, " : "", (unsigned long long)steps);
    print_value(av_pier_kernel(eo->p)->a, effects, eo->budget);
}

/*  The cap's note, if the last poke reached it, and why its replies
 *  stopped short, if they did: false then, the event itself applied. */
/*  A persistent-arena pier whose image did not commit after an event: the
 *  event applied and is logged, so it is not to be poked again; the next
 *  commit or a reopen carries it. */
static bool report_commit(const av_pier *p) {
    const char *c = av_pier_commit_error(p);
    if (c) fprintf(stderr, "avon: the event applied and is logged, but the image did not commit "
                           "(%s); do not poke it again: a reopen replays it\n", c);
    return !c;
}

static bool report_unanswered(const av_pier *p) {
    uint64_t left;
    av_pier_replies(p, &left);
    if (left)
        printf("entropy: %d replies drawn, the most one event may; %llu requests left unanswered\n",
               AV_ENY_MAX, (unsigned long long)left);
    const char *e = av_pier_entropy_error(p);
    if (e) fprintf(stderr, "avon: entropy, after the event applied: %s\n", e);
    return report_commit(p) && !e;
}

/*  avon boot | poke | peek | load: a kernel in a pier directory. */
int kernel_main(int argc, char **argv) {
    const char *cmd = argv[1], *pier = NULL, *subject_file = NULL, *eny_file = NULL;
    bool eny = false;
    const char *files[256];
    int nf = 0;
    bool snap = false, pma = false;
    uint64_t budget = 100000, v;
    bool budget_set = false;
    av_opts o = av_opts_default();
    o.strategy = AV_SHARE;                      /* kernel loops share */
    o.max_steps = 100000000;
    for (int i = 2; i < argc; i++) {
        const char *s = argv[i];
        if (strncmp(s, "--pier=", 7) == 0 && s[7]) pier = s + 7;
        else if (strncmp(s, "--subject=", 10) == 0 && s[10]) subject_file = s + 10;
        else if (strcmp(s, "--strategy=copy") == 0) o.strategy = AV_COPY;
        else if (strcmp(s, "--strategy=share") == 0) o.strategy = AV_SHARE;
        else if (strncmp(s, "--fuel=", 7) == 0 && number(s + 7, &v)) o.max_steps = v;
        else if (strncmp(s, "--budget=", 9) == 0 && number(s + 9, &v)) budget = v, budget_set = true;
        else if (strcmp(s, "--snapshot") == 0) snap = true;
        else if (strcmp(s, "--pma") == 0) pma = true;
        else if (strcmp(s, "--entropy") == 0) eny = true;
        else if (strncmp(s, "--entropy=", 10) == 0 && s[10]) { eny = true; eny_file = s + 10; }
        else if (s[0] != '-' && nf < 256) files[nf++] = s;
        else return usage();
    }
    /* refuse an option the command would ignore: boot takes no snapshot,
     * and without a pier makes no arena, answers no entropy and prints no
     * event; the others reopen the pier as it was made, and only load reads
     * a subject */
    bool boot = strcmp(cmd, "boot") == 0;
    const char *idle = snap && boot ? "--snapshot"
                     : pma && !boot ? "--pma"
                     : subject_file && !boot && strcmp(cmd, "load") != 0 ? "--subject"
                     : boot && !pier && pma ? "--pma"
                     : boot && !pier && eny ? "--entropy"
                     : boot && pier && !eny && budget_set ? "--budget"
                     : NULL;
    if (idle) {
        fprintf(stderr, "avon: %s has no effect on %s%s\n", idle, cmd,
                !boot || strcmp(idle, "--snapshot") == 0 ? ""
                : pier ? " without --entropy" : " without --pier");
        return 2;
    }
    const char *err = NULL;
    size_t ns = 0;
    uint8_t *subject = subject_file ? read_file(subject_file, &ns) : default_subject(&ns);
    if (!subject) return 1;
    int rc = 1;
    if (strcmp(cmd, "boot") == 0) {
        if (nf != 1) { free(subject); return usage(); }
        size_t np;
        uint8_t *pill = read_file(files[0], &np);
        if (!pill) { free(subject); return 1; }
        if (pier) {
            av_pier *p = av_pier_new_ex(pier, pill, np, subject, ns, &o,
                                        (pma ? AV_PIER_PMA : 0u) | (eny ? AV_PIER_ENTROPY : 0u) |
                                            (eny_file ? AV_PIER_ENTROPY_FILE : 0u), &err);
            if (!p) fprintf(stderr, "avon: %s: %s\n", pier, err);
            else {
                printf("booted a kernel in %s%s\n", pier, pma ? ", on a persistent arena" : "");
                rc = 0;
                if (eny) {
                    event_out eo = { p, budget };
                    av_pier_on_event(p, print_event, &eo);
                    if (!av_pier_entropy(p, eny_file, &err)) {
                        fprintf(stderr, "avon: %s: entropy: %s\n", pier, err);
                        rc = 1;
                    } else if (!report_unanswered(p)) {
                        rc = 1;                 /* as poke: a file run out stops it */
                    }
                }
            }
            av_pier_free(p);
        } else {                                /* boot once, and show the value */
            av_arena *a = av_arena_new(ARENA_START);
            uint32_t pt = av_cue(a, pill, np, &err), st = av_cue(a, subject, ns, &err);
            av_kernel k;
            bool is_kernel;
            uint32_t value;
            av_result r;
            if (pt == AV_NONE || st == AV_NONE) fprintf(stderr, "avon: %s\n", err);
            else if (av_kernel_boot(&k, a, pt, st, &o, &is_kernel, &value, &r) != AV_WHNF)
                fprintf(stderr, "avon: %s after %llu contractions\n", av_status_name(r.status),
                        (unsigned long long)r.steps);
            else {
                printf("%s, %llu contractions\n", is_kernel ? "a kernel" : "not a kernel: the value",
                       (unsigned long long)r.steps);
                if (!is_kernel) print_term(a, value, budget);
                else av_kernel_free(&k);
                rc = 0;
            }
            av_arena_free(a);
        }
        free(pill);
        free(subject);
        return rc;
    }
    if (!pier || nf < 1) { free(subject); return usage(); }
    av_pier *p = av_pier_open(pier, &o, &err);
    if (!p) { fprintf(stderr, "avon: %s: %s\n", pier, err); free(subject); return 1; }
    av_kernel *k = av_pier_kernel(p);
    event_out eo = { p, budget };
    av_pier_on_event(p, print_event, &eo);
    if (eny && !av_pier_entropy(p, eny_file, &err)) {
        fprintf(stderr, "avon: %s: %s\n", pier, err);
        av_pier_free(p);
        free(subject);
        return 1;
    }
    rc = 0;
    for (int i = 0; i < nf && rc == 0; i++) {
        size_t n;
        uint8_t *b = read_file(files[i], &n);
        if (!b) { rc = 1; break; }
        if (strcmp(cmd, "poke") == 0) {
            uint32_t eff;
            av_result r;
            if (av_pier_poke(p, b, n, &eff, &r, &err) != AV_WHNF) {
                fprintf(stderr, "avon: %s: %s (%s)\n", files[i], err, av_status_name(r.status));
                rc = 1;
            } else {
                if (!report_unanswered(p)) rc = 1;  /* the events printed as they applied */
            }
        } else if (strcmp(cmd, "peek") == 0) {
            uint32_t path = av_cue(k->a, b, n, &err), ans;
            av_result r;
            if (path == AV_NONE || av_kernel_peek(k, path, &ans, &r) != AV_WHNF) {
                fprintf(stderr, "avon: %s: %s\n", files[i], path == AV_NONE ? err : "no answer");
                rc = 1;
            } else {
                printf("%llu contractions: ", (unsigned long long)r.steps);
                print_value(k->a, ans, budget);
            }
        } else if (strcmp(cmd, "load") == 0) {
            if (!av_pier_load(p, b, n, subject, ns, &err)) {
                fprintf(stderr, "avon: %s: %s\n", files[i], err);
                rc = 1;
            } else {
                printf("event %llu: loaded the kernel that %s boots to\n",
                       (unsigned long long)k->events, files[i]);
                if (!report_commit(p)) rc = 1;
            }
        } else {
            rc = 2;
        }
        free(b);
    }
    if (rc == 0 && snap && !av_pier_snapshot(p, &err)) {
        fprintf(stderr, "avon: snapshot: %s\n", err);
        rc = 1;
    }
    av_pier_free(p);
    free(subject);
    return rc == 2 ? usage() : rc;
}
