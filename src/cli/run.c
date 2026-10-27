/**  run.c
 *
 *  avon run: a program.  Plain, it is `avon reduce`: the term reduced and
 *  its normal form printed.  With --kernel, FILE holds a kernel, which runs
 *  with drivers (DESIGN.md §9.2): its cards read standard input, write
 *  standard output and error, read the environment, and set the exit
 *  status.  The log is in memory; nothing is kept.
 */

#include "cli.h"

int program_main(int argc, char **argv) {
    bool kernel = false;
    for (int i = 2; i < argc && argv[i][0] == '-'; i++)
        if (strcmp(argv[i], "--kernel") == 0) kernel = true;
    if (!kernel) {
        argv[1] = "reduce";                     /* a plain program */
        return term_main(argc, argv);
    }
    av_opts o = av_opts_default();
    o.strategy = AV_SHARE;                      /* kernel loops share */
    o.max_steps = 100000000;
    av_run d = { .fd = { 0, 1, 2 } };
    const char *file = NULL;
    uint64_t v;
    int i = 2;
    for (; i < argc && argv[i][0] == '-'; i++) {
        const char *s = argv[i];
        if (strcmp(s, "--kernel") == 0) continue;
        else if (strcmp(s, "--strategy=copy") == 0) o.strategy = AV_COPY;
        else if (strcmp(s, "--strategy=share") == 0) o.strategy = AV_SHARE;
        else if (strncmp(s, "--fuel=", 7) == 0 && number(s + 7, &v)) o.max_steps = v;
        else if (strcmp(s, "--entropy") == 0) d.entropy = true;
        else if (strncmp(s, "--entropy=", 10) == 0 && s[10]) d.entropy = true, d.entropy_file = s + 10;
        else if (strcmp(s, "--") == 0) { i++; break; }
        else return usage();
    }
    if (i >= argc) return usage();
    file = argv[i];
    d.argc = argc - i;                          /* the kernel's name first */
    d.argv = argv + i;
    FILE *f = fopen(file, "rb");
    if (!f) { perror(file); return 1; }
    size_t len;
    char *src = slurp(f, &len);
    fclose(f);
    if (!src) { fprintf(stderr, "avon: out of memory\n"); return 1; }
    av_arena *a = av_arena_new(ARENA_START);
    uint32_t t = a ? load(a, src, len) : AV_NONE;
    free(src);
    if (t == AV_NONE) { av_arena_free(a); return 1; }
    /* the term as it stands, unreduced, as the reference host holds it:
     * its first poke reduces it, and the step count includes that */
    av_opts po = o;                             /* the shape's probe, not the run's fuel */
    po.max_steps = 1000000;
    if (!av_is_kernel(a, t, &po)) {
        fprintf(stderr, "avon: %s: not a kernel [[poke [peek load]] state]\n", file);
        av_arena_free(a);
        return 1;
    }
    av_kernel k;
    av_result r;
    av_kernel_adopt(&k, a, t, &o);
    const char *err = NULL;
    int rc = 0;
    if (av_run_kernel(&k, &d, &r, &err) != AV_WHNF) {
        fprintf(stderr, "avon: %s: %s (%s, poke %llu)\n", file, err, av_status_name(r.status),
                (unsigned long long)d.pokes + 1);
        rc = 1;
    } else {
        rc = d.status;
    }
    av_kernel_free(&k);
    av_arena_free(a);
    return rc;
}

/*  avon boot --drivers --pier=DIR [options] FILE [ARG...]: the kernel run
 *  durably, in a new pier.  Without FILE, the pier's run reopened: its log
 *  replayed, and the run continued from where the log ends. */
int boot_drivers_main(int argc, char **argv) {
    av_opts o = av_opts_default();
    o.strategy = AV_SHARE;                      /* kernel loops share */
    o.max_steps = 100000000;
    av_run d = { .fd = { 0, 1, 2 } };
    const char *pier = NULL;
    bool eny = false, strategy_set = false;
    uint64_t v;
    int i = 2;
    for (; i < argc && argv[i][0] == '-'; i++) {
        const char *s = argv[i];
        if (strcmp(s, "--drivers") == 0) continue;
        else if (strncmp(s, "--pier=", 7) == 0 && s[7]) pier = s + 7;
        else if (strcmp(s, "--strategy=copy") == 0) o.strategy = AV_COPY, strategy_set = true;
        else if (strcmp(s, "--strategy=share") == 0) o.strategy = AV_SHARE, strategy_set = true;
        else if (strncmp(s, "--fuel=", 7) == 0 && number(s + 7, &v)) o.max_steps = v;
        else if (strcmp(s, "--entropy") == 0) eny = true;
        else if (strncmp(s, "--entropy=", 10) == 0 && s[10]) eny = true, d.entropy_file = s + 10;
        else if (strcmp(s, "--") == 0) { i++; break; }
        else return usage();
    }
    if (!pier) return usage();
    const char *err = NULL;
    av_pier *p = NULL;
    if (i < argc) {                             /* a new pier */
        const char *file = argv[i];
        d.argc = argc - i;                      /* the kernel's name first */
        d.argv = argv + i;
        FILE *f = fopen(file, "rb");
        if (!f) { perror(file); return 1; }
        size_t len;
        char *src = slurp(f, &len);
        fclose(f);
        if (!src) { fprintf(stderr, "avon: out of memory\n"); return 1; }
        av_buf jam = { 0 };
        const uint8_t *skit = (const uint8_t *)src;
        size_t nskit = len;
        if (len < 4 || memcmp(src, "SKIT", 4) != 0) {
            /* a printed kernel, jammed for the pier: a tree, so bounded */
            av_arena *a = av_arena_new(ARENA_START);
            uint32_t t = a ? load(a, src, len) : AV_NONE;
            bool ok = t != AV_NONE && av_jam(a, t, (size_t)1 << 26, &jam, &err);
            av_arena_free(a);
            if (!ok) {
                if (t != AV_NONE) fprintf(stderr, "avon: %s: too large to jam: give it as SKIT\n", file);
                free(src);
                av_buf_free(&jam);
                return 1;
            }
            skit = (const uint8_t *)jam.s;
            nskit = jam.len;
        }
        unsigned flags = eny ? (d.entropy_file ? AV_PIER_ENTROPY_FILE : AV_PIER_ENTROPY) : 0u;
        p = av_pier_new_drivers(pier, skit, nskit, &o, flags, &d, &err);
        free(src);
        av_buf_free(&jam);
    } else {                                    /* the pier's run, reopened */
        p = av_pier_open(pier, &o, &err);
        if (p && !av_pier_is_drivers(p)) {
            av_pier_free(p);
            p = NULL;
            err = "the pier was not booted with --drivers";
        } else if (p && strategy_set && av_pier_strategy(p) != o.strategy) {
            av_pier_free(p);
            p = NULL;
            err = "the pier runs in the other strategy: its run replays as it ran";
        } else if (p && eny && !d.entropy_file) {
            av_pier_free(p);
            p = NULL;
            err = "--entropy chooses nothing on a reopened pier; --entropy=FILE gives its file";
        }
    }
    if (!p) { fprintf(stderr, "avon: %s: %s\n", pier, err); return 1; }
    av_result r;
    int rc;
    if (av_pier_drive(p, &d, &r, &err) != AV_WHNF) {
        fprintf(stderr, "avon: %s: %s (%s, poke %llu)\n", pier, err, av_status_name(r.status),
                (unsigned long long)d.pokes + 1);
        rc = 1;
    } else {
        rc = d.status;
    }
    av_pier_free(p);
    return rc;
}
