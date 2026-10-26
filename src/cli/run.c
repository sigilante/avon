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
    if (!av_is_kernel(a, t, &o)) {
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
