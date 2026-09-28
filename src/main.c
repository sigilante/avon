/**  main.c
 *
 *  The avon command.
 *
 *      avon reduce [options] [FILE]   reduce one term; print status, steps,
 *                                     and the term reached
 *      avon batch  [options]          reduce each stdin line; print one
 *                                     "STATUS steps term" line per term
 *      avon jam    [FILE]             printed form to a SKIT container
 *      avon cue    [FILE]             SKIT container to printed form
 *      avon prefix [FILE]             the term in prefix form (` for application)
 *      avon witness [--rows=N] [--cells=N] [FILE]
 *                                     the witness strategy's table, for
 *                                     lean-ski's aircheck and plonky3 (§17)
 *      avon --version
 *
 *  A FILE may be in the printed form, a SKIT container (docs/DESIGN.md
 *  §4.2), or the prefix form, told apart by a magic or a leading `.  Options: --strategy=copy|share
 *  (default share), --whnf, --fuel=N, --max-nodes=N, --budget=N (nodes
 *  printed or jammed; default 1000000), --allow-bird-atoms (§4.3).
 */

#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "avon.h"

#define AVON_VERSION "0.1.0"

typedef struct {
    av_opts     o;
    size_t      budget;
    bool        birds;
    uint64_t    rows, cells;      /* witness budgets */
    const char *file;
} args;

static int usage(void) {
    fprintf(stderr,
        "usage: avon reduce [--strategy=copy|share] [--whnf] [--fuel=N]\n"
        "                   [--max-nodes=N] [--budget=N] [FILE]\n"
        "       avon batch  [same options]\n"
        "       avon jam    [--budget=N] [FILE]\n"
        "       avon cue    [--budget=N] [FILE]\n"
        "       avon prefix [FILE]\n"
        "       avon witness [--rows=N] [--cells=N] [FILE]\n"
        "       (all accept --allow-bird-atoms)\n"
        "       avon --version\n");
    return 2;
}

static bool number(const char *s, uint64_t *out) {
    char *end;
    errno = 0;
    unsigned long long v = strtoull(s, &end, 10);
    if (errno || end == s || *end) return false;
    *out = v;
    return true;
}

static bool parse_args(int argc, char **argv, args *g) {
    g->o = av_opts_default();
    g->budget = 1000000;
    g->birds = false;
    g->rows = 1u << 21;          /* bench/plonky3's MAX_LOG_HEIGHT */
    g->cells = 1u << 21;
    g->file = NULL;
    for (int i = 2; i < argc; i++) {
        const char *s = argv[i];
        uint64_t v;
        if (strcmp(s, "--strategy=copy") == 0)       g->o.strategy = AV_COPY;
        else if (strcmp(s, "--strategy=share") == 0) g->o.strategy = AV_SHARE;
        else if (strcmp(s, "--whnf") == 0)           g->o.whnf_only = true;
        else if (strcmp(s, "--allow-bird-atoms") == 0) g->birds = true;
        else if (strncmp(s, "--fuel=", 7) == 0 && number(s + 7, &v))
            g->o.max_steps = v;
        else if (strncmp(s, "--max-nodes=", 12) == 0 && number(s + 12, &v)
                 && v <= AV_MAX_NODES)
            g->o.max_nodes = (uint32_t)v;
        else if (strncmp(s, "--budget=", 9) == 0 && number(s + 9, &v))
            g->budget = (size_t)v;
        else if (strncmp(s, "--rows=", 7) == 0 && number(s + 7, &v)
                 && v <= AV_MAX_NODES)
            g->rows = v;
        else if (strncmp(s, "--cells=", 8) == 0 && number(s + 8, &v)
                 && v <= AV_MAX_NODES)
            g->cells = v;
        else if (s[0] != '-' && !g->file) g->file = s;
        else return false;
    }
    return true;
}

static char *slurp(FILE *f, size_t *len) {
    size_t cap = 1 << 16, n = 0;
    char *s = malloc(cap);
    if (!s) return NULL;
    for (;;) {
        n += fread(s + n, 1, cap - n, f);
        if (n < cap) break;
        char *p = realloc(s, cap *= 2);
        if (!p) { free(s); return NULL; }
        s = p;
    }
    *len = n;
    return s;
}

/* A term from either format; reports its own errors. */
static uint32_t load(av_arena *a, const char *src, size_t len) {
    size_t lead = 0;
    while (lead < len && (src[lead] == ' ' || src[lead] == '\n' ||
                          src[lead] == '\r' || src[lead] == '\t'))
        lead++;
    if (lead < len && src[lead] == '`') {
        const char *msg = NULL;
        uint32_t t = av_parse_prefix(a, src, len, &msg);
        if (t == AV_NONE) fprintf(stderr, "avon: bad prefix term: %s\n", msg);
        return t;
    }
    if (len >= 4 && memcmp(src, "SKIT", 4) == 0) {
        const char *msg = NULL;
        uint32_t t = av_cue(a, (const uint8_t *)src, len, &msg);
        if (t == AV_NONE) fprintf(stderr, "avon: bad container: %s\n", msg);
        return t;
    }
    av_parse_error err = { 0, NULL };
    uint32_t t = av_parse(a, src, len, &err);
    if (t == AV_NONE)
        fprintf(stderr, "avon: parse error at %zu: %s\n", err.pos, err.msg);
    return t;
}

static av_arena *new_arena(const args *g, uint32_t cap) {
    av_arena *a = av_arena_new(cap);
    if (!a) fprintf(stderr, "avon: out of memory\n");
    else a->allow_bird_atoms = g->birds;
    return a;
}

/* Reduce one term and print "STATUS steps term" (sep between). */
static int run_one(const args *g, const char *src, size_t len, char sep) {
    av_arena *a = new_arena(g, 1u << 16);
    if (!a) return 1;
    uint32_t t = load(a, src, len);
    if (t == AV_NONE) {
        av_arena_free(a);
        return 1;
    }
    av_result r = av_reduce(a, t, &g->o);
    av_buf b = { 0 };
    bool whole = r.term != AV_NONE && av_print(a, r.term, g->budget, &b);
    printf("%s %" PRIu64 "%c%s%s\n", av_status_name(r.status), r.steps, sep,
           b.s ? b.s : "", whole ? "" : " ...");
    av_buf_free(&b);
    av_arena_free(a);
    return 0;
}

int main(int argc, char **argv) {
    if (argc == 2 && strcmp(argv[1], "--version") == 0) {
        printf("avon %s\n", AVON_VERSION);
        return 0;
    }
    if (argc < 2) return usage();
    args g;
    if (!parse_args(argc, argv, &g)) return usage();

    const char *cmd = argv[1];
    if (strcmp(cmd, "reduce") == 0 || strcmp(cmd, "jam") == 0 ||
        strcmp(cmd, "cue") == 0 || strcmp(cmd, "prefix") == 0 ||
        strcmp(cmd, "witness") == 0) {
        FILE *f = g.file ? fopen(g.file, "rb") : stdin;
        if (!f) { perror(g.file); return 1; }
        size_t len;
        char *src = slurp(f, &len);
        if (f != stdin) fclose(f);
        if (!src) { fprintf(stderr, "avon: out of memory\n"); return 1; }
        int rc;
        if (strcmp(cmd, "reduce") == 0) {
            rc = run_one(&g, src, len, '\n');
        } else if (strcmp(cmd, "witness") == 0) {
            av_arena *a = new_arena(&g, 1u << 16);
            uint32_t t = a ? load(a, src, len) : AV_NONE;
            av_witness w;
            const char *msg = NULL;
            av_buf b = { 0 };
            rc = 1;
            if (t != AV_NONE) {
                av_status st = av_witness_run(a, t, (size_t)g.rows, (size_t)g.cells, &w, &msg);
                if (st != AV_WHNF) {
                    fprintf(stderr, "avon: no witness: %s\n", msg);
                } else if (!av_witness_table(a, t, &w, 4, &b)) {
                    fprintf(stderr, "avon: could not write the table\n");
                } else {
                    fwrite(b.s, 1, b.len, stdout);
                    fprintf(stderr, "contractions %llu rows %zu cells %zu loaded %zu\n",
                            (unsigned long long)w.contractions, w.nrows, w.nmem, w.loaded);
                    rc = 0;
                }
                av_witness_free(&w);
            }
            av_buf_free(&b);
            av_arena_free(a);
        } else if (strcmp(cmd, "prefix") == 0) {
            av_arena *a = new_arena(&g, 1u << 16);
            uint32_t t = a ? load(a, src, len) : AV_NONE;
            av_buf b = { 0 };
            rc = t != AV_NONE && av_prefix(a, t, g.budget, &b) ? 0 : 1;
            if (rc == 0) printf("%s\n", b.s);
            else if (t != AV_NONE) fprintf(stderr, "avon: node budget exceeded or not closed\n");
            av_buf_free(&b);
            av_arena_free(a);
        } else {
            av_arena *a = new_arena(&g, 1u << 16);
            uint32_t t = a ? load(a, src, len) : AV_NONE;
            av_buf b = { 0 };
            const char *msg = "node budget exceeded";
            bool ok = t != AV_NONE &&
                      (cmd[0] == 'j' ? av_jam(a, t, g.budget, &b, &msg)
                                     : av_print(a, t, g.budget, &b));
            if (ok && cmd[0] == 'j') fwrite(b.s, 1, b.len, stdout);
            else if (ok) printf("%s\n", b.s);
            else if (t != AV_NONE) fprintf(stderr, "avon: %s\n", msg);
            rc = ok ? 0 : 1;
            av_buf_free(&b);
            av_arena_free(a);
        }
        free(src);
        return rc;
    }
    if (strcmp(cmd, "batch") == 0) {
        char *line = NULL;
        size_t cap = 0;
        int rc = 0;
        ssize_t n;
        while ((n = getline(&line, &cap, stdin)) > 0) {
            if (run_one(&g, line, (size_t)n, ' ')) rc = 1;
            fflush(stdout);
        }
        free(line);
        return rc;
    }
    return usage();
}
