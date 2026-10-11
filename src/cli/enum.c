/**  enum.c
 *
 *  avon enum: closed S-terms, streamed.
 */

#include "cli.h"

/*  avon enum: closed S-terms, streamed.
 *
 *  enum N [--start=K] [--count=M]   every closed term of size N (leaves), in
 *      the order of the census's V.trees(n): the left size from 1 to N-1,
 *      then the left tree, then the right; the trees below N are kept, one
 *      node each, and size N is printed as it is made.
 *  enum --base=FILE --shape=SHAPES  for every ordered pair (a, q) of the
 *      file's terms, in file order, each shape: sxy  S a q;  ssaq  S (S a) q;
 *      hide  S (S (S (S S) (S a))) q.
 */
#define ENUM_MAX 20

int enum_main(int argc, char **argv) {
    uint64_t N = 0, start = 0, count = UINT64_MAX, v;
    const char *base = NULL, *shapes = NULL;
    for (int i = 2; i < argc; i++) {
        const char *s = argv[i];
        if (strncmp(s, "--start=", 8) == 0 && number(s + 8, &v)) start = v;
        else if (strncmp(s, "--count=", 8) == 0 && number(s + 8, &v)) count = v;
        else if (strncmp(s, "--base=", 7) == 0 && s[7]) base = s + 7;
        else if (strncmp(s, "--shape=", 8) == 0 && s[8]) shapes = s + 8;
        else if (s[0] != '-' && number(s, &v) && v >= 1) N = v;
        else return usage();
    }
    if (N > ENUM_MAX) {
        /* size N pairs every tree below it, each kept as a node: 6.4e8
         * nodes (6 GB) for N = 20, 2.4e9 for N = 21, past the arena's 2^30 */
        fprintf(stderr, "avon: enum takes sizes 1 to %d\n", ENUM_MAX);
        return 2;
    }
    if (!N == !base || (base && !shapes)) return usage();
    av_arena *a = av_arena_new(1u << 20);
    if (!a) { fprintf(stderr, "avon: out of memory\n"); return 1; }
    av_buf b = { 0 };
    uint64_t emitted = 0, index = 0;
    int rc = 0;
    bool said = false;              /* a specific error is already printed */
    uint32_t *trees[ENUM_MAX + 1] = { 0 };     /* trees[k]: every tree of size k < N */
#define EMIT(node)                                                              \
    do {                                                                        \
        if (index >= start && emitted < count) {                                \
            b.len = 0;                                                          \
            if (!av_print(a, (node), 1u << 20, &b)) { rc = 1; goto done; }      \
            fwrite(b.s, 1, b.len, stdout);                                      \
            fputc('\n', stdout);                                                \
            if (++emitted % 100000 == 0)                                        \
                fprintf(stderr, "enum: %llu terms\n", (unsigned long long)emitted); \
        }                                                                       \
        index++;                                                                \
    } while (0)
    if (N) {
        /* trees[k] in the census's order */
        size_t ntrees[ENUM_MAX + 1] = { 0 };
        trees[1] = malloc(sizeof **trees);
        if (!trees[1]) { rc = 1; goto done; }
        trees[1][0] = AV_NODE_S;
        ntrees[1] = 1;
        for (uint64_t n = 2; n < N; n++) {
            size_t total = 0;
            for (uint64_t k = 1; k < n; k++) total += ntrees[k] * ntrees[n - k];
            trees[n] = malloc((total ? total : 1) * sizeof **trees);
            if (!trees[n]) { rc = 1; goto done; }
            size_t m = 0;
            for (uint64_t k = 1; k < n; k++)
                for (size_t l = 0; l < ntrees[k]; l++)
                    for (size_t r = 0; r < ntrees[n - k]; r++) {
                        uint32_t x = av_app(a, trees[k][l], trees[n - k][r]);
                        if (x == AV_NONE) { rc = 1; goto done; }
                        trees[n][m++] = x;
                    }
            ntrees[n] = m;
        }
        if (N == 1) {
            EMIT(AV_NODE_S);
        } else {
            for (uint64_t k = 1; k < N && emitted < count; k++)
                for (size_t l = 0; l < ntrees[k] && emitted < count; l++)
                    for (size_t r = 0; r < ntrees[N - k] && emitted < count; r++) {
                        if (index < start) { index++; continue; }
                        uint32_t used = a->used;
                        uint32_t x = av_app(a, trees[k][l], trees[N - k][r]);
                        if (x == AV_NONE) { rc = 1; goto done; }
                        EMIT(x);
                        a->used = used;         /* the node is printed: reuse it */
                    }
        }
    } else {
        FILE *f = fopen(base, "rb");
        if (!f) { perror(base); said = true; rc = 1; goto done; }
        uint32_t *terms = NULL;
        size_t nt = 0, tcap = 0;
        char *line = NULL;
        size_t lcap = 0, lineno = 0;
        ssize_t n;
        while ((n = getline(&line, &lcap, f)) > 0) {
            size_t len = (size_t)n;
            lineno++;
            while (len && (line[len - 1] == '\n' || line[len - 1] == '\r' || line[len - 1] == ' '))
                len--;
            if (!len) continue;
            uint32_t t = load(a, line, len);
            if (t == AV_NONE) {
                fprintf(stderr, "avon: %s: line %zu is not a term\n", base, lineno);
                said = true;
                rc = 1;
                break;
            }
            if (nt == tcap) {
                uint32_t *q = realloc(terms, (tcap = tcap ? 2 * tcap : 64) * sizeof *q);
                if (!q) { rc = 1; break; }
                terms = q;
            }
            terms[nt++] = t;
        }
        free(line);
        fclose(f);
        if (rc == 0 && nt == 0) fprintf(stderr, "avon: %s holds no terms\n", base);
        uint32_t S = AV_NODE_S, SS = av_app(a, S, S);
        for (size_t i = 0; rc == 0 && i < nt; i++)
            for (size_t j = 0; rc == 0 && j < nt && emitted < count; j++) {
                const char *q = shapes;
                while (*q && rc == 0) {
                    const char *e = strchr(q, ',');
                    size_t len = e ? (size_t)(e - q) : strlen(q);
                    uint32_t x = AV_NONE, p = terms[i], r = terms[j];
                    uint32_t used = a->used;
                    if (len == 3 && memcmp(q, "sxy", 3) == 0)
                        x = av_app(a, av_app(a, S, p), r);
                    else if (len == 4 && memcmp(q, "ssaq", 4) == 0)
                        x = av_app(a, av_app(a, S, av_app(a, S, p)), r);
                    else if (len == 4 && memcmp(q, "hide", 4) == 0)
                        x = av_app(a, av_app(a, S, av_app(a, S, av_app(a, av_app(a, S, SS),
                                                                     av_app(a, S, p)))), r);
                    else {
                        fprintf(stderr, "avon: unknown shape %.*s\n", (int)len, q);
                        said = true;
                        rc = 1;
                        break;
                    }
                    if (x == AV_NONE) { rc = 1; break; }
                    EMIT(x);
                    a->used = used;
                    q += len;
                    if (*q == ',') q++;
                }
            }
        free(terms);
    }
#undef EMIT
done:
    for (int k = 0; k <= ENUM_MAX; k++) free(trees[k]);
    if (rc && !said && !ferror(stdout))
        fprintf(stderr, "avon: enum stopped: out of memory or nodes\n");
    fflush(stdout);
    av_buf_free(&b);
    av_arena_free(a);
    return rc;
}
