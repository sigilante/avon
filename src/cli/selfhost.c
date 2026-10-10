/**  selfhost.c
 *
 *  avon selfhost: the compiler's core as a term (docs/DESIGN.md §20.3),
 *  each call of a calls file checked against Python's by hash.
 */

#include "cli.h"

/*  avon selfhost DIR CALLS: every call of a calls file (tests/selfhost/
 *  export.py) through the compiler term DIR/abs.skit -- or its jet, with
 *  --jets -- decoded and compared with Python's result by hash. */
int selfhost_main(int argc, char **argv) {
    const char *dir = NULL, *calls = NULL;
    bool jets = false;
    uint64_t check = 0, every = 1, v;
    for (int i = 2; i < argc; i++) {
        const char *s = argv[i];
        if (strcmp(s, "--jets") == 0) jets = true;
        else if (strncmp(s, "--jet-check=", 12) == 0 && number(s + 12, &v)) check = v;
        else if (strncmp(s, "--every=", 8) == 0 && number(s + 8, &v) && v > 0) every = v;
        else if (s[0] != '-' && !dir) dir = s;
        else if (s[0] != '-' && !calls) calls = s;
        else return usage();
    }
    if (!dir || !calls) return usage();
    static const char *const names[9] = { "abs", "TS", "TK", "TI", "TV", "TA", "Ap", "Zero", "Suc" };
    FILE *cf = fopen(calls, "rb");
    if (!cf) { perror(calls); return 1; }
    size_t len;
    char *text = slurp(cf, &len);
    fclose(cf);
    if (!text) return 1;
    char dirslash[1024];
    snprintf(dirslash, sizeof dirslash, "%s/", dir);
    uint64_t n = 0, same = 0, steps = 0, fires = 0, line_no = 0;
    for (char *line = text, *nl; *line; line = nl) {
        nl = strchr(line, '\n');
        if (nl) *nl++ = '\0';
        if (line_no++ % every) continue;
        char *fld[4] = { NULL, NULL, NULL, NULL };
        int k = 0;
        for (char *p = line; k < 4 && p; k++) {
            fld[k] = p;
            p = strchr(p, '\t');
            if (p) *p++ = '\0';
        }
        if (k < 3) { fprintf(stderr, "avon: a malformed call\n"); free(text); return 1; }
        av_arena *a = av_arena_new(ARENA_START);
        uint32_t terms[9];
        for (int i = 0; i < 9; i++) {
            char path[1100];
            snprintf(path, sizeof path, "%s%s.skit", dirslash, names[i]);
            FILE *tf = fopen(path, "rb");
            size_t tl = 0;
            char *tb = tf ? slurp(tf, &tl) : NULL;
            if (tf) fclose(tf);
            terms[i] = tb ? av_cue(a, (const uint8_t *)tb, tl, NULL) : AV_NONE;
            free(tb);
        }
        av_compiler c;
        _Static_assert(sizeof c == sizeof terms, "nine terms");
        memcpy(&c, terms, sizeof c);
        const char *err = NULL;
        if (!av_compiler_register(a, &c, &err)) {
            fprintf(stderr, "avon: %s: %s\n", dir, err);
            av_arena_free(a);
            free(text);
            return 1;
        }
        av_compiler kc;
        memcpy(&kc, a->compiler, sizeof kc);
        uint32_t body = av_parse(a, fld[1], strlen(fld[1]), NULL);
        uint32_t d = body == AV_NONE ? AV_NONE : av_tm_encode(a, &kc, body);
        uint32_t x = av_tm_nat(a, &kc, strtoull(fld[0], NULL, 10));
        uint32_t q = d == AV_NONE ? AV_NONE : av_app(a, av_app(a, kc.abs, x), d);
        q = q == AV_NONE ? AV_NONE : av_jets_match(a, q);
        av_opts o = av_opts_default();
        o.strategy = AV_COPY;
        o.whnf_only = true;
        o.max_steps = UINT64_MAX / 2;
        o.compile_jets = jets;
        o.jet_check = check;
        uint64_t p0 = a->probe_steps;
        av_result r = q == AV_NONE ? (av_result){ .status = AV_SIZE } : av_reduce(a, q, &o);
        uint32_t out = AV_NONE;
        if (r.status == AV_WHNF && !r.jet_fault) {
            av_root_push(a, &r.term);
            o.compile_jets = false;
            out = av_tm_decode(a, r.term, &o, &err);
            av_root_pop(a);
        }
        char h[27];
        bool ok = out != AV_NONE && av_structural_hash(a, out, h) && strcmp(h, fld[2]) == 0;
        if (!ok) fprintf(stderr, "avon: call %llu ([v%s] %.60s): %s\n", (unsigned long long)line_no,
                         fld[0], fld[1], r.jet_fault ? "A JET CHECK FAILED" :
                         out == AV_NONE ? "no result" : "not Python's result");
        n++;
        same += ok;
        steps += r.steps + (a->probe_steps - p0);
        fires += r.jet_calls;
        av_arena_free(a);
    }
    free(text);
    printf("selfhost: %llu calls, %llu Python's, %llu contractions, %llu jet fires\n",
           (unsigned long long)n, (unsigned long long)same, (unsigned long long)steps,
           (unsigned long long)fires);
    return same == n ? 0 : 1;
}
