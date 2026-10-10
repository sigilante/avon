/**  scry.c
 *
 *  avon scry: the resume loop (docs/DESIGN.md §8) over a namespaces.tsv
 *  export, each run checked against the reference host's.
 */

#include "cli.h"

typedef struct { const char *dir, *file; } resolution;

static uint32_t load_skit(av_arena *a, const char *dir, const char *file) {
    char path[1024];
    snprintf(path, sizeof path, "%s%s", dir, file);
    FILE *f = fopen(path, "rb");
    if (!f) return AV_NONE;
    size_t len;
    char *b = slurp(f, &len);
    fclose(f);
    uint32_t t = b ? av_cue(a, (const uint8_t *)b, len, NULL) : AV_NONE;
    free(b);
    return t;
}

/*  The namespace: a file of `rendered path <TAB> answer file` lines. */
static uint32_t resolve_file(void *ctx, av_arena *a, const char *key) {
    const resolution *r = ctx;
    if (strcmp(r->file, "-") == 0) return AV_NONE;
    char path[1024];
    snprintf(path, sizeof path, "%s%s", r->dir, r->file);
    FILE *f = fopen(path, "rb");
    if (!f) return AV_NONE;
    size_t len;
    char *text = slurp(f, &len);
    fclose(f);
    uint32_t out = AV_NONE;
    for (char *line = text, *nl; text && line && *line; line = nl) {
        nl = strchr(line, '\n');
        if (nl) *nl++ = '\0';
        char *tab = strchr(line, '\t');
        if (tab && (*tab = '\0', strcmp(line, key) == 0)) out = load_skit(a, r->dir, tab + 1);
    }
    free(text);
    return out;
}

typedef struct { const char *dict, *interp; } arena_setup;

static av_arena *scry_arena(void *ctx) {
    const arena_setup *s = ctx;
    av_arena *a = av_arena_new(ARENA_START);
    const char *err = NULL;
    if (a && s->dict && (av_jets_load(a, s->dict, 8, &err) < 0 ||
                         (s->interp && av_interps_load(a, s->interp, s->dict, &err) < 0))) {
        fprintf(stderr, "avon: %s\n", err);
        av_arena_free(a);
        return NULL;
    }
    return a;
}

/*  avon scry: every run of a namespaces.tsv (skijack.export), each round's
 *  events and every attempt printed, and checked against the reference
 *  host's -- the attempts only when nothing changes counts. */
int scry_main(int argc, char **argv) {
    const char *manifest = NULL, *logdir = NULL, *dict = NULL, *interp = NULL;
    uint64_t check = 0, v;
    for (int i = 2; i < argc; i++) {
        const char *s = argv[i];
        if (strncmp(s, "--log=", 6) == 0 && s[6]) logdir = s + 6;
        else if (strncmp(s, "--jets=", 7) == 0 && s[7]) dict = s + 7;
        else if (strncmp(s, "--interp=", 9) == 0 && s[9]) interp = s + 9;
        else if (strncmp(s, "--jet-check=", 12) == 0 && number(s + 12, &v)) check = v;
        else if (s[0] != '-' && !manifest) manifest = s;
        else return usage();
    }
    if (!manifest || (interp && !dict)) return usage();
    FILE *mf = fopen(manifest, "rb");
    if (!mf) { perror(manifest); return 1; }
    size_t len;
    char *text = slurp(mf, &len);
    fclose(mf);
    if (!text) return 1;
    const char *slash = strrchr(manifest, '/');
    char dir[1024];
    snprintf(dir, sizeof dir, "%.*s", slash ? (int)(slash - manifest + 1) : 0, manifest);
    int runs = 0, off = 0;
    for (char *line = text, *nl; *line; line = nl) {
        nl = strchr(line, '\n');
        if (nl) *nl++ = '\0';
        char *fld[16];
        int k = 0;
        for (char *p = line; k < 16 && p; k++) {
            fld[k] = p;
            p = strchr(p, '\t');
            if (p) *p++ = '\0';
        }
        if (k != 16) { fprintf(stderr, "avon: a malformed namespaces line\n"); free(text); return 1; }
        av_nsprog p;
        memset(&p, 0, sizeof p);
        p.terms = av_arena_new(1u << 12);
        p.interp = load_skit(p.terms, dir, fld[1]);
        p.datum = load_skit(p.terms, dir, fld[3]);
        p.eq = load_skit(p.terms, dir, fld[6]);
        p.hit = load_skit(p.terms, dir, fld[7]);
        p.notyet = load_skit(p.terms, dir, fld[8]);
        p.zero = load_skit(p.terms, dir, fld[9]);
        p.suc = load_skit(p.terms, dir, fld[10]);
        uint32_t params[16];
        if (strcmp(fld[2], "-") != 0) {
            for (char *q = strtok(fld[2], ","); q && p.nparams < 16; q = strtok(NULL, ","))
                params[p.nparams++] = load_skit(p.terms, dir, q);
        }
        p.params = params;
        uint64_t fuel = 0, start = 8, cap = 4096;
        if (strncmp(fld[4], "policy:", 7) == 0) {
            start = strtoull(fld[4] + 7, NULL, 10);
            const char *c = strchr(fld[4] + 7, ':');
            cap = c ? strtoull(c + 1, NULL, 10) : 4096;
        } else {
            fuel = strtoull(fld[4], NULL, 10);
        }
        char *rn[16], *on[16];
        unsigned ar[16], nr = 0, no = 0, ones = 0;
        int app = -1;
        for (char *tok = strtok(fld[11], " "); tok && nr < 16; tok = strtok(NULL, " ")) {
            char *sl = strchr(tok, '/');
            ar[nr] = sl ? (unsigned)atoi(sl + 1) : 0;
            if (sl) *sl = '\0';
            if (ar[nr] == 1 && ++ones == 2) p.block = nr;
            if (ar[nr] == 0) p.timeout = nr;
            rn[nr++] = tok;
        }
        for (char *tok = strtok(fld[12], " "); tok && no < 16; tok = strtok(NULL, " ")) {
            if (tok[0] == '*') { app = (int)no; tok++; }
            char *sl = strchr(tok, '/');
            if (sl) *sl = '\0';
            on[no++] = tok;
        }
        p.nres = nr;
        p.obj = (av_objtype){ (const char *const *)on, no, (unsigned)app };
        bool ok = p.interp != AV_NONE && p.datum != AV_NONE && p.eq != AV_NONE &&
                  p.hit != AV_NONE && p.notyet != AV_NONE && p.zero != AV_NONE &&
                  p.suc != AV_NONE && app >= 0 && ones >= 2;
        for (unsigned i = 0; i < p.nparams; i++) ok = ok && params[i] != AV_NONE;
        if (!ok) { fprintf(stderr, "avon: %s: cannot load its terms\n", fld[0]); free(text); return 1; }
        const char *err = NULL;
        av_facts *f;
        char logpath[1100];
        if (logdir) {
            snprintf(logpath, sizeof logpath, "%s/%s.facts", logdir, fld[0]);
            f = av_facts_open(&p.obj, logpath, &err);
        } else {
            f = av_facts_new(&p.obj);
        }
        if (!f) { fprintf(stderr, "avon: %s: %s\n", fld[0], err ? err : "out of memory"); free(text); return 1; }
        size_t known = av_facts_count(f);
        av_opts o = av_opts_default();
        o.max_steps = 5000000;
        o.interp_jets = interp != NULL;
        o.jets = dict != NULL;
        o.jet_check = check;
        arena_setup setup = { dict, interp };
        resolution res = { dir, fld[13] };
        av_nsrun r;
        if (!av_ns_run(&p, f, resolve_file, &res, dict ? scry_arena : NULL, &setup, fuel,
                       start, cap, (unsigned)atoi(fld[5]), &o, (const char *const *)rn, &r)) {
            fprintf(stderr, "avon: out of memory\n");
            free(text);
            return 1;
        }
        char events[4096] = "", attempts[4096] = "";
        for (size_t i = 0; i < r.nevents; i++) {
            if (i) strncat(events, "|", sizeof events - strlen(events) - 1);
            strncat(events, r.events[i], sizeof events - strlen(events) - 1);
        }
        for (size_t i = 0; i < r.nattempts; i++) {
            char one[64];
            snprintf(one, sizeof one, "%s%llu:%s:%llu", i ? "," : "",
                     (unsigned long long)r.attempts[i].fuel, av_status_name(r.attempts[i].status),
                     (unsigned long long)r.attempts[i].steps);
            strncat(attempts, one, sizeof attempts - strlen(attempts) - 1);
        }
        bool counts = !interp;                  /* interpreter jets change counts */
        bool same = known == 0 && strcmp(events, fld[14]) == 0 &&
                    (!counts || strcmp(attempts, fld[15]) == 0);
        printf("%s: %s%s\n  rounds %u; attempts (fuel:status:contractions) %s\n  facts %zu",
               fld[0], events, known ? "" : same ? "" : "  MISMATCH", r.rounds, attempts,
               av_facts_count(f));
        if (known) printf(", %zu of them from the log: not compared", known);
        printf("\n");
        if (!same && !known) {
            printf("  expected %s\n", fld[14]);
            if (counts) printf("  expected attempts %s\n", fld[15]);
            off++;
        }
        runs++;
        av_nsrun_free(&r);
        av_facts_free(f);
        av_arena_free(p.terms);
    }
    free(text);
    printf("scry: %d runs, %d off the reference\n", runs, off);
    return off ? 1 : 0;
}
