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
 *      avon witness [--rows=N] [--cells=N] [--jet-table=JETS] [--plan=PLAN]
 *                   [FILE]
 *                                     the witness strategy's table, for
 *                                     lean-ski's aircheck and plonky3 (§17);
 *                                     with JETS, lean-ski's jet file for the
 *                                     term, instantiation rows (§18.1)
 *      avon census [--select=N] [--top=N] [--min-atoms=N] [--all]
 *                  [--names=FILE]... MANIFEST...
 *                                     which terms the manifests' runs call,
 *                                     ranked by what a jet on each would
 *                                     absorb (docs/DESIGN.md §6.7)
 *      avon --version
 *
 *  A FILE may be in the printed form, a SKIT container (docs/DESIGN.md
 *  §4.2), or the prefix form, told apart by a magic or a leading `.  Options: --strategy=copy|share
 *  (default share), --whnf, --fuel=N, --max-nodes=N, --budget=N (nodes
 *  printed or jammed; default 1000000), --allow-bird-atoms (§4.3),
 *  --jets=DICT (a dictionary.tsv export: register it and match the term
 *  against it, §6; repeatable), --ctors[=N] (register every Scott
 *  constructor of up to N atoms, default 64, in the term, §6.8),
 *  --jet-floor=N (atoms, default 8), --jet-check=N (check
 *  every Nth fire against the unjetted run, §6.6), --no-jets,
 *  --interp=FILE (interpreters.tsv: interpreter jets, §7; needs --jets).
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
    const char *jets[16];         /* dictionary exports, --jets= each */
    int         njets;
    uint64_t    ctors;            /* --ctors: constructor jets up to N atoms */
    const char *interp;           /* interpreters.tsv, or NULL */
    const char *jet_table;        /* lean-ski's jet file, or NULL */
    const char *plan;             /* lean-ski's probe plan, or NULL */
    uint64_t    jet_floor;
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
        "       avon witness [--rows=N] [--cells=N] [--jet-table=JETS] [--plan=PLAN]\n"
        "                    [FILE]\n"
        "       (all accept --allow-bird-atoms; reduce and batch accept\n"
        "        --jets=DICT... --ctors[=N] --jet-floor=N --jet-check=N --no-jets)\n"
        "       avon census [--select=N] [--top=N] [--min-atoms=N] [--all]\n"
        "                   [--names=FILE]... MANIFEST...\n"
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
    g->njets = 0;
    g->ctors = 0;
    g->interp = NULL;
    g->jet_table = NULL;
    g->plan = NULL;
    g->jet_floor = 8;
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
        else if (strncmp(s, "--jets=", 7) == 0 && s[7] && g->njets < 16)
            g->jets[g->njets++] = s + 7;
        else if (strcmp(s, "--ctors") == 0)          g->ctors = 64;
        else if (strncmp(s, "--ctors=", 8) == 0 && number(s + 8, &v) && v >= 2)
            g->ctors = v;
        else if (strcmp(s, "--no-jets") == 0)        g->o.jets = false;
        else if (strncmp(s, "--interp=", 9) == 0 && s[9]) {
            g->interp = s + 9;
            g->o.interp_jets = true;
        }
        else if (strncmp(s, "--jet-table=", 12) == 0 && s[12]) g->jet_table = s + 12;
        else if (strncmp(s, "--plan=", 7) == 0 && s[7]) g->plan = s + 7;
        else if (strncmp(s, "--jet-floor=", 12) == 0 && number(s + 12, &v))
            g->jet_floor = v;
        else if (strncmp(s, "--jet-check=", 12) == 0 && number(s + 12, &v))
            g->o.jet_check = v;
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
    if (!a) { fprintf(stderr, "avon: out of memory\n"); return NULL; }
    a->allow_bird_atoms = g->birds;
    for (int i = 0; i < g->njets; i++) {
        const char *err = NULL;
        if (av_jets_load(a, g->jets[i], (size_t)g->jet_floor, &err) < 0) {
            fprintf(stderr, "avon: %s: %s\n", g->jets[i], err);
            av_arena_free(a);
            return NULL;
        }
    }
    if (g->njets) {
        const char *err = NULL;
        if (g->interp && av_interps_load(a, g->interp, g->jets[0], &err) < 0) {
            fprintf(stderr, "avon: %s: %s\n", g->interp, err);
            av_arena_free(a);
            return NULL;
        }
    } else if (g->interp) {
        fprintf(stderr, "avon: --interp needs --jets, for the constructors' terms\n");
        av_arena_free(a);
        return NULL;
    }
    return a;
}

/* Reduce one term and print "STATUS steps term" (sep between). */
static int run_one(const args *g, const char *src, size_t len, char sep) {
    av_arena *a = new_arena(g, 1u << 16);
    if (!a) return 1;
    uint32_t t = load(a, src, len);
    long ctors = 0;
    if (t != AV_NONE && g->ctors) {
        av_root_push(a, &t);                /* the scan's runs collect */
        ctors = av_jets_ctors(a, t, (size_t)g->ctors);
        av_root_pop(a);
        if (ctors < 0) t = AV_NONE;
    }
    if (t != AV_NONE && (g->njets || g->ctors)) t = av_jets_match(a, t);
    if (t == AV_NONE) {
        av_arena_free(a);
        return 1;
    }
    av_result r = av_reduce(a, t, &g->o);
    if (g->njets || g->ctors)
        fprintf(stderr, "jets: %u registered (%ld constructors found), %llu fired "
                "(%llu interpreter)%s\n",
                a->njets, ctors, (unsigned long long)r.jet_calls,
                (unsigned long long)r.interp_calls,
                r.jet_fault ? ", A CHECK FAILED" : "");
    av_buf b = { 0 };
    bool whole = r.term != AV_NONE && av_print(a, r.term, g->budget, &b);
    printf("%s %" PRIu64 "%c%s%s\n", av_status_name(r.status), r.steps, sep,
           b.s ? b.s : "", whole ? "" : " ...");
    av_buf_free(&b);
    av_arena_free(a);
    return 0;
}

/*  ------------------------------------------------------------- census */

typedef struct { char *hash, *name; size_t order; } named;

static int named_cmp(const void *x, const void *y) {
    return strcmp(((const named *)x)->hash, ((const named *)y)->hash);
}

static int named_order(const void *x, const void *y) {
    const named *a = x, *b = y;
    int d = strcmp(a->hash, b->hash);
    return d ? d : (a->order > b->order) - (a->order < b->order);
}

/*  One pass over every manifest's runs, recording into c; the runs'
 *  contractions, and the number whose copy-mode count is not the
 *  manifest's. */
static int census_pass(char **manifests, int nm, av_census *c, uint64_t *total,
                       int *runs, int *wrong) {
    *total = 0;
    *runs = *wrong = 0;
    for (int m = 0; m < nm; m++) {
        FILE *f = fopen(manifests[m], "rb");
        if (!f) { perror(manifests[m]); return 1; }
        size_t len;
        char *text = slurp(f, &len);
        fclose(f);
        if (!text) return 1;
        text[len > 0 ? len - (text[len - 1] == '\n') : 0] = '\0';
        const char *slash = strrchr(manifests[m], '/');
        int dirlen = slash ? (int)(slash - manifests[m] + 1) : 0;
        for (char *line = text, *nl; line && *line; line = nl) {
            nl = strchr(line, '\n');
            if (nl) *nl++ = '\0';
            char *fld[9];
            int k = 0;
            for (char *p = line; k < 9 && p; k++) {
                fld[k] = p;
                p = strchr(p, '\t');
                if (p) *p++ = '\0';
            }
            if (k < 5) continue;
            char path[1024];
            snprintf(path, sizeof path, "%.*s%s", dirlen, manifests[m], fld[1]);
            FILE *g = fopen(path, "rb");
            if (!g) { perror(path); free(text); return 1; }
            size_t blen;
            char *bytes = slurp(g, &blen);
            fclose(g);
            av_arena *a = av_arena_new(1u << 16);
            uint32_t t = bytes && a ? av_cue(a, (const uint8_t *)bytes, blen, NULL) : AV_NONE;
            free(bytes);
            if (t != AV_NONE) {
                if (!av_census_begin_run(c, a, t)) { free(text); av_arena_free(a); return 1; }
                av_opts o = av_opts_default();
                o.strategy = AV_COPY;
                o.whnf_only = true;
                o.jets = false;
                o.max_steps = strtoull(fld[2], NULL, 10);
                o.census = c;
                av_result r = av_reduce(a, t, &o);
                *total += r.steps;
                (*runs)++;
                if (r.steps != strtoull(fld[4], NULL, 10) ||
                    strcmp(av_status_name(r.status), fld[3]) != 0) {
                    fprintf(stderr, "avon: %s: %s %llu, the manifest says %s %s\n",
                            fld[0], av_status_name(r.status),
                            (unsigned long long)r.steps, fld[3], fld[4]);
                    (*wrong)++;
                }
            }
            av_arena_free(a);
        }
        free(text);
    }
    return 0;
}

static const char *name_of(named *names, size_t nnames, const av_census_row *r) {
    named key = { (char *)r->hash, NULL, 0 };
    named *hit = r->hash[0] ? bsearch(&key, names, nnames, sizeof *names, named_cmp) : NULL;
    return hit ? hit->name : NULL;
}

static void census_line(av_census *c, uint64_t total, const char *rank,
                        const av_census_row *r, const char *name) {
    av_buf b = { 0 };
    bool whole = r->term != AV_NONE && av_print(av_census_arena(c), r->term, 40, &b);
    printf("%4s %10llu %6.2f %8llu %8llu %3u %6llu %6zu %4zu  %-22.22s %.60s%s\n",
           rank, (unsigned long long)r->saved,
           total ? 100.0 * (double)r->saved / (double)total : 0.0,
           (unsigned long long)r->fires, (unsigned long long)r->calls,
           r->arity, (unsigned long long)r->cost, r->atoms, r->members,
           name ? name : "-", b.s ? b.s : "", whole ? "" : " ...");
    av_buf_free(&b);
}

static int census_main(int argc, char **argv) {
    uint64_t select = 400, top = 40, min_atoms = 5, v;
    bool all = false;
    char *manifests[256], *namefiles[64];
    int nm = 0, nn = 0;
    for (int i = 2; i < argc; i++) {
        const char *s = argv[i];
        if (strncmp(s, "--select=", 9) == 0 && number(s + 9, &v)) select = v;
        else if (strncmp(s, "--top=", 6) == 0 && number(s + 6, &v)) top = v;
        else if (strncmp(s, "--min-atoms=", 12) == 0 && number(s + 12, &v)) min_atoms = v;
        else if (strncmp(s, "--names=", 8) == 0 && nn < 64) namefiles[nn++] = argv[i] + 8;
        else if (strcmp(s, "--all") == 0) all = true;
        else if (s[0] != '-' && nm < 256) manifests[nm++] = argv[i];
        else return usage();
    }
    if (!nm) return usage();

    /* names, by hash: every distinct name the files give, in their order */
    named *names = NULL;
    size_t nnames = 0, ncap = 0;
    for (int i = 0; i < nn; i++) {
        FILE *f = fopen(namefiles[i], "rb");
        if (!f) { perror(namefiles[i]); return 1; }
        char line[4096];
        while (fgets(line, sizeof line, f)) {
            char *t1 = strchr(line, '\t'), *t2 = t1 ? strchr(t1 + 1, '\t') : NULL;
            if (!t2) continue;
            *t1 = *t2 = '\0';
            t2[1 + strcspn(t2 + 1, "\n")] = '\0';
            if (nnames == ncap) {
                named *q = realloc(names, (ncap = ncap ? 2 * ncap : 256) * sizeof *q);
                if (!q) return 1;
                names = q;
            }
            names[nnames].hash = strdup(t2 + 1);
            names[nnames].name = strdup(t1 + 1);
            names[nnames].order = nnames;
            nnames++;
        }
        fclose(f);
    }
    qsort(names, nnames, sizeof *names, named_order);
    size_t kept = 0;
    for (size_t i = 0; i < nnames; i++) {
        named *k = kept ? &names[kept - 1] : NULL;
        if (!k || strcmp(k->hash, names[i].hash)) { names[kept++] = names[i]; continue; }
        size_t kl = strlen(k->name), nl = strlen(names[i].name);
        bool seen = false;
        for (const char *p = k->name; (p = strstr(p, names[i].name)); p += nl)
            if ((p == k->name || p[-1] == '/') && (p[nl] == '/' || !p[nl])) { seen = true; break; }
        char *m = seen ? NULL : malloc(kl + nl + 2);
        if (m) {
            snprintf(m, kl + nl + 2, "%s/%s", k->name, names[i].name);
            free(k->name);
            k->name = m;
        }
        free(names[i].hash);
        free(names[i].name);
    }
    nnames = kept;

    av_census *c = av_census_new();
    uint64_t total;
    int runs, wrong;
    if (!c || census_pass(manifests, nm, c, &total, &runs, &wrong)) return 1;
    uint64_t calls = av_census_calls(c);
    av_census_select(c, (size_t)select, (size_t)min_atoms);
    if (census_pass(manifests, nm, c, &total, &runs, &wrong)) return 1;
    av_census_analyze(c);
    if (census_pass(manifests, nm, c, &total, &runs, &wrong)) return 1;
    av_census_row *rows;
    size_t n = av_census_rows(c, &rows);
    printf("census: %d runs, %llu contractions, %llu calls; %d counts off the "
           "manifests\n", runs, (unsigned long long)total,
           (unsigned long long)calls, wrong);
    printf("%4s %10s %6s %8s %8s %3s %6s %6s %4s  %-22s %s\n", "rank", "saved", "%",
           "fires", "calls", "ar", "cost", "atoms", "+fam", "name", "term");
    size_t shown = 0;
    for (size_t i = 0; i < n && shown < top; i++) {
        av_census_row *r = &rows[i];
        if (r->family >= 0) continue;                /* a layer of a row above */
        if (!r->arity && !all) continue;             /* no residual jet: arity > 8 */
        char rank[16];
        snprintf(rank, sizeof rank, "%zu", ++shown);
        /* unnamed, a head borrows its first named layer's name: ~name */
        const char *name = name_of(names, nnames, r);
        char borrowed[64], shape[48];
        if (!name && r->ctor.count) {       /* a constructor: its shape */
            snprintf(shape, sizeof shape, "ctor %u/%u/%u", r->ctor.fields,
                     r->ctor.index, r->ctor.count);
            name = shape;
        }
        for (size_t j = i + 1; !name && j < n; j++)
            if (rows[j].family == (int64_t)i && name_of(names, nnames, &rows[j])) {
                snprintf(borrowed, sizeof borrowed, "~%s", name_of(names, nnames, &rows[j]));
                name = borrowed;
            }
        census_line(c, total, rank, r, name);
        for (size_t j = i + 1; all && j < n; j++)    /* --all: the layers too */
            if (rows[j].family == (int64_t)i)
                census_line(c, total, "  ^", &rows[j], name_of(names, nnames, &rows[j]));
    }
    for (size_t i = 0; i < nnames; i++) { free(names[i].hash); free(names[i].name); }
    free(names);
    av_census_free(c);
    return wrong ? 1 : 0;
}

int main(int argc, char **argv) {
    if (argc == 2 && strcmp(argv[1], "--version") == 0) {
        printf("avon %s\n", AVON_VERSION);
        return 0;
    }
    if (argc < 2) return usage();
    if (strcmp(argv[1], "census") == 0) return census_main(argc, argv);
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
            av_jettable jt;
            bool have_jt = false;
            uint64_t insts = 0;
            const char *msg = NULL;
            av_buf b = { 0 };
            rc = 1;
            if (t != AV_NONE && g.jet_table) {
                FILE *jf = fopen(g.jet_table, "rb");
                size_t jlen = 0;
                char *jsrc = jf ? slurp(jf, &jlen) : NULL;
                if (jf) fclose(jf);
                if (!jsrc) {
                    fprintf(stderr, "avon: cannot read %s\n", g.jet_table);
                    t = AV_NONE;
                } else if (!av_jettable_read(jsrc, jlen, &jt, &msg)) {
                    fprintf(stderr, "avon: %s: %s\n", g.jet_table, msg);
                    t = AV_NONE;
                } else {
                    have_jt = true;
                }
                free(jsrc);
            }
            av_plan plan = { NULL, 0 };
            av_probe pr = { NULL, NULL, NULL, 0 };
            if (t != AV_NONE && g.plan) {
                FILE *pf = fopen(g.plan, "rb");
                size_t plen = 0;
                char *psrc = pf ? slurp(pf, &plen) : NULL;
                if (pf) fclose(pf);
                if (!psrc) {
                    fprintf(stderr, "avon: cannot read %s\n", g.plan);
                    t = AV_NONE;
                } else if (!av_plan_read(psrc, plen, &plan, &msg)) {
                    fprintf(stderr, "avon: %s: %s\n", g.plan, msg);
                    t = AV_NONE;
                }
                free(psrc);
            }
            if (t != AV_NONE) {
                av_status st = g.plan
                    ? av_witness_run_probe(a, t, have_jt ? &jt : NULL, &plan, (size_t)g.rows,
                                           (size_t)g.cells, &w, &pr, &insts, &msg)
                    : av_witness_run_jets(a, t, have_jt ? &jt : NULL, (size_t)g.rows,
                                          (size_t)g.cells, &w, &insts, &msg);
                if (st == AV_INTERRUPTED) {
                    fprintf(stderr, "avon: the term does not decode to the plan's outcome: %s\n", msg);
                } else if (st != AV_WHNF) {
                    fprintf(stderr, "avon: no witness: %s\n", msg);
                } else if (!av_witness_table(a, t, &w, 4, &b) ||
                           (g.plan && !av_probe_table(&w, &pr, 4, &b))) {
                    fprintf(stderr, "avon: could not write the table\n");
                } else {
                    fwrite(b.s, 1, b.len, stdout);
                    fprintf(stderr, "contractions %llu rows %zu cells %zu loaded %zu insts %llu\n",
                            (unsigned long long)w.contractions, w.nrows, w.nmem, w.loaded,
                            (unsigned long long)insts);
                    rc = 0;
                }
                av_witness_free(&w);
                av_probe_free(&pr);
            }
            av_plan_free(&plan);
            if (have_jt) av_jettable_free(&jt);
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
