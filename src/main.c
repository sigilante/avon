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
 *                  [--names=FILE]... [--emit=DICT] MANIFEST...
 *                                     which terms the manifests' runs call,
 *                                     ranked by what a jet on each would
 *                                     absorb (docs/DESIGN.md §6.7); --emit
 *                                     writes the shown rows and their layers
 *                                     as a jet dictionary
 *      avon jetstat [--jets=DICT]... [--ctors[=N]] [--names=FILE]... [--share]
 *                   [--alone] [--halting] [--top=N] MANIFEST...
 *                                     what each jet does on the manifests'
 *                                     runs: fires, absorbed contractions,
 *                                     misses, demotions, and each fire's
 *                                     origin; with --alone, each dictionary
 *                                     row by itself too (docs/DESIGN.md §6.7)
 *      avon scry [--log=DIR] [--jets=DICT [--interp=FILE]] [--jet-check=N]
 *                NAMESPACES
 *                                     the resume loop (docs/DESIGN.md §8) over
 *                                     a namespaces.tsv export: each run's
 *                                     events and attempts, checked against
 *                                     the reference host's; --log keeps each
 *                                     run's facts in DIR/ID.facts
 *      avon boot [--pier=DIR [--pma]] [--subject=FILE] PILL
 *      avon poke --pier=DIR [--snapshot] EVENT...
 *      avon peek --pier=DIR PATH...
 *      avon load --pier=DIR [--subject=FILE] [--snapshot] PILL
 *                                     a kernel (docs/DESIGN.md §9, §20): boot
 *                                     applies a pill (SKIT) to the initial
 *                                     subject (default I: skijack's standard
 *                                     subject is unbuilt), and with --pier
 *                                     makes a pier -- an event log and
 *                                     snapshots, or with --pma a persistent
 *                                     arena committed every event -- that
 *                                     poke, peek and load reopen; share mode
 *                                     by default
 *      avon selfhost [--jets] [--jet-check=N] [--every=N] DIR CALLS
 *                                     the compiler's core as a term
 *                                     (docs/DESIGN.md §20.3): every call of a
 *                                     calls file through DIR/abs.skit, or its
 *                                     jet, checked against Python's by hash
 *      avon front0 [--profile=NAMES] [--jets=DICT]... [--ctors[=N]] [--jet-stats[=N]]
 *                  [--names=FILE]... [--fuel=N] [--max-nodes=N] DIR SOURCE
 *                                     the SKIjack-0 front end (docs/DESIGN.md
 *                                     §20.3) on SOURCE: DIR/front.skit and the
 *                                     input's constructors; each name and its
 *                                     term's hash, read by probing
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
 *  --interp=FILE (interpreters.tsv: interpreter jets, §7; needs --jets, and
 *  takes the constructors' terms from the first --jets= dictionary),
 *  --profile=NAMES (share mode: each contraction charged to the named term
 *  whose code it runs, reported on stderr, §6.7).
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
    const char *profile;          /* --profile: a names file, or NULL */
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
        "        --jets=DICT... --ctors[=N] --jet-floor=N --jet-check=N --no-jets\n"
        "        --profile=NAMES)\n"
        "       avon census [--select=N] [--top=N] [--min-atoms=N] [--all]\n"
        "                   [--names=FILE]... [--emit=DICT] MANIFEST...\n"
        "       avon jetstat [--jets=DICT]... [--ctors[=N]] [--names=FILE]... [--share]\n"
        "                    [--alone] [--halting] [--top=N] MANIFEST...\n"
        "       avon scry [--log=DIR] [--jets=DICT [--interp=FILE]] [--jet-check=N]\n"
        "                 NAMESPACES\n"
        "       avon boot [--pier=DIR [--pma]] [--subject=FILE] PILL\n"
        "       avon poke --pier=DIR [--snapshot] EVENT...\n"
        "       avon peek --pier=DIR PATH...\n"
        "       avon load --pier=DIR [--subject=FILE] [--snapshot] PILL\n"
        "       (boot, poke, peek, load accept --strategy=, --fuel=, --budget=)\n"
        "       avon selfhost [--jets] [--jet-check=N] [--every=N] DIR CALLS\n"
        "       avon front0 [--profile=NAMES] [--jets=DICT]... [--ctors[=N]] [--jet-stats[=N]]\n"
        "                   [--names=FILE]... [--fuel=N] [--max-nodes=N] DIR SOURCE\n"
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
    g->profile = NULL;
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
        else if (strncmp(s, "--jets=", 7) == 0 && s[7]) {
            if (g->njets == 16) {
                fprintf(stderr, "avon: at most 16 --jets= dictionaries\n");
                return false;
            }
            g->jets[g->njets++] = s + 7;
        }
        else if (strcmp(s, "--ctors") == 0)          g->ctors = 64;
        else if (strncmp(s, "--ctors=", 8) == 0 && number(s + 8, &v)) {
            if (v < 2) {                /* a constructor is an application */
                fprintf(stderr, "avon: --ctors=N needs N >= 2 atoms\n");
                return false;
            }
            g->ctors = v;
        }
        else if (strcmp(s, "--no-jets") == 0)        g->o.jets = false;
        else if (strncmp(s, "--profile=", 10) == 0 && s[10]) g->profile = s + 10;
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
/*  A profile of t (§6.7) named by a names file, `kind TAB name TAB hash`
 *  per line, as census --names reads. */
static av_profile *profile_load(const char *path, const av_arena *a, uint32_t t) {
    FILE *f = fopen(path, "rb");
    if (!f) { perror(path); return NULL; }
    av_profile *p = av_profile_new();
    char line[4096];
    bool ok = p != NULL;
    while (ok && fgets(line, sizeof line, f)) {
        char *t1 = strchr(line, '\t'), *t2 = t1 ? strchr(t1 + 1, '\t') : NULL;
        if (!t2) continue;
        *t1 = *t2 = '\0';
        t2[1 + strcspn(t2 + 1, "\n")] = '\0';
        if (!av_profile_name(p, t2 + 1, t1 + 1)) {
            fprintf(stderr, "avon: %s: bad hash %s\n", path, t2 + 1);
            ok = false;
        }
    }
    fclose(f);
    if (ok && !av_profile_begin(p, a, t)) {
        fprintf(stderr, "avon: out of memory profiling\n");
        ok = false;
    }
    if (!ok) { av_profile_free(p); return NULL; }
    return p;
}

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
    av_opts o = g->o;
    av_profile *prof = NULL;
    if (g->profile && o.strategy != AV_SHARE) {
        fprintf(stderr, "avon: --profile charges share-mode contractions only\n");
        av_arena_free(a);
        return 1;
    }
    if (g->profile && !(prof = profile_load(g->profile, a, t))) {
        av_arena_free(a);
        return 1;
    }
    o.profile = prof;
    av_result r = av_reduce(a, t, &o);
    if (prof) {
        av_profile_report(prof, stderr, SIZE_MAX);
        av_profile_free(prof);
    }
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
           r->arity, (unsigned long long)r->cost, r->atoms, r->folded,
           name ? name : "-", b.s ? b.s : "", whole ? "" : " ...");
    av_buf_free(&b);
}

/*  -------------------------------------------------------------- kernel */

static uint8_t *read_file(const char *path, size_t *len) {
    FILE *f = fopen(path, "rb");
    if (!f) { perror(path); return NULL; }
    char *b = slurp(f, len);
    fclose(f);
    return (uint8_t *)b;
}

/*  The default initial subject: skijack's standard subject is unbuilt
 *  (SPEC.md §5), so until it is, a program is applied to I. */
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

/*  avon boot | poke | peek | load: a kernel in a pier directory (§9, §20). */
static int kernel_main(int argc, char **argv) {
    const char *cmd = argv[1], *pier = NULL, *subject_file = NULL;
    const char *files[256];
    int nf = 0;
    bool snap = false, pma = false;
    uint64_t budget = 100000, v;
    av_opts o = av_opts_default();
    o.strategy = AV_SHARE;                      /* §9: kernel loops share */
    o.max_steps = 100000000;
    for (int i = 2; i < argc; i++) {
        const char *s = argv[i];
        if (strncmp(s, "--pier=", 7) == 0 && s[7]) pier = s + 7;
        else if (strncmp(s, "--subject=", 10) == 0 && s[10]) subject_file = s + 10;
        else if (strcmp(s, "--strategy=copy") == 0) o.strategy = AV_COPY;
        else if (strcmp(s, "--strategy=share") == 0) o.strategy = AV_SHARE;
        else if (strncmp(s, "--fuel=", 7) == 0 && number(s + 7, &v)) o.max_steps = v;
        else if (strncmp(s, "--budget=", 9) == 0 && number(s + 9, &v)) budget = v;
        else if (strcmp(s, "--snapshot") == 0) snap = true;
        else if (strcmp(s, "--pma") == 0) pma = true;
        else if (s[0] != '-' && nf < 256) files[nf++] = s;
        else return usage();
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
            av_pier *p = pma ? av_pier_new_pma(pier, pill, np, subject, ns, &o, &err)
                             : av_pier_new(pier, pill, np, subject, ns, &o, &err);
            if (!p) fprintf(stderr, "avon: %s: %s\n", pier, err);
            else {
                printf("booted a kernel in %s%s\n", pier, pma ? ", on a persistent arena" : "");
                rc = 0;
            }
            av_pier_free(p);
        } else {                                /* boot once, and show the value */
            av_arena *a = av_arena_new(1u << 16);
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
                printf("event %llu, %llu contractions; effects: ", (unsigned long long)k->events,
                       (unsigned long long)r.steps);
                print_value(k->a, eff, budget);
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
                printf("event %llu: loaded the kernel %s boots to\n",
                       (unsigned long long)k->events, files[i]);
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

/*  ------------------------------------------------------------ selfhost */

/*  avon selfhost DIR CALLS: every call of a calls file (tests/selfhost/
 *  export.py) through the compiler term DIR/abs.skit -- or its jet, with
 *  --jets -- decoded and compared with Python's result by hash. */
static int selfhost_main(int argc, char **argv) {
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
        av_arena *a = av_arena_new(1u << 16);
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

/*  ---------------------------------------------------------------- scry */

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
    av_arena *a = av_arena_new(1u << 16);
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
static int scry_main(int argc, char **argv) {
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

static int census_main(int argc, char **argv) {
    uint64_t select = 400, top = 40, min_atoms = 5, v;
    bool all = false;
    const char *emit = NULL;
    char *manifests[256], *namefiles[64];
    int nm = 0, nn = 0;
    for (int i = 2; i < argc; i++) {
        const char *s = argv[i];
        if (strncmp(s, "--select=", 9) == 0 && number(s + 9, &v)) select = v;
        else if (strncmp(s, "--top=", 6) == 0 && number(s + 6, &v)) top = v;
        else if (strncmp(s, "--min-atoms=", 12) == 0 && number(s + 12, &v)) min_atoms = v;
        else if (strncmp(s, "--names=", 8) == 0 && nn < 64) namefiles[nn++] = argv[i] + 8;
        else if (strcmp(s, "--all") == 0) all = true;
        else if (strncmp(s, "--emit=", 7) == 0 && s[7]) emit = s + 7;
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
    FILE *ef = emit ? fopen(emit, "w") : NULL;
    if (emit && !ef) { perror(emit); return 1; }
    for (size_t i = 0; i < n && shown < top; i++) {
        av_census_row *r = &rows[i];
        if (r->folds_into >= 0) continue;            /* a layer of a row above */
        if (!r->arity && !all) continue;             /* no residual jet: arity > 8 */
        /* --emit: the row and its layers, as a jet dictionary */
        for (size_t j = i; ef && j < n; j++) {
            if (j != i && rows[j].folds_into != (int64_t)i) continue;
            if (!rows[j].arity || rows[j].term == AV_NONE || !rows[j].hash[0]) continue;
            av_buf b = { 0 };
            if (av_print(av_census_arena(c), rows[j].term, SIZE_MAX, &b))
                fprintf(ef, "%s\t%zu\t%s\n", rows[j].hash, rows[j].atoms, b.s);
            av_buf_free(&b);
        }
        char rank[16];
        snprintf(rank, sizeof rank, "%zu", ++shown);
        /* unnamed, a head borrows its first named layer's name: ~name */
        const char *name = name_of(names, nnames, r);
        char borrowed[64], shape[48];
        if (!name && av_ctor_is(r->ctor)) {  /* a constructor: its shape */
            snprintf(shape, sizeof shape, "ctor %u/%u/%u", r->ctor.fields,
                     r->ctor.index, r->ctor.count);
            name = shape;
        }
        for (size_t j = i + 1; !name && j < n; j++)
            if (rows[j].folds_into == (int64_t)i && name_of(names, nnames, &rows[j])) {
                snprintf(borrowed, sizeof borrowed, "~%s", name_of(names, nnames, &rows[j]));
                name = borrowed;
            }
        census_line(c, total, rank, r, name);
        for (size_t j = i + 1; all && j < n; j++)    /* --all: the layers too */
            if (rows[j].folds_into == (int64_t)i)
                census_line(c, total, "  ^", &rows[j], name_of(names, nnames, &rows[j]));
    }
    if (ef) fclose(ef);
    for (size_t i = 0; i < nnames; i++) { free(names[i].hash); free(names[i].name); }
    free(names);
    av_census_free(c);
    return wrong ? 1 : 0;
}

/*  ------------------------------------------------------------ jetstat */

typedef struct { uint64_t digest; char hash[27]; char *term; int file; } drow;

typedef struct {
    char   **dicts;
    int      ndicts;
    uint64_t ctors;             /* constructor jets up to N atoms; 0 none  */
    bool     share;
    bool     halting;           /* only the runs the manifest says halt    */
    bool     only;              /* register just one dictionary row        */
    int      only_file;
    uint64_t only_digest;
} jetcfg;

/*  One pass over the manifests' runs with cfg's jets, into s.  A copy-mode
 *  count must be the manifest's: jets keep counts (§6.5). */
static int jet_pass(char **manifests, int nm, const jetcfg *cfg, av_jetstats *s,
                    uint64_t *total, int *runs, int *wrong) {
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
            for (char *q = line; k < 9 && q; k++) {
                fld[k] = q;
                q = strchr(q, '\t');
                if (q) *q++ = '\0';
            }
            if (k < 5) continue;
            /* a run the fuel stops counts what the budget buys, and a
             * share-mode fire is charged its copy cost: --halting skips it */
            if (cfg->halting && strcmp(fld[3], "FUEL") == 0) continue;
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
            if (t == AV_NONE) { fprintf(stderr, "avon: %s: not a term\n", path); free(text); av_arena_free(a); return 1; }
            av_root_push(a, &t);                /* registration collects */
            bool ok = !cfg->ctors || cfg->only || av_jets_ctors(a, t, (size_t)cfg->ctors) >= 0;
            for (int d = 0; ok && d < cfg->ndicts; d++) {
                if (cfg->only && d != cfg->only_file) continue;
                const char *err = NULL;
                long got = cfg->only ? av_jets_load_only(a, cfg->dicts[d], 1, cfg->only_digest, &err)
                                     : av_jets_load(a, cfg->dicts[d], 1, &err);
                if (got < 0) { fprintf(stderr, "avon: %s: %s\n", cfg->dicts[d], err); ok = false; }
            }
            av_root_pop(a);
            if (ok && a->njets) t = av_jets_match(a, t);
            if (!ok || t == AV_NONE || !av_jetstats_begin(s, a, t)) {
                free(text);
                av_arena_free(a);
                return 1;
            }
            av_opts o = av_opts_default();
            o.strategy = cfg->share ? AV_SHARE : AV_COPY;
            o.whnf_only = true;
            o.jets = true;
            o.max_steps = strtoull(fld[2], NULL, 10);
            o.jetstats = s;
            av_result r = av_reduce(a, t, &o);
            *total += r.steps;
            (*runs)++;
            if (!cfg->share && (r.steps != strtoull(fld[4], NULL, 10) ||
                                strcmp(av_status_name(r.status), fld[3]) != 0)) {
                fprintf(stderr, "avon: %s: %s %llu with jets, the manifest says %s %s\n",
                        fld[0], av_status_name(r.status), (unsigned long long)r.steps,
                        fld[3], fld[4]);
                (*wrong)++;
            }
            av_arena_free(a);
        }
        free(text);
    }
    return 0;
}

typedef struct { char *hash, *name; } jname;

static int jname_cmp(const void *x, const void *y) {
    return strcmp(((const jname *)x)->hash, ((const jname *)y)->hash);
}

/*  A row's label: its name, its constructor shape, or its dictionary term. */
static void jet_label(char *out, size_t cap, const char *hash, av_ctor ctor,
                      const jname *names, size_t nn, const drow *rows, size_t nr) {
    jname key = { (char *)hash, NULL };
    const jname *hit = nn ? bsearch(&key, names, nn, sizeof key, jname_cmp) : NULL;
    if (hit) { snprintf(out, cap, "%s", hit->name); return; }
    if (av_ctor_is(ctor)) {
        snprintf(out, cap, "ctor %u/%u/%u", ctor.fields, ctor.index, ctor.count);
        return;
    }
    for (size_t i = 0; i < nr; i++)
        if (strcmp(rows[i].hash, hash) == 0) { snprintf(out, cap, "%.40s", rows[i].term); return; }
    snprintf(out, cap, "%.16s", hash + 10);
}

/*  The dictionaries' rows, for --alone and for labels. */
static int load_rows(char **dicts, int nd, drow **out, size_t *count) {
    drow *rows = NULL;
    size_t nr = 0, rcap = 0;
    for (int d = 0; d < nd; d++) {
        FILE *f = fopen(dicts[d], "rb");
        if (!f) { perror(dicts[d]); return 1; }
        char *line = NULL;
        size_t cap = 0;
        while (getline(&line, &cap, f) > 0) {
            char *t1 = strchr(line, '\t'), *t2 = t1 ? strchr(t1 + 1, '\t') : NULL;
            if (!t2 || t1 - line != 26) continue;
            if (nr == rcap) {
                drow *q = realloc(rows, (rcap = rcap ? 2 * rcap : 256) * sizeof *q);
                if (!q) return 1;
                rows = q;
            }
            drow *r = &rows[nr];
            memcpy(r->hash, line, 26);
            r->hash[26] = '\0';
            if (!av_hash_parse(r->hash, &r->digest)) continue;
            t2[1 + strcspn(t2 + 1, "\n")] = '\0';
            r->term = strdup(t2 + 1);
            r->file = d;
            nr++;
        }
        free(line);
        fclose(f);
    }
    *out = rows;
    *count = nr;
    return 0;
}

/*  Names by hash, a second name for one hash joined with "/". */
static int load_jnames(char **namefiles, int nn, jname **out, size_t *count) {
    jname *names = NULL;
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
            size_t j = 0;
            while (j < nnames && strcmp(names[j].hash, t2 + 1) != 0) j++;
            if (j < nnames) {
                if (strstr(names[j].name, t1 + 1)) continue;
                size_t l = strlen(names[j].name) + strlen(t1 + 1) + 2;
                char *q = malloc(l);
                if (!q) return 1;
                snprintf(q, l, "%s/%s", names[j].name, t1 + 1);
                free(names[j].name);
                names[j].name = q;
                continue;
            }
            if (nnames == ncap) {
                jname *q = realloc(names, (ncap = ncap ? 2 * ncap : 256) * sizeof *q);
                if (!q) return 1;
                names = q;
            }
            names[nnames].hash = strdup(t2 + 1);
            names[nnames].name = strdup(t1 + 1);
            nnames++;
        }
        fclose(f);
    }
    if (nnames) qsort(names, nnames, sizeof *names, jname_cmp);
    *out = names;
    *count = nnames;
    return 0;
}

static const av_jetstats *sort_stats;

static int by_absorbed(const void *x, const void *y) {
    char h[27];
    unsigned ar;
    uint64_t cost;
    size_t atoms;
    av_jetstat_row a, b;
    av_jetstats_row(sort_stats, *(const size_t *)x, h, &ar, &cost, &atoms, &a);
    av_jetstats_row(sort_stats, *(const size_t *)y, h, &ar, &cost, &atoms, &b);
    return (a.absorbed < b.absorbed) - (a.absorbed > b.absorbed);
}

static int by_pair_fires(const void *x, const void *y) {
    uint64_t a = ((const av_jetstat_pair *)x)->fires, b = ((const av_jetstat_pair *)y)->fires;
    return (a < b) - (a > b);
}

/*  The jets' table, most absorbed first, then the nested fires; with the
 *  alone arrays (per dictionary row), each jet's run by itself beside. */
static void print_jetstats(FILE *out, const av_jetstats *all, uint64_t total, size_t top,
                           const drow *rows, size_t nr, const jname *names, size_t nnames,
                           bool alone, const bool *alone_seen, const uint64_t *alone_abs,
                           const uint64_t *alone_fires) {
    size_t n = av_jetstats_rows(all);
    size_t *order = malloc((n ? n : 1) * sizeof *order);
    if (!order) return;
    for (size_t i = 0; i < n; i++) order[i] = i;
    sort_stats = all;
    qsort(order, n, sizeof *order, by_absorbed);
    uint64_t sum_together = 0, sum_alone = 0, sum_alone_together = 0, sum_fires = 0;
    for (size_t i = 0; i < n; i++) {
        char h[27];
        unsigned ar;
        uint64_t cost;
        size_t atoms;
        av_jetstat_row c;
        av_jetstats_row(all, i, h, &ar, &cost, &atoms, &c);
        sum_together += c.absorbed;
        sum_fires += c.fires;
        for (size_t j = 0; alone && j < nr; j++)
            if (alone_seen[j] && strcmp(rows[j].hash, h) == 0) {
                sum_alone += alone_abs[j];
                sum_alone_together += c.absorbed;
                break;
            }
    }
    fprintf(out, "%zu jets registered; together they absorb %llu (%.1f%%) in %llu fires, "
           "leaving %llu contractions stepped\n", n,
           (unsigned long long)sum_together, total ? 100.0 * (double)sum_together / (double)total : 0.0,
           (unsigned long long)sum_fires, (unsigned long long)(total - sum_together));
    if (alone)
        fprintf(out, "the dictionary's jets absorb %llu together, %llu summed alone: "
               "%.1f%% of the alone sum is lost to overlap\n",
               (unsigned long long)sum_alone_together, (unsigned long long)sum_alone,
               sum_alone ? 100.0 * (1.0 - (double)sum_alone_together / (double)sum_alone) : 0.0);
    fprintf(out, "\n%10s %10s %10s %10s %9s %9s %9s %9s %9s %3s %5s %5s %6s  %s\n", "absorbed", "alone",
           "fires", "alone", "top", "in-resid", "in-term", "misses", "demoted", "ar",
           "cost", "atoms", "nodes", "jet");
    for (size_t k = 0; k < n && k < top; k++) {
        size_t i = order[k];
        char h[27], label[64];
        unsigned ar;
        uint64_t cost;
        size_t atoms;
        av_jetstat_row c;
        av_jetstats_row(all, i, h, &ar, &cost, &atoms, &c);
        char aabs[24] = "-", afires[24] = "-";
        for (size_t j = 0; alone && j < nr; j++)
            if (alone_seen[j] && strcmp(rows[j].hash, h) == 0) {
                snprintf(aabs, sizeof aabs, "%llu", (unsigned long long)alone_abs[j]);
                snprintf(afires, sizeof afires, "%llu", (unsigned long long)alone_fires[j]);
                break;
            }
        jet_label(label, sizeof label, h, c.ctor, names, nnames, rows, nr);
        fprintf(out, "%10llu %10s %10llu %10s %9llu %9llu %9llu %9llu %9llu %3u %5llu %5zu %6u  %s\n",
               (unsigned long long)c.absorbed, aabs, (unsigned long long)c.fires, afires,
               (unsigned long long)c.top, (unsigned long long)c.in_residual,
               (unsigned long long)c.in_term, (unsigned long long)c.misses,
               (unsigned long long)c.demotions, ar, (unsigned long long)cost, atoms, c.nodes, label);
    }
    av_jetstat_pair *pairs;
    size_t np = av_jetstats_pairs(all, &pairs);
    qsort(pairs, np, sizeof *pairs, by_pair_fires);
    fprintf(out, "\nnested fires: the inner jet fired from the outer's residual (after it "
           "fired) or term (after it missed)\n");
    for (size_t k = 0; k < np && k < top; k++) {
        char ho[27], hi[27], lo[64], li[64];
        unsigned ar;
        uint64_t cost;
        size_t atoms;
        av_jetstat_row co, ci;
        av_jetstats_row(all, pairs[k].outer, ho, &ar, &cost, &atoms, &co);
        av_jetstats_row(all, pairs[k].inner, hi, &ar, &cost, &atoms, &ci);
        jet_label(lo, sizeof lo, ho, co.ctor, names, nnames, rows, nr);
        jet_label(li, sizeof li, hi, ci.ctor, names, nnames, rows, nr);
        fprintf(out, "%10llu  %-8s %s  <-  %s\n", (unsigned long long)pairs[k].fires,
               pairs[k].kind == AV_FROM_RESIDUAL ? "residual" : "term", li, lo);
    }
    free(pairs);
    free(order);
}

/*  avon front0 [--profile=NAMES] [--fuel=N] [--max-nodes=N] DIR SOURCE:
 *  the SKIjack-0 front end (§20.3) on SOURCE, DIR holding its term and the
 *  input's constructors as SKIT files; a line `name TAB hash` per name, or
 *  `RErr`, and the contractions on stderr. */
static int front0_main(int argc, char **argv) {
    const char *dir = NULL, *source = NULL, *profile = NULL;
    char *dicts[16], *namefiles[64];
    int nd = 0, nn = 0;
    uint64_t ctors = 0, stats_top = 0;
    av_opts o = av_opts_default();
    o.jets = false;
    uint64_t v;
    for (int i = 2; i < argc; i++) {
        const char *s = argv[i];
        if (strncmp(s, "--profile=", 10) == 0 && s[10]) profile = s + 10;
        else if (strncmp(s, "--jets=", 7) == 0 && s[7] && nd < 16) dicts[nd++] = argv[i] + 7;
        else if (strcmp(s, "--ctors") == 0) ctors = 64;
        else if (strncmp(s, "--ctors=", 8) == 0 && number(s + 8, &v) && v) ctors = v;
        else if (strncmp(s, "--names=", 8) == 0 && s[8] && nn < 64) namefiles[nn++] = argv[i] + 8;
        else if (strcmp(s, "--jet-stats") == 0) stats_top = 40;
        else if (strncmp(s, "--jet-stats=", 12) == 0 && number(s + 12, &v)) stats_top = v;
        else if (strncmp(s, "--fuel=", 7) == 0 && number(s + 7, &v)) o.max_steps = v;
        else if (strncmp(s, "--max-nodes=", 12) == 0 && number(s + 12, &v) && v <= AV_MAX_NODES)
            o.max_nodes = (uint32_t)v;
        else if (s[0] != '-' && !dir) dir = s;
        else if (s[0] != '-' && !source) source = s;
        else return usage();
    }
    if (!dir || !source) return usage();
    FILE *sf = fopen(source, "rb");
    if (!sf) { perror(source); return 1; }
    size_t slen;
    char *src = slurp(sf, &slen);
    fclose(sf);
    if (!src) return 1;
    static const char *const names[6] = { "front", "SCons", "SNil", "Code", "Lo", "Hi" };
    av_arena *a = av_arena_new(1u << 16);
    uint32_t terms[6];
    for (int i = 0; i < 6; i++) {
        char path[1100];
        snprintf(path, sizeof path, "%s/%s.skit", dir, names[i]);
        FILE *tf = fopen(path, "rb");
        size_t tl = 0;
        char *tb = tf ? slurp(tf, &tl) : NULL;
        if (tf) fclose(tf);
        terms[i] = tb && a ? av_cue(a, (const uint8_t *)tb, tl, NULL) : AV_NONE;
        free(tb);
        if (terms[i] == AV_NONE) {
            fprintf(stderr, "avon: %s: not a term\n", path);
            free(src);
            av_arena_free(a);
            return 1;
        }
    }
    av_front0 f;
    _Static_assert(sizeof f == sizeof terms, "six terms");
    memcpy(&f, terms, sizeof f);
    uint32_t t = av_front0_input(a, &f, src, slen);
    free(src);
    if (t == AV_NONE) {
        fprintf(stderr, "avon: %s: not ASCII, or out of memory\n", source);
        av_arena_free(a);
        return 1;
    }
    /* jets: constructors found in the program, then the dictionaries */
    av_root_push(a, &t);
    bool jets_ok = !ctors || av_jets_ctors(a, t, (size_t)ctors) >= 0;
    for (int d = 0; jets_ok && d < nd; d++) {
        const char *jerr = NULL;
        if (av_jets_load(a, dicts[d], 1, &jerr) < 0) {
            fprintf(stderr, "avon: %s: %s\n", dicts[d], jerr);
            jets_ok = false;
        }
    }
    av_root_pop(a);
    if (jets_ok && a->njets) {
        t = av_jets_match(a, t);
        o.jets = true;
    }
    av_jetstats *stats = stats_top ? av_jetstats_new() : NULL;
    if (!jets_ok || t == AV_NONE || (stats && !av_jetstats_begin(stats, a, t))) {
        av_jetstats_free(stats);
        av_arena_free(a);
        return 1;
    }
    o.jetstats = stats;
    av_profile *prof = NULL;
    if (profile && !(prof = profile_load(profile, a, t))) { av_arena_free(a); return 1; }
    o.profile = prof;
    uint64_t steps = 0;
    const char *err = NULL;
    int rc = av_front0_read(a, t, &o, stdout, &steps, &err);
    fprintf(stderr, "contractions %llu\n", (unsigned long long)steps);
    if (stats) {
        drow *rows = NULL;
        size_t nr = 0, nlabels = 0;
        jname *labels = NULL;
        if (!load_rows(dicts, nd, &rows, &nr) && !load_jnames(namefiles, nn, &labels, &nlabels))
            print_jetstats(stderr, stats, steps, (size_t)stats_top, rows, nr, labels, nlabels,
                           false, NULL, NULL, NULL);
        for (size_t i = 0; i < nr; i++) free(rows[i].term);
        free(rows);
        for (size_t i = 0; i < nlabels; i++) { free(labels[i].hash); free(labels[i].name); }
        free(labels);
        av_jetstats_free(stats);
    }
    if (rc < 0) fprintf(stderr, "avon: the result does not read: %s\n", err ? err : "?");
    if (prof) {
        av_profile_report(prof, stderr, SIZE_MAX);
        av_profile_free(prof);
    }
    av_arena_free(a);
    return rc < 0 ? 1 : 0;
}

/*  avon jetstat: what each jet does on the manifests' runs, together and,
 *  with --alone, each by itself (docs/DESIGN.md §6.7). */
static int jetstat_main(int argc, char **argv) {
    char *dicts[16], *manifests[256], *namefiles[64];
    int nd = 0, nm = 0, nn = 0;
    uint64_t ctors = 0, top = 40, v;
    bool share = false, alone = false, halting = false;
    for (int i = 2; i < argc; i++) {
        const char *s = argv[i];
        if (strncmp(s, "--jets=", 7) == 0 && s[7] && nd < 16) dicts[nd++] = argv[i] + 7;
        else if (strcmp(s, "--ctors") == 0) ctors = 64;
        else if (strncmp(s, "--ctors=", 8) == 0 && number(s + 8, &v) && v) ctors = v;
        else if (strncmp(s, "--names=", 8) == 0 && s[8] && nn < 64) namefiles[nn++] = argv[i] + 8;
        else if (strcmp(s, "--share") == 0) share = true;
        else if (strcmp(s, "--alone") == 0) alone = true;
        else if (strcmp(s, "--halting") == 0) halting = true;
        else if (strncmp(s, "--top=", 6) == 0 && number(s + 6, &v)) top = v;
        else if (s[0] != '-' && nm < 256) manifests[nm++] = argv[i];
        else return usage();
    }
    if (!nm || (!nd && !ctors)) return usage();

    drow *rows = NULL;
    size_t nr = 0;
    jname *names = NULL;
    size_t nnames = 0;
    if (load_rows(dicts, nd, &rows, &nr) || load_jnames(namefiles, nn, &names, &nnames)) return 1;

    jetcfg cfg = { dicts, nd, ctors, share, halting, false, 0, 0 };
    av_jetstats *all = av_jetstats_new();
    uint64_t total;
    int runs, wrong;
    if (!all || jet_pass(manifests, nm, &cfg, all, &total, &runs, &wrong)) return 1;

    /* each dictionary row alone: its fires and absorbed contractions */
    uint64_t *alone_fires = calloc(nr ? nr : 1, sizeof *alone_fires);
    uint64_t *alone_abs = calloc(nr ? nr : 1, sizeof *alone_abs);
    bool *alone_seen = calloc(nr ? nr : 1, sizeof *alone_seen);
    if (!alone_fires || !alone_abs || !alone_seen) return 1;
    for (size_t i = 0; alone && i < nr; i++) {
        bool dup = false;
        for (size_t j = 0; j < i; j++) dup |= rows[j].digest == rows[i].digest;
        if (dup) continue;
        jetcfg one = { dicts, nd, 0, share, halting, true, rows[i].file, rows[i].digest };
        av_jetstats *s1 = av_jetstats_new();
        uint64_t t1;
        int r1, w1;
        if (!s1 || jet_pass(manifests, nm, &one, s1, &t1, &r1, &w1)) return 1;
        wrong += w1;
        size_t k;
        if (av_jetstats_find(s1, rows[i].hash, &k)) {
            char h[27];
            unsigned ar;
            uint64_t cost;
            size_t atoms;
            av_jetstat_row c;
            av_jetstats_row(s1, k, h, &ar, &cost, &atoms, &c);
            alone_fires[i] = c.fires;
            alone_abs[i] = c.absorbed;
            alone_seen[i] = true;
        }
        av_jetstats_free(s1);
    }

    printf("jetstat: %s mode, %d %sruns, %llu contractions, %d counts off the manifests%s\n",
           share ? "share" : "copy", runs, halting ? "halting " : "", (unsigned long long)total, wrong,
           av_jetstats_lost(all) ? "; ORIGINS LOST TO MEMORY" : "");
    print_jetstats(stdout, all, total, (size_t)top, rows, nr, names, nnames, alone,
                   alone_seen, alone_abs, alone_fires);
    free(alone_fires);
    free(alone_abs);
    free(alone_seen);
    for (size_t i = 0; i < nr; i++) free(rows[i].term);
    free(rows);
    for (size_t i = 0; i < nnames; i++) { free(names[i].hash); free(names[i].name); }
    free(names);
    av_jetstats_free(all);
    return wrong ? 1 : 0;
}

int main(int argc, char **argv) {
    if (argc == 2 && strcmp(argv[1], "--version") == 0) {
        printf("avon %s\n", AVON_VERSION);
        return 0;
    }
    if (argc < 2) return usage();
    if (strcmp(argv[1], "census") == 0) return census_main(argc, argv);
    if (strcmp(argv[1], "jetstat") == 0) return jetstat_main(argc, argv);
    if (strcmp(argv[1], "scry") == 0) return scry_main(argc, argv);
    if (strcmp(argv[1], "selfhost") == 0) return selfhost_main(argc, argv);
    if (strcmp(argv[1], "front0") == 0) return front0_main(argc, argv);
    if (strcmp(argv[1], "boot") == 0 || strcmp(argv[1], "poke") == 0 ||
        strcmp(argv[1], "peek") == 0 || strcmp(argv[1], "load") == 0)
        return kernel_main(argc, argv);
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
            av_probe pr = { .n = 0 };
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
