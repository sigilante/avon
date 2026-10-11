/**  term.c
 *
 *  The commands on one term---reduce, batch, jam, cue, prefix and
 *  witness---over one set of options, args, each refused where its command
 *  would ignore it (options_fit).
 */

#include "cli.h"

/*  Each option parse_args takes, a bit of args.given, so options_fit can
 *  refuse one the command would ignore. */
enum {
    O_STRATEGY, O_WHNF, O_BIRDS, O_JETS, O_CTORS, O_NO_JETS, O_PROFILE, O_TEMPLATES,
    O_DATA, O_FIX, O_MEMORY, O_NO_DEFER, O_P2, O_INTERP, O_JET_TABLE, O_PLAN,
    O_STATEMENT, O_JET_FLOOR, O_JET_CHECK, O_FUEL, O_MAX_NODES, O_BUDGET, O_ROWS,
    O_CELLS, O_TRACE, O_PASSENGER, O_RECORDS, O_FRAME_DUMP, O_FILE, O_COUNT
};
static const char *const option_name[O_COUNT] = {
    "--strategy", "--whnf", "--allow-bird-atoms", "--jets", "--ctors", "--no-jets",
    "--profile", "--templates", "--data", "--fix", "--memory", "--no-defer", "--p2",
    "--interp", "--jet-table", "--plan", "--statement", "--jet-floor", "--jet-check",
    "--fuel", "--max-nodes", "--budget", "--rows", "--cells", "--trace-frame",
    "--passenger", "--records", "--frame-dump", "a FILE",
};
#define OPT(o) (1u << (o))

/*  The O_ of an argument parse_args accepted: its name up to any '='. */
static int option_of(const char *s) {
    if (s[0] != '-') return O_FILE;
    size_t n = strcspn(s, "=");
    for (int o = 0; o < O_FILE; o++)
        if (strlen(option_name[o]) == n && memcmp(s, option_name[o], n) == 0) return o;
    return O_FILE;                      /* unreachable: every option is named */
}

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
    const char *statement;        /* lean-ski's composed statement, or NULL */
    uint64_t    jet_floor;
    const char *profile;          /* --profile: a names file, or NULL */
    const char *templates;        /* --templates: a directory, or NULL */
    bool        data;             /* --data: data jets */
    bool        fix;              /* --fix: Y unfolded in one step */
    const char *p2;               /* --p2: P's term, a file, or NULL */
    const char *file;
    /* frame traces */
    int         trace;            /* 0 off, 1 summary, 2 a line per step */
    const char *passenger;
    size_t      records;          /* the confirmation window; 0: no records */
    uint64_t    dump_steps[64];   /* --frame-dump steps */
    size_t      ndump;
    bool        dump_records, dump_halt, dump_restart, dump_census;
    uint32_t    given;            /* OPT(O_...) of each option given */
} args;

static bool parse_args(int argc, char **argv, args *g) {
    g->o = av_opts_default();
    g->budget = 1000000;
    g->birds = false;
    g->njets = 0;
    g->ctors = 0;
    g->interp = NULL;
    g->profile = NULL;
    g->templates = NULL;
    g->data = false;
    g->fix = false;
    g->p2 = NULL;
    g->jet_table = NULL;
    g->plan = NULL;
    g->statement = NULL;
    g->jet_floor = 8;
    g->rows = 1u << 21;          /* bench/plonky3's MAX_LOG_HEIGHT */
    g->cells = 1u << 21;
    g->file = NULL;
    g->trace = 0;
    g->passenger = "X";
    g->records = 0;
    g->ndump = 0;
    g->dump_records = g->dump_halt = g->dump_restart = g->dump_census = false;
    g->given = 0;
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
        else if (strncmp(s, "--templates=", 12) == 0 && s[12]) g->templates = s + 12;
        else if (strcmp(s, "--data") == 0)           g->data = true;
        else if (strcmp(s, "--fix") == 0)            g->fix = true;
        else if (strcmp(s, "--memory") == 0)         g->fix = g->o.fix_shared = true;
        else if (strcmp(s, "--no-defer") == 0)       g->o.no_defer = true;
        else if (strncmp(s, "--p2=", 5) == 0 && s[5])  g->p2 = s + 5;
        else if (strncmp(s, "--interp=", 9) == 0 && s[9]) {
            g->interp = s + 9;
            g->o.interp_jets = true;
        }
        else if (strncmp(s, "--jet-table=", 12) == 0 && s[12]) g->jet_table = s + 12;
        else if (strncmp(s, "--plan=", 7) == 0 && s[7]) g->plan = s + 7;
        else if (strncmp(s, "--statement=", 12) == 0 && s[12]) g->statement = s + 12;
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
        else if (strcmp(s, "--trace-frame") == 0)    g->trace = 2;
        else if (strcmp(s, "--trace-frame=summary") == 0) g->trace = 1;
        else if (strncmp(s, "--passenger=", 12) == 0 && s[12])
            g->passenger = s + 12;
        else if (strcmp(s, "--records") == 0)        g->records = 150;
        else if (strncmp(s, "--records=", 10) == 0 && number(s + 10, &v) && v)
            g->records = (size_t)v;
        else if (strncmp(s, "--frame-dump=", 13) == 0 && s[13]) {
            /* a comma list of steps and the keywords records, halt, last-restart */
            const char *q = s + 13;
            while (*q) {
                const char *e = strchr(q, ',');
                size_t n = e ? (size_t)(e - q) : strlen(q);
                if (n == 7 && memcmp(q, "records", 7) == 0) g->dump_records = true;
                else if (n == 6 && memcmp(q, "census", 6) == 0) g->dump_census = true;
                else if (n == 4 && memcmp(q, "halt", 4) == 0) g->dump_halt = true;
                else if (n == 12 && memcmp(q, "last-restart", 12) == 0) g->dump_restart = true;
                else {
                    char tmp[32];
                    if (n == 0 || n >= sizeof tmp || g->ndump == 64) return false;
                    memcpy(tmp, q, n);
                    tmp[n] = '\0';
                    if (!number(tmp, &v)) return false;
                    g->dump_steps[g->ndump++] = v;
                }
                q += n;
                if (*q == ',') q++;
            }
        }
        else if (s[0] != '-' && !g->file) g->file = s;
        else return false;
        g->given |= OPT(option_of(s));
    }
    return true;
}

/*  Refuse an option the command would ignore, naming the first such.
 *  reduce and batch read the reduction's options; batch reads its terms
 *  from stdin, not a FILE.  --trace-frame runs copy mode's head run with
 *  no jets, templates or profile and prints no term (--strategy=copy,
 *  --whnf and --no-jets agree with it), and the frame-trace options mean
 *  nothing without it.  jam, cue and prefix read a term and print it;
 *  witness reads its budgets and lean-ski's files, and with --statement
 *  only the statement, the jet table and a witness. */
static bool options_fit(const args *g, const char *cmd) {
    const uint32_t frames = OPT(O_PASSENGER) | OPT(O_RECORDS) | OPT(O_FRAME_DUMP);
    const uint32_t untraced = OPT(O_TEMPLATES) | OPT(O_DATA) | OPT(O_FIX) | OPT(O_MEMORY) |
                              OPT(O_NO_DEFER) | OPT(O_P2) | OPT(O_PROFILE) | OPT(O_JETS) |
                              OPT(O_CTORS) | OPT(O_INTERP) |
                              OPT(O_JET_FLOOR) | OPT(O_JET_CHECK) | OPT(O_BUDGET);
    const uint32_t reducing = (OPT(O_FILE) - 1) & ~(OPT(O_JET_TABLE) | OPT(O_PLAN) |
                              OPT(O_STATEMENT) | OPT(O_ROWS) | OPT(O_CELLS));
    bool reduce = strcmp(cmd, "reduce") == 0, batch = strcmp(cmd, "batch") == 0;
    uint32_t takes, moded = 0;          /* moded: refused for the mode, not the command */
    const char *mode = "";
    if (reduce || batch) {
        takes = reducing | (reduce ? OPT(O_FILE) : 0);
        moded = g->trace ? untraced : frames;
        mode = g->trace ? " with --trace-frame" : " without --trace-frame";
        takes &= ~moded;
    } else if (strcmp(cmd, "jam") == 0 || strcmp(cmd, "cue") == 0 ||
               strcmp(cmd, "prefix") == 0) {
        takes = OPT(O_BIRDS) | OPT(O_BUDGET) | OPT(O_FILE);
    } else if (strcmp(cmd, "witness") == 0 && g->statement) {
        takes = OPT(O_STATEMENT) | OPT(O_JET_TABLE) | OPT(O_FILE);
        moded = ~takes;
        mode = " with --statement";
    } else if (strcmp(cmd, "witness") == 0) {
        takes = OPT(O_BIRDS) | OPT(O_ROWS) | OPT(O_CELLS) | OPT(O_JET_TABLE) | OPT(O_PLAN) |
                OPT(O_FILE);
    } else {
        return true;                    /* run_main answers with the usage */
    }
    uint32_t idle = g->given & ~takes;
    const char *name = NULL;
    if (idle) {
        int o = 0;
        while (!(idle & OPT(o))) o++;
        name = option_name[o];
        if (!(moded & OPT(o))) mode = "";
        if (o == O_FILE && batch) mode = ", which reads its terms from stdin";
    } else if (g->trace && (g->given & OPT(O_STRATEGY)) && g->o.strategy == AV_SHARE) {
        name = "--strategy=share";      /* the trace runs copy mode */
        mode = " with --trace-frame";
    }
    if (!name) return true;
    fprintf(stderr, "avon: %s has no effect on %s%s\n", name, cmd, mode);
    return false;
}

/*  An arena for one term: the bird-atom rule, and the dictionaries
 *  --jets and --interp name loaded.  NULL, with a message, on failure. */
static av_arena *new_arena(const args *g) {
    av_arena *a = av_arena_new(ARENA_START);
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

/*  A profile of t named by a names file, `kind TAB name TAB hash`
 *  per line, as census --names reads. */
av_profile *profile_load(const char *path, const av_arena *a, uint32_t t) {
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

/*  Supercombinator templates from dir, loaded after every other jet,
 *  then *t matched and the templates bound to it.  counts: accepted,
 *  refused, skipped, unbound.  False, with a message, on failure. */
bool use_templates(av_arena *a, const char *dir, uint32_t *t, long counts[4],
                          bool data, long wc[3], bool fix) {
    const char *err = NULL;
    if (fix) av_fix_on(a);
    if (data && !av_words_on(a)) {
        fprintf(stderr, "avon: out of memory\n");
        return false;
    }
    av_tmplset *ts = av_templates_load(a, dir, &err);
    if (!ts) {
        fprintf(stderr, "avon: %s: %s\n", dir, err ? err : "cannot load templates");
        return false;
    }
    if (fix && !av_templates_fix(ts)) {
        fprintf(stderr, "avon: Y is already another jet; --fix cannot register it\n");
        av_templates_free(ts);
        return false;
    }
    *t = av_jets_match(a, *t);
    bool ok = *t != AV_NONE && av_templates_bind(a, ts, *t);
    if (ok) av_templates_counts(ts, &counts[0], &counts[1], &counts[2], &counts[3]);
    else fprintf(stderr, "avon: could not bind the templates\n");
    if (ok && data) {           /* data jets: the numerals, as words */
        av_templates_word_counts(ts, &wc[0], &wc[1]);
        wc[2] = av_words_scan(a, *t);
        ok = wc[2] >= 0 && av_words_mark(a);
        if (!ok) fprintf(stderr, "avon: out of memory\n");
    }
    av_templates_free(ts);
    return ok;
}

/*  The Poseidon2 jet: P's term from path, registered.  Its id, or
 *  AV_NONE with a message. */
static uint32_t use_p2(av_arena *a, const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) {
        fprintf(stderr, "avon: %s: cannot open\n", path);
        return AV_NONE;
    }
    size_t len;
    char *src = slurp(f, &len);
    fclose(f);
    if (!src) {
        fprintf(stderr, "avon: out of memory\n");
        return AV_NONE;
    }
    uint32_t p = load(a, src, len);
    free(src);
    if (p == AV_NONE) return AV_NONE;
    const char *err = NULL;
    uint32_t id = av_p2_register(a, p, &err);
    if (id == AV_NONE) fprintf(stderr, "avon: %s: %s\n", path, err);
    return id;
}

/*  The data jets' report line. */
void report_data(const long wc[3], const av_result *r) {
    fprintf(stderr, "data: %ld numeral operations admitted, %ld refused; %ld numerals "
            "made words; %llu dispatches (%llu fused), %llu numeral operations "
            "among the contractions; %llu cases joined to their instances\n",
            wc[0], wc[1], wc[2],
            (unsigned long long)r->dispatches, (unsigned long long)r->fused,
            (unsigned long long)r->word_ops, (unsigned long long)r->joins);
}

/*  The unfolding's report line. */
void report_fix(const av_result *r) {
    fprintf(stderr, "fix: %llu unfoldings of Y among the contractions\n",
            (unsigned long long)r->fix_calls);
}

/*  The input line a term came from: 1 for reduce, counted by batch. */
static uint64_t term_line = 1;

/*  One frame-trace run: copy mode, the head run, no collection. */
static bool trace_pass(const args *g, const char *src, size_t len, bool out,
                       const uint64_t *dumps, size_t ndumps, bool dump_halt,
                       uint64_t **rec_steps, size_t *nrec, int64_t *restart, bool census) {
    av_arena *a = av_arena_new(ARENA_START);
    if (!a) { fprintf(stderr, "avon: out of memory\n"); return false; }
    a->allow_bird_atoms = g->birds;
    uint32_t t = load(a, src, len);
    av_trace *tr = t == AV_NONE ? NULL
                 : av_trace_new(a, g->passenger, out && g->trace == 2, out ? stdout : NULL);
    bool ok = tr != NULL;
    if (ok && !av_trace_check(tr, a, t)) {
        fprintf(stderr, "avon: --trace-frame takes terms of S and the passenger %s only\n",
                g->passenger);
        ok = false;
    }
    if (ok && ndumps && !av_trace_dump_at(tr, dumps, ndumps)) ok = false;
    if (ok) {
        av_trace_dump_halt(tr, dump_halt);
        av_opts o = g->o;
        o.strategy = AV_COPY;
        o.whnf_only = true;
        o.no_collect = true;
        o.jets = false;
        o.trace = tr;
        av_result r = av_reduce(a, t, &o);
        av_trace_summary sum;
        if (r.status == AV_INTERRUPTED ||
            !av_trace_end(tr, a, r.status, r.steps, r.term, g->records, out && g->records, &sum)) {
            fprintf(stderr, "avon: the trace could not follow the run\n");
            ok = false;
        }
        /* records only for a run that reached the horizon, as the census */
        if (ok && rec_steps && sum.kind[0] == 'F')
            *nrec = census ? av_trace_census_steps(tr, g->records ? g->records : 150, rec_steps)
                           : av_trace_record_steps(tr, g->records ? g->records : 150, rec_steps);
        if (ok && restart) *restart = sum.last_restart;
        av_trace_flush(tr);
    }
    av_trace_free(tr);
    av_arena_free(a);
    return ok;
}

/*  --trace-frame: a pass for the steps the keywords name, when any does,
 *  then the pass that prints; copy mode is deterministic and never
 *  collects here, so node ids are the same in both. */
static int run_trace(const args *g, const char *src, size_t len) {
    uint64_t *dumps = NULL;
    size_t nd = g->ndump;
    bool ok = true;
    printf("> %llu\n", (unsigned long long)term_line);     /* every block framed */
    fflush(stdout);
    if (g->dump_records || g->dump_census || g->dump_restart) {
        uint64_t *rec = NULL;
        size_t nrec = 0;
        int64_t restart = -1;
        ok = trace_pass(g, src, len, false, NULL, 0, false,
                        g->dump_records || g->dump_census ? &rec : NULL, &nrec, &restart,
                        g->dump_census && !g->dump_records);
        if (ok) {
            dumps = malloc((nd + nrec + 1) * sizeof *dumps);
            if (!dumps) ok = false;
        }
        if (ok) {
            memcpy(dumps, g->dump_steps, nd * sizeof *dumps);
            if (rec) memcpy(dumps + nd, rec, nrec * sizeof *dumps);
            nd += nrec;
            if (g->dump_restart && restart >= 0) dumps[nd++] = (uint64_t)restart;
        }
        free(rec);
    } else if (nd) {
        dumps = malloc(nd * sizeof *dumps);
        if (!dumps) ok = false;
        else memcpy(dumps, g->dump_steps, nd * sizeof *dumps);
    }
    if (ok) ok = trace_pass(g, src, len, true, dumps, nd, g->dump_halt, NULL, NULL, NULL, false);
    free(dumps);
    if (!ok) printf("! no trace\n");
    printf("$\n");                                         /* the block ends */
    fflush(stdout);
    return ok ? 0 : 1;
}

/*  Reduce one term and print "STATUS steps term" (sep between). */
static int run_one(const args *g, const char *src, size_t len, char sep) {
    if (g->trace) return run_trace(g, src, len);
    av_arena *a = new_arena(g);
    if (!a) return 1;
    uint32_t t = load(a, src, len);
    long ctors = 0;
    if (t != AV_NONE && g->ctors) {
        av_root_push(a, &t);                /* the scan's runs collect */
        ctors = av_jets_ctors(a, t, (size_t)g->ctors);
        av_root_pop(a);
        if (ctors < 0) t = AV_NONE;
    }
    long tc[4] = { 0, 0, 0, 0 }, wc[3] = { 0, 0, 0 };
    if (g->templates && g->o.strategy != AV_SHARE) {
        fprintf(stderr, "avon: --templates runs in share mode only; copy mode keeps its counts\n");
        av_arena_free(a);
        return 1;
    }
    if (g->data && !g->templates) {
        fprintf(stderr, "avon: --data needs --templates=DIR, which holds words.tsv\n");
        av_arena_free(a);
        return 1;
    }
    if (g->fix && !g->templates) {
        fprintf(stderr, "avon: %s needs --templates=DIR: Y is registered with them\n",
                g->o.fix_shared ? "--memory" : "--fix");
        av_arena_free(a);
        return 1;
    }
    if (g->p2 && g->o.strategy != AV_SHARE) {
        fprintf(stderr, "avon: --p2 runs in share mode only\n");
        av_arena_free(a);
        return 1;
    }
    uint32_t p2id = AV_NONE;
    if (t != AV_NONE && g->p2) {
        av_root_push(a, &t);
        p2id = use_p2(a, g->p2);
        av_root_pop(a);
        if (p2id == AV_NONE) t = AV_NONE;
    }
    if (t != AV_NONE && g->templates) {
        if (!use_templates(a, g->templates, &t, tc, g->data, wc, g->fix)) t = AV_NONE;
    } else if (t != AV_NONE && (g->njets || g->ctors || g->p2)) {
        t = av_jets_match(a, t);
    }
    long p2kept = 0;
    if (t != AV_NONE && g->p2 && (p2kept = av_p2_bind(a, t, p2id)) < 0) {
        fprintf(stderr, "avon: out of memory\n");
        t = AV_NONE;
    }
    if (t == AV_NONE) {
        av_arena_free(a);
        return 1;
    }
    av_opts o = g->o;
    o.templates = g->templates != NULL;
    o.data = g->data;
    o.fix = g->fix;
    o.p2 = g->p2 != NULL;
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
    if (g->templates)
        fprintf(stderr, "templates: %ld accepted, %ld refused, %ld skipped, %ld unbound; "
                "%llu instantiations among the contractions\n", tc[0], tc[1], tc[2], tc[3],
                (unsigned long long)r.tmpl_calls);
    if (g->data) report_data(wc, &r);
    if (g->fix) report_fix(&r);
    if (g->p2)
        fprintf(stderr, "p2: %ld occurrences of P bound (%s); %llu permutations run natively "
                "among the contractions, %llu declined (an argument neither a state nor a chain "
                "of calls ending in one), %llu unbound at a call\n",
                p2kept, AV_P2_DIGEST, (unsigned long long)r.p2_calls,
                (unsigned long long)r.p2_declines, (unsigned long long)r.p2_unbound);
    av_buf b = { 0 };
    bool whole = r.term != AV_NONE && av_print(a, r.term, g->budget, &b);
    printf("%s %" PRIu64 "%c%s%s\n", av_status_name(r.status), r.steps, sep,
           b.s ? b.s : "", whole ? "" : " ...");
    av_buf_free(&b);
    av_arena_free(a);
    /* the run's status is the line's, a script's to read: exit 1 is for a
     * failure of Avon's own, here a jet that disagreed with its term */
    return r.jet_fault ? 1 : 0;
}

static char *read_text(const char *path, size_t *len) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    char *s = slurp(f, len);
    fclose(f);
    return s;
}

/*  avon witness --statement=PUBLIC [--jet-table=JETS]: the composed table
 *  for the witness wsrc, on stdout: with code jets from JETS, or, for a
 *  `p2pre` or `p2commit` statement and no jet table, with the Poseidon2
 *  jet. */
static int composed_witness(const args *g, const char *wsrc, size_t wlen) {
    size_t slen = 0, jlen = 0;
    char *ssrc = read_text(g->statement, &slen);
    char *jsrc = NULL;
    av_cstmt st;
    av_jettable jt;
    bool have_st = false, have_jt = false;
    av_cell *priv = NULL;
    size_t *ends = NULL;
    av_witness w = { 0 };
    av_buf b = { 0 };
    uint64_t insts = 0;
    const char *msg = NULL;
    int rc = 1;
    if (!ssrc) { fprintf(stderr, "avon: cannot read %s\n", g->statement); goto out; }
    if (!(have_st = av_cstmt_read(ssrc, slen, &st, &msg))) {
        fprintf(stderr, "avon: %s: %s\n", g->statement, msg);
        goto out;
    }
    /* a statement with the Poseidon2 jet has no code jets; any other needs
       its jet table */
    if (st.p2 && g->jet_table) {
        fprintf(stderr, "avon: a statement with the Poseidon2 jet takes no --jet-table\n");
        goto out;
    }
    if (!st.p2 && !g->jet_table) {
        fprintf(stderr, "avon: --statement needs --jet-table\n");
        goto out;
    }
    if (st.p2 && !av_p2_selftest()) {
        fprintf(stderr, "avon: Poseidon2 fails its test vectors\n");
        goto out;
    }
    if (!st.p2) {
        jsrc = read_text(g->jet_table, &jlen);
        if (!jsrc) { fprintf(stderr, "avon: cannot read %s\n", g->jet_table); goto out; }
        if (!(have_jt = av_jettable_read(jsrc, jlen, &jt, &msg))) {
            fprintf(stderr, "avon: %s: %s\n", g->jet_table, msg);
            goto out;
        }
    }
    priv = calloc((size_t)st.nbits + st.w + 1, sizeof *priv);
    if (!priv) { fprintf(stderr, "avon: out of memory\n"); goto out; }
    if (!av_cwitness_read(wsrc, wlen, &st, priv, &msg)) {
        fprintf(stderr, "avon: the witness: %s\n", msg);
        goto out;
    }
    av_status s = st.p2 ? av_witness_run_p2(&st, priv, &w, &ends, &msg)
                        : av_witness_run_composed(&st, priv, &jt, &w, &ends, &insts, &msg);
    if (s != AV_WHNF) {
        fprintf(stderr, "avon: no witness: %s\n", msg);
    } else if (!av_composed_table(&st, &w, ends, &b)) {
        fprintf(stderr, "avon: could not write the table\n");
    } else {
        fwrite(b.s, 1, b.len, stdout);
        if (st.p2)
            fprintf(stderr, "rows %zu cells %zu segments %zu jet calls %llu\n", w.nrows, w.nmem, st.nroots,
                    (unsigned long long)w.p2calls);
        else
            fprintf(stderr, "rows %zu cells %zu segments %zu insts %llu pops %llu written %llu\n",
                    w.nrows, w.nmem, st.nroots, (unsigned long long)insts,
                    (unsigned long long)w.pops, (unsigned long long)w.wcells);
        rc = 0;
    }
out:
    av_witness_free(&w);
    free(ends);
    free(priv);
    if (have_jt) av_jettable_free(&jt);
    if (have_st) av_cstmt_free(&st);
    av_buf_free(&b);
    free(ssrc);
    free(jsrc);
    return rc;
}

/*  avon reduce | batch | jam | cue | prefix | witness. */
int term_main(int argc, char **argv) {
    args g;
    if (!parse_args(argc, argv, &g)) return usage();
    if (!options_fit(&g, argv[1])) return 2;

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
        } else if (strcmp(cmd, "witness") == 0 && g.statement) {
            rc = composed_witness(&g, src, len);
        } else if (strcmp(cmd, "witness") == 0) {
            av_arena *a = new_arena(&g);
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
            av_arena *a = new_arena(&g);
            uint32_t t = a ? load(a, src, len) : AV_NONE;
            av_buf b = { 0 };
            rc = t != AV_NONE && av_prefix(a, t, g.budget, &b) ? 0 : 1;
            if (rc == 0) printf("%s\n", b.s);
            else if (t != AV_NONE) fprintf(stderr, "avon: node budget exceeded or not closed\n");
            av_buf_free(&b);
            av_arena_free(a);
        } else {
            av_arena *a = new_arena(&g);
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
        term_line = 0;
        while ((n = getline(&line, &cap, stdin)) > 0) {
            term_line++;
            if (run_one(&g, line, (size_t)n, ' ')) rc = 1;
            fflush(stdout);
        }
        free(line);
        return rc;
    }
    return usage();
}
