/**  jetstat.c
 *
 *  avon jetstat: what each jet does on the manifests' runs; and the rows,
 *  names and table front0 reads too.
 */

#include "cli.h"

typedef struct {
    char   **dicts;
    int      ndicts;
    uint64_t ctors;             /* constructor jets up to N atoms; 0 none  */
    bool     share;
    bool     halting;           /* only the runs the manifest says halt    */
    bool     only;              /* register just one dictionary row        */
    int      only_file;
    av_digest only_digest;
} jetcfg;

/*  One pass over the manifests' runs with cfg's jets, into s.  A copy-mode
 *  count must be the manifest's: a fire charges the contractions it
 *  absorbs, so jets keep counts. */
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
            av_arena *a = av_arena_new(ARENA_START);
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
int load_rows(char **dicts, int nd, drow **out, size_t *count) {
    drow *rows = NULL;
    size_t nr = 0, rcap = 0;
    for (int d = 0; d < nd; d++) {
        FILE *f = fopen(dicts[d], "rb");
        if (!f) { perror(dicts[d]); return 1; }
        char *line = NULL;
        size_t cap = 0;
        while (getline(&line, &cap, f) > 0) {
            char *t1 = strchr(line, '\t'), *t2 = t1 ? strchr(t1 + 1, '\t') : NULL;
            if (!t2 || t1 - line != AV_HASH_LEN) continue;
            if (nr == rcap) {
                drow *q = realloc(rows, (rcap = rcap ? 2 * rcap : 256) * sizeof *q);
                if (!q) return 1;
                rows = q;
            }
            drow *r = &rows[nr];
            memcpy(r->hash, line, AV_HASH_LEN);
            r->hash[AV_HASH_LEN] = '\0';
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
int load_jnames(char **namefiles, int nn, jname **out, size_t *count) {
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
    char h[AV_HASH_LEN + 1];
    unsigned ar;
    uint64_t cost;
    size_t atoms;
    av_jetstat_row a, b;
    av_jetstats_row(sort_stats, *(const size_t *)x, h, &ar, &cost, &atoms, &a);
    av_jetstats_row(sort_stats, *(const size_t *)y, h, &ar, &cost, &atoms, &b);
    /* ties in row order: qsort is not stable, and libcs break ties apart */
    size_t i = *(const size_t *)x, j = *(const size_t *)y;
    return a.absorbed != b.absorbed ? (a.absorbed < b.absorbed) - (a.absorbed > b.absorbed)
                                    : (i > j) - (i < j);
}

static int by_pair_fires(const void *x, const void *y) {
    const av_jetstat_pair *p = x, *q = y;
    if (p->fires != q->fires) return (p->fires < q->fires) - (p->fires > q->fires);
    if (p->outer != q->outer) return (p->outer > q->outer) - (p->outer < q->outer);
    if (p->inner != q->inner) return (p->inner > q->inner) - (p->inner < q->inner);
    return (p->kind > q->kind) - (p->kind < q->kind);
}

static int by_site(const void *x, const void *y) {
    const av_jetstat_site *p = x, *q = y;
    if (p->n != q->n) return (p->n < q->n) - (p->n > q->n);
    if (p->caller != q->caller) return (p->caller > q->caller) - (p->caller < q->caller);
    if (p->formal != q->formal) return (p->formal > q->formal) - (p->formal < q->formal);
    if (p->callee != q->callee) return (p->callee > q->callee) - (p->callee < q->callee);
    return (p->args > q->args) - (p->args < q->args);
}

static double pct(uint64_t n, uint64_t of) { return of ? 100.0 * (double)n / (double)of : 0.0; }

/*  Template instances by their body's head, and the known functions their
 *  formals held there: how many indirect calls a specialization on the
 *  argument could make direct (docs/SKA.md). */
static void print_heads(FILE *out, const av_jetstats *all, size_t top, const drow *rows,
                        size_t nr, const jname *names, size_t nnames) {
    av_jetstat_heads h;
    av_jetstats_heads(all, &h);
    if (!h.instances) return;
    fprintf(out, "\ntemplate instances by their body's head: %llu\n",
            (unsigned long long)h.instances);
    fprintf(out, "%10llu %5.1f%%  a closed term: a known call\n",
            (unsigned long long)h.known, pct(h.known, h.instances));
    fprintf(out, "%10llu %5.1f%%  a formal: a call to what its argument holds\n",
            (unsigned long long)h.formal, pct(h.formal, h.instances));
    fprintf(out, "%10llu %5.1f%%  no application\n",
            (unsigned long long)h.bare, pct(h.bare, h.instances));
    static const char *const held[AV_HELD_KINDS] = {
        "a constructor with its fields",
        "a numeral or list word",
        "a template or residual jet short of its arguments: a known function",
        "S, K or I short of their arguments",
        "a head with all its arguments: not yet a value",
        "an atom, a native operation or Y",
    };
    fprintf(out, "what the formal held\n");
    for (unsigned k = 0; k < AV_HELD_KINDS; k++)
        fprintf(out, "%10llu %5.1f%%  %s\n", (unsigned long long)h.held[k],
                pct(h.held[k], h.formal), held[k]);
    av_jetstat_site *sites;
    size_t ns = av_jetstats_sites(all, &sites);
    if (!ns) { free(sites); return; }
    qsort(sites, ns, sizeof *sites, by_site);
    uint64_t in10 = 0, in100 = 0;
    for (size_t k = 0; k < ns; k++) {
        if (k < 10) in10 += sites[k].n;
        if (k < 100) in100 += sites[k].n;
    }
    uint64_t fn = h.held[AV_HELD_FUNCTION];
    fprintf(out, "known functions at a formal: %llu (%.1f%%) given all their arguments by the "
            "head, a call made at once; the rest short of them\n",
            (unsigned long long)h.full, pct(h.full, fn));
    fprintf(out, "%zu sites (caller, formal, callee and the arguments it held); the top 10 "
            "hold %.1f%%, the top 100 %.1f%%\n", ns, pct(in10, fn), pct(in100, fn));
    for (size_t k = 0; k < ns && k < top; k++) {
        char hc[AV_HASH_LEN + 1], hf[AV_HASH_LEN + 1], lc[64], lf[64];
        unsigned ar;
        uint64_t cost;
        size_t atoms;
        av_jetstat_row cc, cf;
        av_jetstats_row(all, sites[k].caller, hc, &ar, &cost, &atoms, &cc);
        av_jetstats_row(all, sites[k].callee, hf, &ar, &cost, &atoms, &cf);
        jet_label(lc, sizeof lc, hc, cc.ctor, names, nnames, rows, nr);
        jet_label(lf, sizeof lf, hf, cf.ctor, names, nnames, rows, nr);
        fprintf(out, "%10llu  %-5s %s, holding %u  <-  formal %u of %s\n",
                (unsigned long long)sites[k].n, sites[k].full ? "call" : "short", lf,
                sites[k].args, sites[k].formal, lc);
    }
    free(sites);
}

/*  The jets' table, most absorbed first, then the nested fires; with the
 *  alone arrays (per dictionary row), each jet's run by itself beside. */
void print_jetstats(FILE *out, const av_jetstats *all, uint64_t total, size_t top,
                           const drow *rows, size_t nr, const jname *names, size_t nnames,
                           bool alone, const bool *alone_seen, const uint64_t *alone_abs,
                           const uint64_t *alone_fires) {
    size_t n = av_jetstats_rows(all);
    size_t *order = malloc((n ? n : 1) * sizeof *order);
    if (!order) return;
    for (size_t i = 0; i < n; i++) order[i] = i;
    sort_stats = all;
    if (n) qsort(order, n, sizeof *order, by_absorbed);
    uint64_t sum_together = 0, sum_alone = 0, sum_alone_together = 0, sum_fires = 0;
    for (size_t i = 0; i < n; i++) {
        char h[AV_HASH_LEN + 1];
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
        char h[AV_HASH_LEN + 1], label[64];
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
    if (np) qsort(pairs, np, sizeof *pairs, by_pair_fires);
    fprintf(out, "\nnested fires: the inner jet fired from the outer's residual (after it "
           "fired) or term (after it missed)\n");
    for (size_t k = 0; k < np && k < top; k++) {
        char ho[AV_HASH_LEN + 1], hi[AV_HASH_LEN + 1], lo[64], li[64];
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
    print_heads(out, all, top, rows, nr, names, nnames);
    free(order);
}

/*  avon jetstat: what each jet does on the manifests' runs, together and,
 *  with --alone, each by itself. */
int jetstat_main(int argc, char **argv) {
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

    jetcfg cfg = { dicts, nd, ctors, share, halting, false, 0, { 0, 0 } };
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
        for (size_t j = 0; j < i; j++) dup |= av_digest_eq(rows[j].digest, rows[i].digest);
        if (dup) continue;
        jetcfg one = { dicts, nd, 0, share, halting, true, rows[i].file, rows[i].digest };
        av_jetstats *s1 = av_jetstats_new();
        uint64_t t1;
        int r1, w1;
        if (!s1 || jet_pass(manifests, nm, &one, s1, &t1, &r1, &w1)) return 1;
        wrong += w1;
        size_t k;
        if (av_jetstats_find(s1, rows[i].hash, &k)) {
            char h[AV_HASH_LEN + 1];
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
