/**  census.c
 *
 *  avon census: which terms the manifests' runs call, ranked by what a jet
 *  on each would absorb.
 */

#include "cli.h"

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
            av_arena *a = av_arena_new(ARENA_START);
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

int census_main(int argc, char **argv) {
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
    if (nnames) qsort(names, nnames, sizeof *names, named_order);
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
