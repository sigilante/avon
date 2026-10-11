/**  test_scry.c
 *
 *  Scry's acceptance: the resume loop replays every run skijack's
 *  tests/test_scry.py pins---tests/conformance/namespaces.tsv, from
 *  `skijack.export`---event for event, including
 *  STUCK, the fuel policy and the round cap, and every level-1 attempt at
 *  the reference host's fuel, status and contraction count.  With the
 *  interpreter jet and the native lookup, every fire checked, the events
 *  are the same.  The fact store's log replays; a resolver whose term
 *  disagrees with the native lookup is not looked up natively; the
 *  resolver is aviary's abstraction.  Run from the repository root.
 */

#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "avon.h"
#include "test.h"

#define DIR "tests/conformance/"

static uint8_t *slurp(const char *path, size_t *len) {
    FILE *f = test_open(path);
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *p = malloc((size_t)n + 1);
    *len = fread(p, 1, (size_t)n, f);
    p[*len] = 0;
    fclose(f);
    return p;
}

static uint32_t load(av_arena *a, const char *file) {
    char path[512];
    snprintf(path, sizeof path, DIR "%s", file);
    size_t len;
    uint8_t *b = slurp(path, &len);
    uint32_t t = b ? av_cue(a, b, len, NULL) : AV_NONE;
    free(b);
    return t;
}

/*  One namespaces.tsv line, parsed. */
typedef struct {
    char *fld[16];
    av_nsprog p;
    char *rnames[16], *onames[16];
    unsigned nr, no;
    uint64_t fuel, start, cap;
    unsigned rounds;
} nscase;

static unsigned ctors(char *spec, char **names, unsigned *arity, int *app) {
    unsigned n = 0;
    for (char *tok = strtok(spec, " "); tok && n < 16; tok = strtok(NULL, " ")) {
        if (tok[0] == '*') { if (app) *app = (int)n; tok++; }
        char *slash = strchr(tok, '/');
        if (slash) { *slash = '\0'; if (arity) arity[n] = (unsigned)atoi(slash + 1); }
        names[n++] = tok;
    }
    return n;
}

static bool parse_case(char *line, nscase *c) {
    memset(c, 0, sizeof *c);
    int k = 0;
    for (char *p = line; k < 16 && p; k++) {
        c->fld[k] = p;
        p = strchr(p, '\t');
        if (p) *p++ = '\0';
    }
    if (k != 16) return false;
    av_arena *t = av_arena_new(1u << 12);
    c->p.terms = t;
    c->p.interp = load(t, c->fld[1]);
    c->p.datum = load(t, c->fld[3]);
    c->p.eq = load(t, c->fld[6]);
    c->p.hit = load(t, c->fld[7]);
    c->p.notyet = load(t, c->fld[8]);
    c->p.zero = load(t, c->fld[9]);
    c->p.suc = load(t, c->fld[10]);
    if (strcmp(c->fld[2], "-") != 0) return false;      /* no case has more */
    if (strncmp(c->fld[4], "policy:", 7) == 0) {
        c->fuel = 0;
        c->start = strtoull(c->fld[4] + 7, NULL, 10);
        c->cap = strtoull(strchr(c->fld[4] + 7, ':') + 1, NULL, 10);
    } else {
        c->fuel = strtoull(c->fld[4], NULL, 10);
    }
    c->rounds = (unsigned)atoi(c->fld[5]);
    unsigned ar[16];
    char *rs = strdup(c->fld[11]), *os = strdup(c->fld[12]);
    c->nr = ctors(rs, c->rnames, ar, NULL);
    /* run.py: the block is the second one-field constructor, the timeout
     * the last terminal */
    unsigned ones = 0;
    for (unsigned i = 0; i < c->nr; i++) {
        if (ar[i] == 1 && ++ones == 2) c->p.block = i;
        if (ar[i] == 0) c->p.timeout = i;
    }
    int app = -1;
    c->no = ctors(os, c->onames, NULL, &app);
    c->p.nres = c->nr;
    c->p.obj = (av_objtype){ (const char *const *)c->onames, c->no, (unsigned)app };
    return c->p.interp != AV_NONE && c->p.datum != AV_NONE && c->p.eq != AV_NONE &&
           c->p.hit != AV_NONE && c->p.notyet != AV_NONE && c->p.zero != AV_NONE &&
           c->p.suc != AV_NONE && app >= 0 && ones >= 2;
}

static void free_case(nscase *c) {
    av_arena_free(c->p.terms);
    free(c->rnames[0]);
    free(c->onames[0]);
}

/*  The namespace: the resolution file's rendered paths and answers. */
static uint32_t resolve(void *ctx, av_arena *a, const char *key) {
    const char *file = ctx;
    if (strcmp(file, "-") == 0) return AV_NONE;
    char path[512];
    snprintf(path, sizeof path, DIR "%s", file);
    size_t len;
    char *text = (char *)slurp(path, &len);
    uint32_t out = AV_NONE;
    for (char *line = text, *nl; line && *line; line = nl) {
        nl = strchr(line, '\n');
        if (nl) *nl++ = '\0';
        char *tab = strchr(line, '\t');
        if (tab && (*tab = '\0', strcmp(line, key) == 0)) out = load(a, tab + 1);
    }
    free(text);
    return out;
}

static av_arena *jetted(void *ctx) {
    (void)ctx;
    av_arena *a = av_arena_new(1u << 16);
    const char *err = NULL;
    if (av_jets_load(a, DIR "dictionary.tsv", 8, &err) < 0 ||
        av_interps_load(a, DIR "interpreters.tsv", DIR "dictionary.tsv", &err) < 0) {
        av_arena_free(a);
        return NULL;
    }
    return a;
}

static char *joined(const av_nsrun *r) {
    size_t n = 1;
    for (size_t i = 0; i < r->nevents; i++) n += strlen(r->events[i]) + 1;
    char *s = calloc(n, 1);
    for (size_t i = 0; i < r->nevents; i++) {
        if (i) strcat(s, "|");
        strcat(s, r->events[i]);
    }
    return s;
}

static char *attempts(const av_nsrun *r) {
    char *s = calloc(r->nattempts * 48 + 1, 1);
    for (size_t i = 0; i < r->nattempts; i++) {
        char one[48];
        snprintf(one, sizeof one, "%s%llu:%s:%llu", i ? "," : "",
                 (unsigned long long)r->attempts[i].fuel,
                 av_status_name(r->attempts[i].status),
                 (unsigned long long)r->attempts[i].steps);
        strcat(s, one);
    }
    return s;
}

static char *cases_text(void) {
    size_t len;
    return (char *)slurp(DIR "namespaces.tsv", &len);
}

/*  Every pinned run, reference host: events and attempts exactly. */
TEST(every_pinned_run_replays_round_for_round) {
    char *text = cases_text();
    CHECK(text != NULL);
    if (!text) return;
    int n = 0, stuck = 0;
    for (char *line = text, *nl; *line; line = nl) {
        nl = strchr(line, '\n');
        if (nl) *nl++ = '\0';
        nscase c;
        CHECK(parse_case(line, &c));
        av_facts *f = av_facts_new(&c.p.obj);
        av_opts o = av_opts_default();
        o.jets = false;
        o.max_steps = 5000000;
        av_nsrun r;
        CHECK(av_ns_run(&c.p, f, resolve, c.fld[13], NULL, NULL, c.fuel, c.start, c.cap,
                        c.rounds, &o, (const char *const *)c.rnames, &r));
        char *ev = joined(&r), *at = attempts(&r);
        if (strcmp(ev, c.fld[14]) || strcmp(at, c.fld[15]))
            fprintf(stderr, "  %s:\n    events   %s\n    expected %s\n    attempts %s\n"
                    "    expected %s\n", c.fld[0], ev, c.fld[14], at, c.fld[15]);
        CHECK(strcmp(ev, c.fld[14]) == 0);
        CHECK(strcmp(at, c.fld[15]) == 0);
        stuck += strstr(ev, "STUCK") != NULL;
        free(ev);
        free(at);
        av_nsrun_free(&r);
        av_facts_free(f);
        free_case(&c);
        n++;
    }
    printf("  %d runs replayed, %d of them STUCK\n", n, stuck);
    CHECK_EQ(n, 12);
    CHECK_EQ(stuck, 2);
    free(text);
}

/*  The same runs with the interpreter jet and the native lookup, every
 *  fire checked against the unjetted interpreter: the same events. */
TEST(the_native_lookup_gives_the_same_events) {
    char *text = cases_text();
    if (!text) { CHECK(0); return; }
    int n = 0;
    uint64_t lookups = 0;
    for (char *line = text, *nl; *line; line = nl) {
        nl = strchr(line, '\n');
        if (nl) *nl++ = '\0';
        nscase c;
        CHECK(parse_case(line, &c));
        av_facts *f = av_facts_new(&c.p.obj);
        av_opts o = av_opts_default();
        o.max_steps = 5000000;
        o.interp_jets = true;
        o.jet_check = 1;
        av_nsrun r;
        CHECK(av_ns_run(&c.p, f, resolve, c.fld[13], jetted, NULL, c.fuel, c.start, c.cap,
                        c.rounds, &o, (const char *const *)c.rnames, &r));
        char *ev = joined(&r);
        if (strcmp(ev, c.fld[14])) fprintf(stderr, "  %s: %s, expected %s\n", c.fld[0], ev, c.fld[14]);
        CHECK(strcmp(ev, c.fld[14]) == 0);
        for (size_t i = 0; i < r.nattempts; i++) lookups += r.attempts[i].lookups;
        free(ev);
        av_nsrun_free(&r);
        av_facts_free(f);
        free_case(&c);
        n++;
    }
    CHECK_EQ(n, 12);
    printf("  %llu scries answered natively\n", (unsigned long long)lookups);
    CHECK(lookups > 0);
    free(text);
}

static bool find_case(const char *id, char **text, nscase *c) {
    *text = cases_text();
    for (char *line = *text, *nl; line && *line; line = nl) {
        nl = strchr(line, '\n');
        if (nl) *nl++ = '\0';
        if (strncmp(line, id, strlen(id)) == 0 && line[strlen(id)] == '\t')
            return parse_case(line, c);
    }
    return false;
}

/*  The chain run logs S and K; a store reopened from the log resolves at
 *  once, in the reference host's count for the last round. */
TEST(the_log_replays_the_facts) {
    char *text;
    nscase c;
    CHECK(find_case("scry-block.chain", &text, &c));
    char log[] = "/tmp/avon-facts-XXXXXX";
    int fd = mkstemp(log);
    CHECK(fd >= 0);
    close(fd);
    unlink(log);
    const char *err = NULL;
    av_facts *f = av_facts_open(&c.p.obj, log, &err);
    CHECK(f != NULL);
    av_opts o = av_opts_default();
    o.jets = false;
    o.max_steps = 5000000;
    av_nsrun r;
    CHECK(av_ns_run(&c.p, f, resolve, c.fld[13], NULL, NULL, c.fuel, 0, 0, c.rounds, &o,
                    (const char *const *)c.rnames, &r));
    CHECK_EQ(av_facts_count(f), 2);
    av_nsrun_free(&r);
    av_facts_free(f);

    av_facts *g = av_facts_open(&c.p.obj, log, &err);
    if (!g) fprintf(stderr, "  reopen: %s\n", err);
    CHECK(g != NULL);
    if (g) {
        CHECK_EQ(av_facts_count(g), 2);
        CHECK(strcmp(av_facts_key(g, 0), "S") == 0);
        CHECK(strcmp(av_facts_key(g, 1), "K") == 0);
        CHECK(av_ns_run(&c.p, g, NULL, NULL, NULL, NULL, c.fuel, 0, 0, c.rounds, &o,
                        (const char *const *)c.rnames, &r));
        CHECK_EQ(r.nevents, 1);
        CHECK(r.nevents == 1 && strcmp(r.events[0], "RValN") == 0);
        CHECK(r.nattempts == 1 && r.attempts[0].steps == 1250);
        CHECK(r.payload && strcmp(r.payload, "I") == 0);
        /* a known key cannot be appended again */
        av_arena *a = av_arena_new(0);
        uint32_t k = load(a, "ns.ansK.skit");
        CHECK(!av_facts_append(g, a, k, k, &err));
        CHECK(err && strstr(err, "append-only"));
        av_arena_free(a);
        av_nsrun_free(&r);
        av_facts_free(g);
    }
    unlink(log);
    free_case(&c);
    free(text);
}

/*  EQ5 replaced by a comparison that is always false: the resolver term
 *  answers not-yet for everything, so the native lookup, which would hit,
 *  must be refused---the run blocks again on K, which the store knows:
 *  STUCK, jets on or off. */
TEST(a_resolver_that_disagrees_is_not_looked_up) {
    char *text;
    nscase c;
    CHECK(find_case("scry-block.one-block", &text, &c));
    c.p.eq = av_parse(c.p.terms, "K (K (K I))", 11, NULL);   /* λm n. PFalse */
    for (int jets = 0; jets < 2; jets++) {
        av_facts *f = av_facts_new(&c.p.obj);
        av_opts o = av_opts_default();
        o.max_steps = 5000000;
        o.interp_jets = jets;
        o.jet_check = jets;
        av_nsrun r;
        CHECK(av_ns_run(&c.p, f, resolve, c.fld[13], jets ? jetted : NULL, NULL, c.fuel, 0, 0,
                        c.rounds, &o, (const char *const *)c.rnames, &r));
        char *ev = joined(&r);
        CHECK(strcmp(ev, "BLOCK on K|BLOCK on K|STUCK") == 0);
        /* round 1, the store empty: the term and the lookup agree---all
         * not yet---so jets answer natively; round 2 holds K, the check
         * finds the term disagrees, and nothing is answered natively */
        CHECK_EQ(r.nattempts, 2);
        if (r.nattempts == 2) {
            CHECK_EQ(r.attempts[0].lookups, jets ? 1u : 0u);
            CHECK_EQ(r.attempts[1].lookups, 0);
        }
        if (strcmp(ev, "BLOCK on K|BLOCK on K|STUCK")) fprintf(stderr, "  jets %d: %s\n", jets, ev);
        free(ev);
        av_nsrun_free(&r);
        av_facts_free(f);
    }
    free_case(&c);
    free(text);
}

/*  Aviary's abstraction: [x]x = I; [x]K = K K; [x](K x) = K (eta);
 *  [x](x K) = S I (K K). */
TEST(abstraction_is_aviarys) {
    av_arena *a = av_arena_new(0);
    uint32_t x = av_leaf(a, "@x", 2);
    struct { uint32_t body; const char *want; } t[] = {
        { x, "I" },
        { AV_NODE_K, "K K" },
        { av_app(a, AV_NODE_K, x), "K" },
        { av_app(a, x, AV_NODE_K), "S I (K K)" },
        { av_app(a, av_app(a, AV_NODE_S, x), x), "S S I" },
    };
    for (size_t i = 0; i < sizeof t / sizeof *t; i++) {
        av_buf b = { 0 };
        CHECK(av_print(a, av_abstract(a, x, t[i].body), 100, &b));
        if (strcmp(b.s, t[i].want)) fprintf(stderr, "  %zu: %s, want %s\n", i, b.s, t[i].want);
        CHECK(strcmp(b.s, t[i].want) == 0);
        av_buf_free(&b);
    }
    av_arena_free(a);
}

TEST_MAIN(
    TEST_CASE(every_pinned_run_replays_round_for_round),
    TEST_CASE(the_native_lookup_gives_the_same_events),
    TEST_CASE(the_log_replays_the_facts),
    TEST_CASE(a_resolver_that_disagrees_is_not_looked_up),
    TEST_CASE(abstraction_is_aviarys),
)
