/**  interp.c
 *
 *  The interpreter jet (docs/DESIGN.md §7): a generated interpreter's fuel
 *  loop run natively.  What it must reproduce is the generator's
 *  (python/skijack/generate.py): one loop iteration per fuel unit; each
 *  iteration walks the object term's spine to its head and either
 *  contracts an S, K or I redex, or ends -- a combinator short of arguments
 *  is the value, another leaf runs its arm.  Copy-mode reduction with the
 *  object fuel as max_steps is exactly that loop, attempt for attempt, and
 *  stops where an arm must run, since the other leaves are inert atoms.
 */

#define _POSIX_C_SOURCE 200809L

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "jets.h"

/*  ---------------------------------------------------------------- loading */

static char *slurp(const char *path, size_t *len) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    size_t cap = 1 << 16, n = 0;
    char *s = malloc(cap + 1);
    while (s) {
        n += fread(s + n, 1, cap - n, f);
        if (n < cap) break;
        char *q = realloc(s, (cap *= 2) + 1);
        if (!q) { free(s); s = NULL; }
        else s = q;
    }
    fclose(f);
    if (s) s[n] = '\0';
    *len = n;
    return s;
}

typedef struct { const char *hash, *term; size_t tlen; } drow;

static int drow_cmp(const void *x, const void *y) {
    return strncmp(((const drow *)x)->hash, ((const drow *)y)->hash, 26);
}

/*  The dictionary's term for a published hash, parsed into the arena. */
static uint32_t dict_term(av_arena *a, const drow *rows, size_t n, const char *hash) {
    drow key = { hash, NULL, 0 };
    const drow *r = bsearch(&key, rows, n, sizeof *rows, drow_cmp);
    if (!r) return AV_NONE;
    return av_parse(a, r->term, r->tlen, NULL);
}

static bool role_of(const char *tok, size_t n, uint8_t *role, uint8_t *arg) {
    *arg = 0;
    if (n == 1 && tok[0] == 'S') { *role = AV_OROLE_S; return true; }
    if (n == 1 && tok[0] == 'K') { *role = AV_OROLE_K; return true; }
    if (n == 1 && tok[0] == 'I') { *role = AV_OROLE_I; return true; }
    if (n == 3 && !memcmp(tok, "App", 3)) { *role = AV_OROLE_APP; return true; }
    if (n == 7 && !memcmp(tok, "diverge", 7)) { *role = AV_OROLE_DIVERGE; return true; }
    if (n == 4 && !memcmp(tok, "scry", 4)) { *role = AV_OROLE_SCRY; return true; }
    if (n > 3 && !memcmp(tok, "err", 3)) {
        *role = AV_OROLE_ERR;
        *arg = (uint8_t)atoi(tok + 3);
        return true;
    }
    return false;
}

long av_interps_load(av_arena *a, const char *ipath, const char *dpath,
                     const char **err) {
    size_t dlen, ilen, n = 0, cap = 512;
    char *dtext = slurp(dpath, &dlen), *itext = slurp(ipath, &ilen);
    drow *rows = malloc(cap * sizeof *rows);
    const char *msg = NULL;
    long loaded = 0;
    if (!dtext || !itext || !rows) { msg = "cannot read the dictionary or the interpreters"; goto done; }
    for (char *p = dtext, *nl; *p; p = nl + 1) {
        nl = strchr(p, '\n');
        if (!nl) break;
        char *t1 = memchr(p, '\t', (size_t)(nl - p));
        char *t2 = t1 ? memchr(t1 + 1, '\t', (size_t)(nl - t1 - 1)) : NULL;
        if (!t2) { msg = "malformed dictionary line"; goto done; }
        if (n == cap) {
            drow *q = realloc(rows, (cap *= 2) * sizeof *q);
            if (!q) { msg = "out of memory"; goto done; }
            rows = q;
        }
        rows[n++] = (drow){ p, t2 + 1, (size_t)(nl - t2 - 1) };
    }
    qsort(rows, n, sizeof *rows, drow_cmp);

    for (char *line = itext, *nl; *line; line = nl + 1) {
        nl = strchr(line, '\n');
        if (!nl) break;
        *nl = '\0';
        if (!strncmp(line, "nat\t", 4)) {             /* a known numeral */
            char *z = line + 4, *tab = strchr(z, '\t');
            if (!tab) { msg = "malformed nat line"; goto done; }
            *tab = '\0';
            uint32_t zt = dict_term(a, rows, n, z), st = dict_term(a, rows, n, tab + 1);
            if (zt == AV_NONE || st == AV_NONE) { msg = "a numeral missing from the dictionary"; goto done; }
            uint32_t *q = realloc(a->nats, 2 * (a->nnats + 1) * sizeof *q);
            if (!q) { msg = "out of memory"; goto done; }
            a->nats = q;
            a->nats[2 * a->nnats] = zt;
            a->nats[2 * a->nnats + 1] = st;
            a->nnats++;
            continue;
        }
        char *f[6];
        int k = 0;
        for (char *p = line; k < 6; k++) {
            f[k] = p;
            char *tab = strchr(p, '\t');
            if (!tab) { k++; break; }
            *tab = '\0';
            p = tab + 1;
        }
        if (k != 6) { msg = "malformed interpreters line"; goto done; }
        av_interp in;
        memset(&in, 0, sizeof in);
        if (!av_hash_parse(f[0], &in.digest)) { msg = "malformed interpreter hash"; goto done; }
        in.nparams = (unsigned)atoi(f[2]);
        in.value = in.timeout = AV_INTERP_CTORS;
        bool apps = false, s = false, kk = false, ii = false;
        for (char *tok = strtok(f[3], " "); tok; tok = strtok(NULL, " ")) {
            char *slash = strchr(tok, '/');
            if (!slash || in.nobj == AV_INTERP_CTORS) { msg = "malformed object type"; goto done; }
            unsigned i = in.nobj++;
            if (!role_of(tok, (size_t)(slash - tok), &in.orole[i], &in.oarg[i])) {
                msg = "unknown object role";
                goto done;
            }
            in.octor[i] = dict_term(a, rows, n, slash + 1);
            if (in.octor[i] == AV_NONE) { msg = "a constructor missing from the dictionary"; goto done; }
            switch (in.orole[i]) {
            case AV_OROLE_S: in.oleaf[i] = AV_NODE_S; s = true; break;
            case AV_OROLE_K: in.oleaf[i] = AV_NODE_K; kk = true; break;
            case AV_OROLE_I: in.oleaf[i] = AV_NODE_I; ii = true; break;
            case AV_OROLE_APP: in.oleaf[i] = in.octor[i]; apps = true; break;
            default: {
                char nm[16];
                int len = snprintf(nm, sizeof nm, "@leaf%u", i);
                in.oleaf[i] = av_leaf(a, nm, (size_t)len);
                if (in.oleaf[i] == AV_NONE) { msg = "out of memory"; goto done; }
            }
            }
        }
        for (char *tok = strtok(f[4], " "); tok; tok = strtok(NULL, " ")) {
            char *slash = strchr(tok, '/');
            if (!slash || in.nres == AV_INTERP_CTORS) { msg = "malformed result type"; goto done; }
            unsigned i = in.nres++;
            size_t len = (size_t)(slash - tok);
            in.rrole[i] = len == 5 && !memcmp(tok, "value", 5) ? AV_RROLE_VALUE
                        : len == 7 && !memcmp(tok, "timeout", 7) ? AV_RROLE_TIMEOUT
                        : AV_RROLE_OTHER;
            if (in.rrole[i] == AV_RROLE_VALUE) in.value = i;
            if (in.rrole[i] == AV_RROLE_TIMEOUT) in.timeout = i;
            in.rctor[i] = dict_term(a, rows, n, slash + 1);
            if (in.rctor[i] == AV_NONE) { msg = "a constructor missing from the dictionary"; goto done; }
        }
        if (strcmp(f[5], "-") != 0) {
            for (char *tok = strtok(f[5], " "); tok; tok = strtok(NULL, " ")) {
                if (in.nans == AV_INTERP_CTORS) { msg = "malformed answer type"; goto done; }
                unsigned i = in.nans++;
                if (!strcmp(tok, "hit")) in.arole[i] = AV_AROLE_HIT;
                else if (!strncmp(tok, "miss", 4)) { in.arole[i] = AV_AROLE_MISS; in.aarg[i] = (uint8_t)atoi(tok + 4); }
                else if (!strncmp(tok, "notyet", 6)) { in.arole[i] = AV_AROLE_NOTYET; in.aarg[i] = (uint8_t)atoi(tok + 6); }
                else { msg = "unknown answer role"; goto done; }
            }
        }
        /* the spec must be one the fire below can run */
        bool scry = false;
        for (unsigned i = 0; i < in.nobj; i++) {
            if (in.orole[i] == AV_OROLE_SCRY) scry = true;
            if (in.orole[i] == AV_OROLE_ERR && in.oarg[i] >= in.nres) { msg = "an error outcome out of range"; goto done; }
        }
        for (unsigned i = 0; i < in.nans; i++)
            if (in.arole[i] != AV_AROLE_HIT && in.aarg[i] >= in.nres) { msg = "an answer outcome out of range"; goto done; }
        if (!apps || !s || !kk || !ii || in.value == AV_INTERP_CTORS ||
            in.timeout == AV_INTERP_CTORS || (scry && (in.nparams != 1 || !in.nans))) {
            msg = "an interpreter spec the jet cannot run";
            goto done;
        }
        uint32_t loop = dict_term(a, rows, n, f[0]);
        if (loop == AV_NONE) { msg = "the loop term is missing from the dictionary"; goto done; }
        in.jet = jet_entry_for(a, in.digest, loop);
        if (in.jet == AV_NONE) { msg = "out of memory"; goto done; }
        av_interp *q = realloc(a->interps, (a->ninterps + 1) * sizeof *q);
        if (!q) { msg = "out of memory"; goto done; }
        a->interps = q;
        a->interps[a->ninterps] = in;
        a->jets[in.jet].interp = (int32_t)a->ninterps;
        a->ninterps++;
        loaded++;
    }
done:
    free(dtext);
    free(itext);
    free(rows);
    if (msg) { if (err) *err = msg; return -1; }
    return loaded;
}

/*  ------------------------------------------------ decoding and encoding */

static bool same(const av_arena *a, uint32_t x, uint32_t y) {
    return av_equal(a, x, y, 100000) == 1;
}

/*  A fuel numeral: a known encoding read by structure, level by level, and
 *  probing from the first level that is not one. */
static bool read_fuel(av_arena *a, uint32_t t, const av_opts *o, uint64_t *k) {
    uint64_t n = 0;
    for (;;) {
        uint32_t x = av_view(a, t);
        bool step = false;
        for (uint32_t j = 0; j < a->nnats; j++) {
            if (same(a, x, a->nats[2 * j])) { *k = n; return true; }
            if (av_tag(a, x) == AV_APP && same(a, av_left(a, x), a->nats[2 * j + 1])) {
                n++;
                t = av_right(a, x);
                step = true;
                break;
            }
        }
        if (step) continue;
        uint64_t rest;
        if (!av_read_nat(a, t, 64 * 1024 * 1024, o, &rest, NULL)) return false;
        *k = n + rest;
        return true;
    }
}

/*  The constructor a datum node is by structure, and its fields: the
 *  object type's leaf constructors, or its application constructor over
 *  two fields.  False if the node is neither; then it is probed. */
static bool read_ctor(const av_arena *a, const av_interp *in, uint32_t node,
                      unsigned *ctor, uint32_t *f0, uint32_t *f1) {
    uint32_t x = av_view(a, node);
    for (unsigned i = 0; i < in->nobj; i++) {
        if (in->orole[i] == AV_OROLE_APP) {
            if (av_tag(a, x) != AV_APP) continue;
            uint32_t l = av_view(a, av_left(a, x));
            if (av_tag(a, l) != AV_APP || !same(a, av_left(a, l), in->octor[i])) continue;
            *ctor = i;
            *f0 = av_right(a, l);
            *f1 = av_right(a, x);
            return true;
        }
        if (same(a, x, in->octor[i])) { *ctor = i; return true; }
    }
    return false;
}

/*  A quoted datum to a live object term: probing as av_decode does, each
 *  leaf constructor its live leaf.  Probes never collect, so the memo's
 *  keys hold; nothing here reduces otherwise. */
static uint32_t decode_live(av_arena *a, const av_interp *in, uint32_t datum,
                            const av_opts *o) {
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 256, top = 0, nb = 0, bcap = 256, probes = 0;
    item *todo = malloc(cap * sizeof *todo);
    uint32_t *built = malloc(bcap * sizeof *built), out = AV_NONE;
    nmap m = { 0 };
    if (!todo || !built) goto done;
    todo[top++] = (item){ datum, false };
    while (top) {
        item it = todo[--top];
        if (nb + 1 > bcap) {
            uint32_t *q = realloc(built, (bcap *= 2) * sizeof *q);
            if (!q) goto done;
            built = q;
        }
        uint64_t v;
        if (it.done) {
            uint32_t r = built[--nb], l = built[--nb];
            uint32_t e = av_app(a, l, r);
            if (e == AV_NONE || !nmap_put(&m, it.node, e)) goto done;
            built[nb++] = e;
            continue;
        }
        if (nmap_get(&m, it.node, &v)) { built[nb++] = (uint32_t)v; continue; }
        av_peeled p;
        uint32_t f0 = AV_NONE, f1 = AV_NONE;
        if (read_ctor(a, in, it.node, &p.ctor, &f0, &f1)) {
            p.nfields = in->orole[p.ctor] == AV_OROLE_APP ? 2 : 0;
            p.field[0] = f0;
            p.field[1] = f1;
        } else {
            if (++probes > 50000000) goto done;
            if (!av_peel(a, it.node, in->nobj, o, &p, NULL)) goto done;
        }
        if (in->orole[p.ctor] == AV_OROLE_APP) {
            if (p.nfields != 2) goto done;
            if (top + 3 > cap) {
                item *q = realloc(todo, (cap *= 2) * sizeof *q);
                if (!q) goto done;
                todo = q;
            }
            todo[top++] = (item){ it.node, true };
            todo[top++] = (item){ p.field[1], false };
            todo[top++] = (item){ p.field[0], false };
        } else {
            if (p.nfields != 0 || !nmap_put(&m, it.node, in->oleaf[p.ctor])) goto done;
            built[nb++] = in->oleaf[p.ctor];
        }
    }
    if (nb == 1) out = built[0];
done:
    free(todo);
    free(built);
    nmap_free(&m);
    return out;
}

/*  A live object term to a datum, with the program's own constructors.
 *  Allocates, never reduces.  AV_NONE for a leaf the object type lacks. */
static uint32_t encode(av_arena *a, const av_interp *in, uint32_t t) {
    unsigned app = 0;
    for (unsigned i = 0; i < in->nobj; i++)
        if (in->orole[i] == AV_OROLE_APP) app = i;
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 256, top = 0;
    item *todo = malloc(cap * sizeof *todo);
    nmap m = { 0 };
    uint32_t out = AV_NONE;
    if (!todo) goto done;
    todo[top++] = (item){ av_view(a, t), false };
    while (top) {
        item it = todo[--top];
        uint64_t v;
        if (!it.done && nmap_get(&m, it.node, &v)) continue;
        uint32_t built = AV_NONE;
        if (av_tag(a, it.node) == AV_LEAF) {
            for (unsigned i = 0; i < in->nobj; i++)
                if (in->orole[i] != AV_OROLE_APP && in->oleaf[i] == it.node) built = in->octor[i];
            if (built == AV_NONE) goto done;
        } else if (!it.done) {
            if (top + 3 > cap) {
                item *q = realloc(todo, (cap *= 2) * sizeof *q);
                if (!q) goto done;
                todo = q;
            }
            todo[top++] = (item){ it.node, true };
            todo[top++] = (item){ av_view(a, av_right(a, it.node)), false };
            todo[top++] = (item){ av_view(a, av_left(a, it.node)), false };
            continue;
        } else {
            uint64_t l, r;
            nmap_get(&m, av_view(a, av_left(a, it.node)), &l);
            nmap_get(&m, av_view(a, av_right(a, it.node)), &r);
            built = av_app(a, av_app(a, in->octor[app], (uint32_t)l), (uint32_t)r);
            if (built == AV_NONE) goto done;
        }
        if (!nmap_put(&m, it.node, built)) goto done;
    }
    uint64_t r;
    if (nmap_get(&m, av_view(a, t), &r)) out = (uint32_t)r;
done:
    free(todo);
    nmap_free(&m);
    return out;
}

/*  --------------------------------------------------------------- firing */

/*  The native lookup (docs/DESIGN.md §8): when the resolver is a fact
 *  store's (a jet key tagged by av_facts_resolver), find the path among
 *  the facts it encodes instead of reducing it.  The first use checks the
 *  lookup against the term -- every fact's key must hit with its answer,
 *  and a path longer than every key must be not-yet -- and a resolver
 *  that disagrees is never looked up natively.  1 a hit, *ans the answer
 *  datum; 0 not yet; -1 no native answer: reduce the resolver.  *spent is
 *  what the check's probes cost, not part of the fire's own work. */
static int native_lookup(av_arena *a, const av_interp *in, uint32_t resolver,
                         uint32_t path, const av_opts *po, uint32_t *ans,
                         uint64_t *spent) {
    *spent = 0;
    const av_facts *f = a->facts;
    if (!f || av_tag(a, resolver) != AV_JET) return -1;
    av_jet *J = &a->jets[AV_JET_ID(av_left(a, resolver))];
    if (!J->resolves || J->admitted == 2) return -1;
    size_t n = J->resolves - 1;
    int hit = -1, notyet = -1;
    for (unsigned c = 0; c < in->nans; c++) {
        if (in->arole[c] == AV_AROLE_HIT) hit = (int)c;
        if (in->arole[c] == AV_AROLE_NOTYET) notyet = (int)c;
    }
    if (hit < 0 || notyet < 0) return -1;
    if (J->admitted == 0) {
        uint64_t p0 = a->probe_steps;
        bool agrees = true;
        size_t longest = 0;
        uint32_t term = J->fallback;
        for (size_t i = 0; i < n && agrees; i++) {
            uint32_t live = facts_live_path(f, i, a, in->oleaf);
            uint32_t pd = live == AV_NONE ? AV_NONE : encode(a, in, live);
            uint32_t q = pd == AV_NONE ? AV_NONE : av_app(a, term, pd);
            av_peeled pe;
            agrees = q != AV_NONE && av_peel(a, q, in->nans, po, &pe, NULL) &&
                     (int)pe.ctor == hit && pe.nfields == 1 &&
                     facts_same_answer(f, i, a, pe.field[0]);
            size_t len = strlen(av_facts_key(f, i));
            if (len > longest) longest = len;
        }
        if (agrees) {                   /* a path no key can print as */
            unsigned leaf0 = in->orole[0] == AV_OROLE_APP ? 1 : 0;
            uint32_t absent = in->oleaf[leaf0];
            for (size_t i = 0; i <= longest && absent != AV_NONE; i++)
                absent = av_app(a, absent, in->oleaf[leaf0]);
            uint32_t pd = absent == AV_NONE ? AV_NONE : encode(a, in, absent);
            uint32_t q = pd == AV_NONE ? AV_NONE : av_app(a, term, pd);
            av_peeled pe;
            agrees = q != AV_NONE && av_peel(a, q, in->nans, po, &pe, NULL) &&
                     (int)pe.ctor == notyet;
        }
        *spent = a->probe_steps - p0;
        J = &a->jets[AV_JET_ID(av_left(a, resolver))];
        J->admitted = agrees ? 1 : 2;
        if (!agrees) return -1;
    }
    size_t which;
    int found = facts_find(f, n, a, path, in->oleaf, &which);
    if (found < 0) return -1;
    a->lookups++;
    if (found == 0) return 0;
    *ans = facts_answer(f, which, a);
    return *ans == AV_NONE ? -1 : 1;
}

int interp_fire(av_arena *a, uint32_t id, const uint32_t *argv,
                const av_opts *o, uint64_t host_left, uint32_t *out,
                uint64_t *charge, av_status *st, bool *fault) {
    const av_interp *in = &a->interps[a->jets[id].interp];
    unsigned nargs = in->nparams + 2;
    uint32_t loc[AV_INTERP_CTORS + 2], t = AV_NONE, res = AV_NONE;
    unsigned pushed = 0;
    for (unsigned i = 0; i < nargs; i++, pushed++) {
        loc[i] = argv[i];
        av_root_push(a, &loc[i]);
    }
    av_root_push(a, &t);
    av_root_push(a, &res);
    pushed += 2;
    uint64_t probe0 = a->probe_steps, objsteps = 0, k;
    int rc = 0;
    *fault = false;

    av_opts po = av_opts_default();          /* probes and the object run */
    po.strategy = AV_COPY;
    po.whnf_only = true;
    po.jets = o->jets;
    po.interp_jets = false;                  /* object fuel is bounded: §7 */
    po.jet_check = o->jet_check;
    po.max_steps = host_left;
    po.interrupt = o->interrupt;

#define SPENT() (objsteps + (a->probe_steps - probe0))
    if (!read_fuel(a, loc[in->nparams], &po, &k)) goto out;
    t = decode_live(a, in, loc[in->nparams + 1], &po);
    if (t == AV_NONE) goto out;
    t = av_jets_match(a, t);
    if (t == AV_NONE) goto out;

    uint64_t used = 0;
    for (;;) {
        if (SPENT() >= host_left) goto out;              /* decline: over budget */
        uint64_t left = k - used, hleft = host_left - SPENT();
        av_opts ro = po;
        ro.max_steps = left < hleft ? left : hleft;
        av_result r = av_reduce(a, t, &ro);
        objsteps += r.steps;
        used += r.steps;
        if (r.jet_fault) { *fault = true; *st = AV_INTERRUPTED; rc = -1; goto out; }
        if (r.status == AV_SIZE || r.status == AV_INTERRUPTED) { *st = r.status; rc = -1; goto out; }
        if (r.status == AV_FUEL) {
            if (ro.max_steps != left) goto out;          /* the host's bound: decline */
            res = in->rctor[in->timeout];                /* the object's: timeout */
            break;
        }
        t = r.term;
        /* the head and the arguments, first argument first */
        uint32_t h = av_view(a, t), spine[64];
        unsigned n = 0;
        while (av_tag(a, h) == AV_APP) {
            if (n < 64) spine[n] = av_right(a, h);
            n++;
            h = av_view(a, av_left(a, h));
        }
        unsigned leaf = in->nobj;
        for (unsigned i = 0; i < in->nobj; i++)
            if (in->orole[i] != AV_OROLE_APP && in->oleaf[i] == h) leaf = i;
        if (leaf == in->nobj) goto out;                  /* an atom it lacks */
        uint8_t role = in->orole[leaf];
        if (role == AV_OROLE_S || role == AV_OROLE_K || role == AV_OROLE_I ||
            (role == AV_OROLE_SCRY && n == 0)) {         /* no redex: the value */
            uint32_t v = encode(a, in, t);
            if (v == AV_NONE) goto out;
            res = av_app(a, in->rctor[in->value], v);
            break;
        }
        if (role == AV_OROLE_ERR) { res = in->rctor[in->oarg[leaf]]; break; }
        if (role != AV_OROLE_SCRY || n > 64) goto out;   /* diverge: decline */

        /* Scry p rest: one step, answered natively or by the resolver */
        used += 1;
        objsteps += 1;
        uint32_t path = spine[n - 1];
        uint32_t pd = encode(a, in, path);
        if (pd == AV_NONE) goto out;
        uint32_t natv = AV_NONE;
        uint64_t checked;
        int nat = native_lookup(a, in, loc[0], path, &po, &natv, &checked);
        probe0 += checked;                      /* the check is not this fire's */
        av_peeled ans;
        if (nat == 0) {
            for (unsigned c = 0; c < in->nans; c++)
                if (in->arole[c] == AV_AROLE_NOTYET) ans.ctor = c;
            res = av_app(a, in->rctor[in->aarg[ans.ctor]], pd);
            break;
        }
        if (nat == 1) {
            ans.nfields = 1;
            ans.field[0] = natv;
        } else {
            uint32_t q = av_app(a, loc[0], pd);
            if (q == AV_NONE || !av_peel(a, q, in->nans, &po, &ans, NULL)) goto out;
            uint8_t ar = in->arole[ans.ctor];
            if (ar == AV_AROLE_MISS) { res = in->rctor[in->aarg[ans.ctor]]; break; }
            if (ar == AV_AROLE_NOTYET) { res = av_app(a, in->rctor[in->aarg[ans.ctor]], pd); break; }
        }
        if (ans.nfields != 1) goto out;
        uint32_t v = decode_live(a, in, ans.field[0], &po);
        if (v == AV_NONE) goto out;
        for (unsigned i = n - 1; i-- > 0;)             /* v applied to the rest */
            if ((v = av_app(a, v, spine[i])) == AV_NONE) goto out;
        t = av_jets_match(a, v);
        if (t == AV_NONE) goto out;
    }
    if (res == AV_NONE || SPENT() > host_left) goto out;
    *out = res;
    *charge = SPENT();
    rc = 1;
out:
#undef SPENT
    for (unsigned i = 0; i < pushed; i++) av_root_pop(a);
    return rc;
}

bool interp_check(av_arena *a, uint32_t id, uint32_t node, const uint32_t *argv,
                  uint32_t out) {
    const av_interp *in = &a->interps[a->jets[id].interp];
    unsigned nargs = in->nparams + 2;
    uint32_t t = av_right(a, node);
    for (unsigned i = 0; i < nargs && t != AV_NONE; i++) t = av_app(a, t, argv[i]);
    if (t == AV_NONE) return true;
    av_opts co = av_opts_default();
    co.strategy = AV_COPY;
    co.whnf_only = true;
    co.jets = false;
    co.interp_jets = false;
    co.max_steps = 200000000;
    co.no_collect = true;                     /* out and argv stay where they are */
    av_result r = av_reduce(a, t, &co);
    if (r.status != AV_WHNF) return true;     /* inconclusive */
    av_peeled p1, p2;
    if (!av_peel(a, r.term, in->nres, &co, &p1, NULL)) return false;
    if (!av_peel(a, out, in->nres, &co, &p2, NULL)) return false;
    if (p1.ctor != p2.ctor || p1.nfields != p2.nfields) return false;
    if (p1.nfields == 0) return true;
    const char *names[AV_INTERP_CTORS];
    static const char *const nm[] = { "c0", "c1", "c2", "c3", "c4", "c5", "c6", "c7",
                                      "c8", "c9", "c10", "c11", "c12", "c13", "c14", "c15" };
    unsigned app = 0;
    for (unsigned i = 0; i < in->nobj; i++) {
        names[i] = nm[i];
        if (in->orole[i] == AV_OROLE_APP) app = i;
    }
    uint32_t d1 = av_decode(a, p1.field[0], in->nobj, names, app, 50000000, &co, NULL);
    uint32_t d2 = av_decode(a, p2.field[0], in->nobj, names, app, 50000000, &co, NULL);
    if (d1 == AV_NONE || d2 == AV_NONE) return true;   /* inconclusive */
    return av_equal(a, d1, d2, 100000000) != 0;
}
