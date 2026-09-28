/**  census.c
 *
 *  A dynamic census of called terms, for choosing jets (docs/DESIGN.md
 *  §6.7).  Where SKIjack's avon/bench/jets.py counts the subterms a
 *  compiled program contains, this counts the terms a running program
 *  calls, weighted by what a residual jet on each would absorb.
 */

#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "jets.h"

struct av_census {
    av_census_row *row;
    size_t         nrow, rowcap;
    uint64_t      *key;             /* open addressing: fp -> row + 1 */
    uint32_t      *slot;
    size_t         kcap;
    nmap           fp, atoms;       /* per node of the arena being run */
    const av_arena *seen;           /* ... whose collections they match */
    uint64_t       seen_gc;
    enum { COUNT, CAPTURE, MEASURE } mode;
    av_arena      *cap;             /* captured terms live here */
    uint64_t       calls;
    uint64_t       clock, epoch;    /* contractions recorded; runs begun */
    uint64_t      *code;            /* fingerprints of loaded subterms */
    size_t         ncode, codecap;
};

static bool is_code(const av_census *c, uint64_t fp) {
    if (!c->codecap) return false;
    uint64_t want = fp | 1;
    for (size_t j = (size_t)(fp * 0x9e3779b97f4a7c15u >> 7) & (c->codecap - 1);;
         j = (j + 1) & (c->codecap - 1)) {
        if (!c->code[j]) return false;
        if (c->code[j] == want) return true;
    }
}

static bool add_code(av_census *c, uint64_t fp) {
    if (is_code(c, fp)) return true;
    if (2 * (c->ncode + 1) > c->codecap) {
        size_t cap = c->codecap ? c->codecap * 2 : 4096;
        uint64_t *k = calloc(cap, sizeof *k);
        if (!k) return false;
        for (size_t i = 0; i < c->codecap; i++) {
            if (!c->code[i]) continue;
            size_t j = (size_t)((c->code[i] & ~1ull) * 0x9e3779b97f4a7c15u >> 7) & (cap - 1);
            while (k[j]) j = (j + 1) & (cap - 1);
            k[j] = c->code[i];
        }
        free(c->code);
        c->code = k;
        c->codecap = cap;
    }
    size_t j = (size_t)(fp * 0x9e3779b97f4a7c15u >> 7) & (c->codecap - 1);
    while (c->code[j]) j = (j + 1) & (c->codecap - 1);
    c->code[j] = fp | 1;
    c->ncode++;
    return true;
}

av_census *av_census_new(void) {
    av_census *c = calloc(1, sizeof *c);
    if (c) c->cap = av_arena_new(1024);
    if (c && !c->cap) { free(c); c = NULL; }
    return c;
}

void av_census_free(av_census *c) {
    if (!c) return;
    free(c->row);
    free(c->key);
    free(c->slot);
    nmap_free(&c->fp);
    nmap_free(&c->atoms);
    av_arena_free(c->cap);
    free(c->code);
    free(c);
}

av_arena *av_census_arena(av_census *c) { return c->cap; }
uint64_t av_census_calls(const av_census *c) { return c->calls; }

static uint64_t mix(uint64_t x) {                  /* splitmix64's finalizer */
    x ^= x >> 30; x *= 0xbf58476d1ce4e5b9u;
    x ^= x >> 27; x *= 0x94d049bb133111ebu;
    return x ^ (x >> 31);
}

/*  The fingerprint and the size of a node, memoized: iterative, children
 *  first.  Leaves by name, so fingerprints agree across arenas. */
static bool measure_in(nmap *fpm, nmap *atm, const av_arena *a, uint32_t t,
                       uint64_t *fpo, uint64_t *atomo) {
    typedef struct { uint32_t node; bool done; } item;
    item stack[256], *todo = stack;
    size_t cap = 256, top = 0;
    bool ok = true;
    todo[top++] = (item){ av_res(a, t), false };
    while (ok && top) {
        item it = todo[--top];
        uint64_t v;
        if (!it.done && nmap_get(fpm, it.node, &v)) continue;
        if (av_tag(a, it.node) != AV_APP) {
            const char *nm = av_leaf_name(a, av_right(a, it.node));
            uint64_t h = 0xcbf29ce484222325u;
            for (const char *p = nm; *p; p++) h = (h ^ (uint8_t)*p) * 0x100000001b3u;
            ok = nmap_put(fpm, it.node, mix(h)) && nmap_put(atm, it.node, 1);
            continue;
        }
        uint32_t l = av_res(a, av_left(a, it.node)), r = av_res(a, av_right(a, it.node));
        if (it.done) {
            uint64_t fl, fr, al, ar;
            nmap_get(fpm, l, &fl);
            nmap_get(fpm, r, &fr);
            nmap_get(atm, l, &al);
            nmap_get(atm, r, &ar);
            ok = nmap_put(fpm, it.node, mix(fl * 0x9e3779b97f4a7c15u ^ mix(fr + 1))) &&
                 nmap_put(atm, it.node, al + ar < al ? UINT64_MAX : al + ar);
            continue;
        }
        if (top + 3 > cap) {
            item *q = todo == stack ? malloc(2 * cap * sizeof *q)
                                    : realloc(todo, 2 * cap * sizeof *q);
            if (!q) { ok = false; break; }
            if (todo == stack) memcpy(q, stack, top * sizeof *q);
            todo = q;
            cap *= 2;
        }
        todo[top++] = (item){ it.node, true };
        todo[top++] = (item){ r, false };
        todo[top++] = (item){ l, false };
    }
    if (todo != stack) free(todo);
    t = av_res(a, t);
    return ok && nmap_get(fpm, t, fpo) && nmap_get(atm, t, atomo);
}

static bool measure(av_census *c, const av_arena *a, uint32_t t,
                    uint64_t *fpo, uint64_t *atomo) {
    return measure_in(&c->fp, &c->atoms, a, t, fpo, atomo);
}

static size_t kslot(uint64_t fp, size_t cap) {
    return (size_t)(mix(fp) & (cap - 1));
}

/*  The row for a fingerprint, made if new; SIZE_MAX out of memory. */
static size_t row_for(av_census *c, uint64_t fp, bool make) {
    if (make && 2 * (c->nrow + 1) > c->kcap) {
        size_t cap = c->kcap ? c->kcap * 2 : 4096;
        uint64_t *k = calloc(cap, sizeof *k);
        uint32_t *sl = malloc(cap * sizeof *sl);
        if (!k || !sl) { free(k); free(sl); return SIZE_MAX; }
        for (size_t i = 0; i < c->nrow; i++) {
            size_t j = kslot(c->row[i].fp, cap);
            while (k[j]) j = (j + 1) & (cap - 1);
            k[j] = c->row[i].fp | 1;             /* never 0 */
            sl[j] = (uint32_t)i;
        }
        free(c->key);
        free(c->slot);
        c->key = k;
        c->slot = sl;
        c->kcap = cap;
    }
    if (!c->kcap) return SIZE_MAX;
    uint64_t want = fp | 1;
    size_t j = kslot(fp, c->kcap);
    while (c->key[j]) {
        if (c->key[j] == want && c->row[c->slot[j]].fp == fp) return c->slot[j];
        j = (j + 1) & (c->kcap - 1);
    }
    if (!make) return SIZE_MAX;
    if (c->nrow == c->rowcap) {
        size_t cap = c->rowcap ? c->rowcap * 2 : 4096;
        av_census_row *r = realloc(c->row, cap * sizeof *r);
        if (!r) return SIZE_MAX;
        c->row = r;
        c->rowcap = cap;
    }
    size_t i = c->nrow++;
    memset(&c->row[i], 0, sizeof c->row[i]);
    c->row[i].fp = fp;
    c->row[i].term = AV_NONE;
    c->key[j] = want;
    c->slot[j] = (uint32_t)i;
    return i;
}

/*  Copy the term below t into the census's arena, sharing kept. */
static uint32_t capture(av_census *c, const av_arena *a, uint32_t t) {
    nmap m = { 0 };
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 256, top = 0;
    item *todo = malloc(cap * sizeof *todo);
    uint32_t out = AV_NONE;
    if (!todo) return AV_NONE;
    todo[top++] = (item){ av_res(a, t), false };
    while (top) {
        item it = todo[--top];
        uint64_t v;
        if (!it.done && nmap_get(&m, it.node, &v)) continue;
        uint32_t built;
        if (av_tag(a, it.node) != AV_APP) {
            const char *nm = av_leaf_name(a, av_right(a, it.node));
            built = av_leaf(c->cap, nm, strlen(nm));
        } else if (!it.done) {
            if (top + 3 > cap) {
                item *q = realloc(todo, (cap *= 2) * sizeof *q);
                if (!q) goto done;
                todo = q;
            }
            todo[top++] = (item){ it.node, true };
            todo[top++] = (item){ av_res(a, av_right(a, it.node)), false };
            todo[top++] = (item){ av_res(a, av_left(a, it.node)), false };
            continue;
        } else {
            uint64_t l, r;
            nmap_get(&m, av_res(a, av_left(a, it.node)), &l);
            nmap_get(&m, av_res(a, av_right(a, it.node)), &r);
            built = av_app(c->cap, (uint32_t)l, (uint32_t)r);
        }
        if (built == AV_NONE || !nmap_put(&m, it.node, built)) goto done;
    }
    uint64_t r;
    if (nmap_get(&m, av_res(a, t), &r)) out = (uint32_t)r;
done:
    free(todo);
    nmap_free(&m);
    return out;
}

/*  From the reducer: x was put in function position, with `avail`
 *  arguments now at the head.  Every prefix of x's spine is recorded. */
bool av_census_begin_run(av_census *c, const av_arena *a, uint32_t loaded) {
    c->epoch++;
    /* a new run's arena may reuse the last one's address: nothing the
     * per-node memo holds is about it */
    nmap_free(&c->fp);
    nmap_free(&c->atoms);
    c->seen = a;
    c->seen_gc = a->collections;
    /* every subterm of the loaded term is code */
    uint64_t fp, atoms;
    if (!measure(c, a, loaded, &fp, &atoms)) return false;
    for (size_t i = 0; i < c->fp.cap; i++)
        if (c->fp.key[i] != AV_NONE && !add_code(c, c->fp.val[i])) return false;
    return true;
}

void census_record(av_census *c, const av_arena *a, uint32_t x, size_t avail) {
    c->clock++;                             /* one call per contraction */
    if (c->seen != a || c->seen_gc != a->collections) {   /* nodes moved */
        nmap_free(&c->fp);
        nmap_free(&c->atoms);
        c->seen = a;
        c->seen_gc = a->collections;
    }
    x = av_res(a, x);
    size_t j = 0;
    uint32_t p = x;
    while (av_tag(a, p) == AV_APP) {        /* x = h a1 .. am: m first */
        j++;
        p = av_res(a, av_left(a, p));
    }
    for (p = x; av_tag(a, p) == AV_APP; p = av_res(a, av_left(a, p)), j--) {
        uint64_t fp, atoms;
        if (!measure(c, a, p, &fp, &atoms)) return;
        if (c->mode == COUNT && !is_code(c, fp)) continue;  /* built by the run */
        size_t i = row_for(c, fp, c->mode == COUNT);
        if (i == SIZE_MAX) continue;        /* in the capture pass: not chosen */
        av_census_row *r = &c->row[i];
        size_t extra = avail >= j ? avail - j : 0;
        if (c->mode == COUNT) {
            r->calls++;
            r->hist[extra < 9 ? extra : 9]++;
            r->atoms = (size_t)atoms;
            c->calls++;
        } else if (c->mode == CAPTURE) {
            if (r->term == AV_NONE) r->term = capture(c, a, p);
        } else if (r->arity && extra >= r->arity &&
                   (r->epoch != c->epoch || c->clock >= r->until)) {
            /* a fire: it absorbs the next `cost` contractions, the ones
             * this run is about to make (the genericity of §6.5) */
            r->fires++;
            r->saved += r->cost;
            r->until = c->clock + r->cost;
            r->epoch = c->epoch;
        }
    }
}

static int by_calls(const void *x, const void *y) {
    const av_census_row *a = x, *b = y;
    return a->calls < b->calls ? 1 : a->calls > b->calls ? -1 : 0;
}

void av_census_select(av_census *c, size_t n, size_t min_atoms) {
    size_t kept = 0;
    for (size_t i = 0; i < c->nrow; i++)
        if (c->row[i].atoms >= min_atoms) c->row[kept++] = c->row[i];
    c->nrow = kept;
    qsort(c->row, c->nrow, sizeof *c->row, by_calls);
    if (c->nrow > n) c->nrow = n;
    free(c->key);
    free(c->slot);
    c->key = NULL;
    c->slot = NULL;
    c->kcap = 0;
    size_t nrow = c->nrow;                  /* rebuild the index: rows fixed */
    c->nrow = 0;
    for (size_t i = 0; i < nrow; i++) {
        av_census_row r = c->row[i];
        size_t k = row_for(c, r.fp, true);
        if (k != SIZE_MAX) c->row[k] = r;
    }
    c->mode = CAPTURE;
}

static int by_saved(const void *x, const void *y) {
    const av_census_row *a = x, *b = y;
    /* ties go to the larger term: of one call's layers, the whole
     * function; then the fingerprint, so the order is the input's alone */
    return a->saved < b->saved ? 1 : a->saved > b->saved ? -1
         : a->calls < b->calls ? 1 : a->calls > b->calls ? -1
         : a->atoms < b->atoms ? 1 : a->atoms > b->atoms ? -1
         : (a->fp > b->fp) - (a->fp < b->fp);
}

void av_census_analyze(av_census *c) {
    /* registration may collect the census's arena: every row's term is a
     * root until the analysis is done */
    size_t rooted = 0;
    for (size_t i = 0; i < c->nrow; i++)
        if (c->row[i].term != AV_NONE) {
            av_root_push(c->cap, &c->row[i].term);
            rooted++;
        }
    for (size_t i = 0; i < c->nrow; i++) {
        av_census_row *r = &c->row[i];
        if (r->term == AV_NONE) continue;
        av_structural_hash(c->cap, r->term, r->hash);
        const char *why = NULL;
        uint32_t id = av_jet_register(c->cap, r->term, 0, 1000000, &why);
        if (id == AV_NONE) continue;
        r->arity = c->cap->jets[id].arity;
        r->cost = c->cap->jets[id].cost;
    }
    for (size_t i = 0; i < rooted; i++) av_root_pop(c->cap);
    /* The jets hold theirs now.  Nothing allocates in the census's arena
     * after this, so a term that is not a jet stays where it is. */
    for (size_t i = 0; i < c->nrow; i++)
        if (c->row[i].term != AV_NONE) {
            uint64_t d;
            char *h = c->row[i].hash;
            uint32_t id = av_hash_parse(h, &d) ? jet_find(c->cap, d) : AV_NONE;
            if (id != AV_NONE) c->row[i].term = c->cap->jets[id].fallback;
        }
    c->mode = MEASURE;
}

static int u64cmp(const void *x, const void *y) {
    uint64_t a = *(const uint64_t *)x, b = *(const uint64_t *)y;
    return a < b ? -1 : a > b;
}

/*  The fingerprints of every subterm of t, sorted. */
static uint64_t *subterms(const av_arena *a, uint32_t t, size_t *n) {
    nmap fpm = { 0 }, atm = { 0 };
    uint64_t fp, atoms, *out = NULL;
    *n = 0;
    if (measure_in(&fpm, &atm, a, t, &fp, &atoms) && (out = malloc(fpm.n * sizeof *out))) {
        for (size_t i = 0; i < fpm.cap; i++)
            if (fpm.key[i] != AV_NONE) out[(*n)++] = fpm.val[i];
        qsort(out, *n, sizeof *out, u64cmp);
    }
    nmap_free(&fpm);
    nmap_free(&atm);
    return out;
}

size_t av_census_rows(av_census *c, av_census_row **rows) {
    qsort(c->row, c->nrow, sizeof *c->row, by_saved);
    /* One call reaches a supercombinator's layers in turn: each layer is a
     * subterm of the one before, called as often.  Fold each row into the
     * best-ranked row it shares its calls with and is a subterm of, or
     * that is a subterm of it; a jet on the head absorbs the rest. */
    uint64_t **sub = calloc(c->nrow ? c->nrow : 1, sizeof *sub);
    size_t *nsub = calloc(c->nrow ? c->nrow : 1, sizeof *nsub);
    for (size_t i = 0; sub && nsub && i < c->nrow; i++)
        if (c->row[i].term != AV_NONE) sub[i] = subterms(c->cap, c->row[i].term, &nsub[i]);
    for (size_t i = 0; i < c->nrow; i++) {
        c->row[i].family = -1;
        c->row[i].members = 0;
        if (!sub || !sub[i]) continue;
        for (size_t h = 0; h < i; h++) {
            if (c->row[h].family >= 0 || !sub[h] || c->row[h].calls != c->row[i].calls)
                continue;
            if (bsearch(&c->row[i].fp, sub[h], nsub[h], sizeof *sub[h], u64cmp) ||
                bsearch(&c->row[h].fp, sub[i], nsub[i], sizeof *sub[i], u64cmp)) {
                c->row[i].family = (int64_t)h;
                c->row[h].members++;
                break;
            }
        }
    }
    for (size_t i = 0; sub && i < c->nrow; i++) free(sub[i]);
    free(sub);
    free(nsub);
    *rows = c->row;
    return c->nrow;
}
