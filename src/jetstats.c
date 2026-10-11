/**  jetstats.c
 *
 *  What each jet does on a run: its fires and the contractions they
 *  absorb, its misses---reached at the head with fewer arguments than its
 *  arity---and, in share mode, its demotions.  And for each fire, where
 *  its jet node came from:
 *
 *    top      the program as loaded, outside every jet;
 *    residual an instance of another jet J's residual, so the fire happens
 *             after J fired;
 *    term     J's term, entered because J did not fire.
 *
 *  A jet node's origin is fixed where the node is made.  At av_jetstats_begin
 *  the loaded program and every jet's templates are walked: a jet node
 *  outside every jet is top; one inside jet node J's term is J's term; the
 *  first jet nodes of J's residual template, and of its term, are J's
 *  residual and J's term.  A node the walk meets both outside and inside a
 *  jet is top, since it is reached there too.  Share mode makes fresh jet
 *  nodes when it instantiates a residual or copies a term, and records
 *  each as it goes.  The origins follow the nodes through collections.
 *
 *  Stats persist across runs and arenas, keyed by a jet's structural digest.
 */

#define _POSIX_C_SOURCE 200809L

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "jets.h"

#define TOPMARK UINT64_MAX      /* an origin entry: outside every jet */

typedef struct {
    uint64_t digest;
    unsigned arity;
    uint64_t cost;
    size_t   atoms;
    av_ctor  ctor;
    uint32_t nodes;
    av_jetstat_row c;           /* the counts */
} row;

typedef struct { uint64_t key, n; } pairslot;

struct av_jetstats {
    row      *rows;
    size_t    nrows, rowcap;
    uint32_t *row_of_id;        /* this arena's jet id -> row + 1; 0 none */
    size_t    nids;
    nmap      origin;           /* jet node -> row << 1 | kind, or TOPMARK */
    pairslot *pairs;            /* (outer row, inner row, kind) -> fires  */
    size_t    npairs, paircap;
    bool      lost;             /* out of memory: counts undercount */
};

av_jetstats *av_jetstats_new(void) { return calloc(1, sizeof(av_jetstats)); }

void av_jetstats_free(av_jetstats *s) {
    if (!s) return;
    free(s->rows);
    free(s->row_of_id);
    free(s->pairs);
    nmap_free(&s->origin);
    free(s);
}

static uint32_t row_for(av_jetstats *s, const av_jet *j) {
    for (size_t i = 0; i < s->nrows; i++)
        if (s->rows[i].digest == j->digest) return (uint32_t)i;
    if (s->nrows == s->rowcap) {
        size_t cap = s->rowcap ? 2 * s->rowcap : 64;
        row *q = realloc(s->rows, cap * sizeof *q);
        if (!q) return AV_NONE;
        s->rows = q;
        s->rowcap = cap;
    }
    s->rows[s->nrows] = (row){ .digest = j->digest, .arity = j->arity,
                               .cost = j->cost, .atoms = j->atoms, .ctor = j->ctor,
                               .nodes = j->nodes };
    return (uint32_t)s->nrows++;
}

/*  Walk from root: jet nodes met outside every jet get `outside`; below a
 *  jet node x, jet nodes get (x's row, term) unless already given one.
 *  Two passes, so a node reachable outside keeps `outside`. */
static bool walk(av_jetstats *s, const av_arena *a, uint32_t root, uint64_t outside) {
    nmap seen = { 0 };
    size_t cap = 256, top = 0, ncap = 64, nin = 0;
    uint32_t *todo = malloc(cap * sizeof *todo), *inner = malloc(ncap * sizeof *inner);
    bool ok = todo && inner;
    if (ok) todo[top++] = av_res(a, root);
    /* pass 1: outside every jet */
    while (ok && top) {
        uint32_t x = av_res(a, todo[--top]);
        uint64_t v;
        if (nmap_get(&seen, x, &v)) continue;
        if (!(ok = nmap_put(&seen, x, 1))) break;
        if (av_is_word(a, x)) continue;             /* a numeral, no jet id */
        if (av_tag(a, x) == AV_JET) {
            if (!nmap_get(&s->origin, x, &v) && !(ok = nmap_put(&s->origin, x, outside))) break;
            if (nin == ncap) {
                uint32_t *q = realloc(inner, (ncap *= 2) * sizeof *q);
                if (!q) { ok = false; break; }
                inner = q;
            }
            inner[nin++] = x;
            continue;
        }
        if (av_tag(a, x) != AV_APP) continue;
        if (top + 2 > cap) {
            uint32_t *q = realloc(todo, (cap *= 2) * sizeof *q);
            if (!q) { ok = false; break; }
            todo = q;
        }
        todo[top++] = av_right(a, x);
        todo[top++] = av_left(a, x);
    }
    /* pass 2: inside each jet node met, its term; nested jets in turn */
    while (ok && nin) {
        uint32_t j = inner[--nin];
        uint64_t jrow = s->row_of_id[AV_JET_ID(av_left(a, j))];
        uint64_t in = jrow ? (jrow - 1) << 1 | AV_FROM_TERM : TOPMARK;
        top = 0;
        todo[top++] = av_res(a, av_right(a, j));
        while (ok && top) {
            uint32_t x = av_res(a, todo[--top]);
            uint64_t v;
            if (nmap_get(&seen, x, &v)) continue;
            if (!(ok = nmap_put(&seen, x, 1))) break;
            if (av_is_word(a, x)) continue;
            if (av_tag(a, x) == AV_JET) {
                if (!nmap_get(&s->origin, x, &v) && !(ok = nmap_put(&s->origin, x, in))) break;
                if (nin == ncap) {
                    uint32_t *q = realloc(inner, (ncap *= 2) * sizeof *q);
                    if (!q) { ok = false; break; }
                    inner = q;
                }
                inner[nin++] = x;
                continue;
            }
            if (av_tag(a, x) != AV_APP) continue;
            if (top + 2 > cap) {
                uint32_t *q = realloc(todo, (cap *= 2) * sizeof *q);
                if (!q) { ok = false; break; }
                todo = q;
            }
            todo[top++] = av_right(a, x);
            todo[top++] = av_left(a, x);
        }
    }
    free(todo);
    free(inner);
    nmap_free(&seen);
    return ok;
}

bool av_jetstats_begin(av_jetstats *s, const av_arena *a, uint32_t t) {
    nmap_free(&s->origin);
    free(s->row_of_id);
    s->nids = a->njets;
    s->row_of_id = calloc(s->nids ? s->nids : 1, sizeof *s->row_of_id);
    if (!s->row_of_id) return false;
    for (uint32_t id = 0; id < a->njets; id++) {
        if (!a->jets[id].residual_ok) continue;
        uint32_t r = row_for(s, &a->jets[id]);
        if (r == AV_NONE) return false;
        s->row_of_id[id] = r + 1;
    }
    if (!walk(s, a, t, TOPMARK)) return false;
    for (uint32_t id = 0; id < a->njets; id++) {
        if (!s->row_of_id[id]) continue;
        uint64_t r = s->row_of_id[id] - 1;
        if (!walk(s, a, a->jets[id].residual, r << 1 | AV_FROM_RESIDUAL) ||
            !walk(s, a, a->jets[id].fallback, r << 1 | AV_FROM_TERM))
            return false;
    }
    return true;
}

static void pair_add(av_jetstats *s, uint64_t key) {
    if (2 * (s->npairs + 1) > s->paircap) {
        size_t cap = s->paircap ? 2 * s->paircap : 256;
        pairslot *q = calloc(cap, sizeof *q);
        if (!q) { s->lost = true; return; }
        for (size_t i = 0; i < s->paircap; i++) {
            if (!s->pairs[i].n) continue;
            size_t k = (size_t)(s->pairs[i].key * 0x9e3779b97f4a7c15u >> 20) & (cap - 1);
            while (q[k].n) k = (k + 1) & (cap - 1);
            q[k] = s->pairs[i];
        }
        free(s->pairs);
        s->pairs = q;
        s->paircap = cap;
    }
    size_t k = (size_t)(key * 0x9e3779b97f4a7c15u >> 20) & (s->paircap - 1);
    while (s->pairs[k].n && s->pairs[k].key != key) k = (k + 1) & (s->paircap - 1);
    if (!s->pairs[k].n) { s->pairs[k].key = key; s->npairs++; }
    s->pairs[k].n++;
}

void jetstats_fire(av_jetstats *s, uint32_t node, uint32_t id) {
    if (id >= s->nids || !s->row_of_id[id]) return;
    row *r = &s->rows[s->row_of_id[id] - 1];
    r->c.fires++;
    r->c.absorbed += r->cost;
    uint64_t o;
    if (!nmap_get(&s->origin, node, &o) || o == TOPMARK) { r->c.top++; return; }
    unsigned kind = (unsigned)(o & 1);
    if (kind == AV_FROM_RESIDUAL) r->c.in_residual++;
    else r->c.in_term++;
    pair_add(s, (o >> 1) << 33 | (uint64_t)(s->row_of_id[id] - 1) << 1 | kind);
}

void jetstats_miss(av_jetstats *s, uint32_t id) {
    if (id < s->nids && s->row_of_id[id]) s->rows[s->row_of_id[id] - 1].c.misses++;
}

void jetstats_demote(av_jetstats *s, uint32_t id, bool copied) {
    if (id >= s->nids || !s->row_of_id[id]) return;
    row *r = &s->rows[s->row_of_id[id] - 1];
    r->c.demotions++;
    if (copied) r->c.copies++;
}

void jetstats_made(av_jetstats *s, uint32_t node, uint32_t owner, unsigned kind) {
    if (owner >= s->nids || !s->row_of_id[owner]) return;
    if (!nmap_put(&s->origin, node, (uint64_t)(s->row_of_id[owner] - 1) << 1 | kind))
        s->lost = true;
}

void jetstats_remap(av_jetstats *s, const av_gc *g) {
    nmap old = s->origin, fresh = { 0 };
    for (size_t i = 0; i < old.cap; i++) {
        if (old.key[i] == AV_NONE) continue;
        uint32_t j = av_gc_forwarded(g, old.key[i]);
        if (j != AV_NONE && !nmap_put(&fresh, j, old.val[i])) s->lost = true;
    }
    nmap_free(&old);
    s->origin = fresh;
}

/*  ----------------------------------------------------------- reading */

size_t av_jetstats_rows(const av_jetstats *s) { return s->nrows; }

bool av_jetstats_lost(const av_jetstats *s) { return s->lost; }

void av_jetstats_row(const av_jetstats *s, size_t i, char hash[27], unsigned *arity,
                     uint64_t *cost, size_t *atoms, av_jetstat_row *counts) {
    const row *r = &s->rows[i];
    snprintf(hash, 27, AV_HASH_VERSION ":%016llx", (unsigned long long)r->digest);
    *arity = r->arity;
    *cost = r->cost;
    *atoms = r->atoms;
    *counts = r->c;
    counts->ctor = r->ctor;
    counts->nodes = r->nodes;
}

bool av_jetstats_find(const av_jetstats *s, const char *hash, size_t *i) {
    uint64_t d;
    if (!av_hash_parse(hash, &d)) return false;
    for (size_t k = 0; k < s->nrows; k++)
        if (s->rows[k].digest == d) { *i = k; return true; }
    return false;
}

size_t av_jetstats_pairs(const av_jetstats *s, av_jetstat_pair **out) {
    *out = malloc((s->npairs ? s->npairs : 1) * sizeof **out);
    if (!*out) return 0;
    size_t n = 0;
    for (size_t k = 0; k < s->paircap; k++) {
        if (!s->pairs[k].n) continue;
        uint64_t key = s->pairs[k].key;
        (*out)[n++] = (av_jetstat_pair){ (size_t)(key >> 33),
                                         (size_t)(key >> 1 & 0xffffffffu),
                                         (unsigned)(key & 1), s->pairs[k].n };
    }
    return n;
}
