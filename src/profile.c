/**  profile.c
 *
 *  A share-mode profile (docs/DESIGN.md §6.7): which named terms a run's
 *  contractions execute.  At load, every node of the term belongs to the
 *  innermost subterm whose §5 hash a names file gives, or to none; the
 *  ownership follows the nodes through collections.  Leaves are one node
 *  per atom, shared by every term, so they belong to no one.
 *
 *  A contraction is charged to the first node of the loaded term among
 *  its combinator's partial applications, innermost first: `S f` then
 *  `S f g`, `K x`, the redex `I x`.  Share mode rewrites a redex root in
 *  place, and a loaded node it rewrites holds the run's work from then
 *  on, so it leaves the loaded term.  When the run built or rewrote them
 *  all -- a combinator passed as a value, a Scott boolean chosen by a
 *  case -- the contraction goes to a row of its own.
 */

/*  An owner entry for a loaded node the run has rewritten. */
#define REWRITTEN UINT64_MAX

#define _POSIX_C_SOURCE 200809L

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "jets.h"

typedef struct { uint64_t digest; uint32_t row; } dname;

struct av_profile {
    char    **names;            /* row i's name; rows 0-3 are fixed      */
    uint64_t *counts;
    size_t    nrows, rowcap;
    dname    *by_digest;        /* sorted once av_profile_begin runs     */
    size_t    ndig, digcap;
    nmap      owner;            /* node -> row, for the loaded term      */
    uint64_t  total;
    bool      lost;             /* a remap ran out of memory             */
};

av_profile *av_profile_new(void) {
    av_profile *p = calloc(1, sizeof *p);
    if (!p) return NULL;
    p->rowcap = 64;
    p->names = malloc(p->rowcap * sizeof *p->names);
    p->counts = calloc(p->rowcap, sizeof *p->counts);
    if (!p->names || !p->counts) { av_profile_free(p); return NULL; }
    static const char *const fixed[4] = {
        "(loaded, no name)", "(built at run time) S", "(built at run time) K",
        "(built at run time) I" };
    for (; p->nrows < 4; p->nrows++)
        if (!(p->names[p->nrows] = strdup(fixed[p->nrows]))) {
            av_profile_free(p);
            return NULL;
        }
    return p;
}

void av_profile_free(av_profile *p) {
    if (!p) return;
    for (size_t i = 0; i < p->nrows; i++) free(p->names[i]);
    free(p->names);
    free(p->counts);
    free(p->by_digest);
    nmap_free(&p->owner);
    free(p);
}

static dname *find(const av_profile *p, uint64_t digest) {
    for (size_t i = 0; i < p->ndig; i++)        /* before sorting: a scan */
        if (p->by_digest[i].digest == digest) return &p->by_digest[i];
    return NULL;
}

bool av_profile_name(av_profile *p, const char *hash, const char *name) {
    uint64_t d;
    if (!av_hash_parse(hash, &d)) return false;
    dname *hit = find(p, d);
    if (hit) {                                  /* one term, several names */
        char *old = p->names[hit->row];
        size_t n = strlen(old) + strlen(name) + 2;
        char *m = malloc(n);
        if (!m) return false;
        snprintf(m, n, "%s/%s", old, name);
        free(old);
        p->names[hit->row] = m;
        return true;
    }
    if (p->nrows == p->rowcap) {
        size_t cap = 2 * p->rowcap;
        char **nm = realloc(p->names, cap * sizeof *nm);
        if (!nm) return false;
        p->names = nm;
        uint64_t *c = realloc(p->counts, cap * sizeof *c);
        if (!c) return false;
        memset(c + p->rowcap, 0, (cap - p->rowcap) * sizeof *c);
        p->counts = c;
        p->rowcap = cap;
    }
    if (p->ndig == p->digcap) {
        size_t cap = p->digcap ? 2 * p->digcap : 64;
        dname *q = realloc(p->by_digest, cap * sizeof *q);
        if (!q) return false;
        p->by_digest = q;
        p->digcap = cap;
    }
    p->names[p->nrows] = strdup(name);
    if (!p->names[p->nrows]) return false;
    p->by_digest[p->ndig++] = (dname){ d, (uint32_t)p->nrows++ };
    return true;
}

static int by_digest(const void *x, const void *y) {
    uint64_t a = ((const dname *)x)->digest, b = ((const dname *)y)->digest;
    return (a > b) - (a < b);
}

static uint32_t row_of(const av_profile *p, uint64_t digest) {
    dname key = { digest, 0 };
    const dname *hit = bsearch(&key, p->by_digest, p->ndig, sizeof key, by_digest);
    return hit ? hit->row : 0;
}

bool av_profile_begin(av_profile *p, const av_arena *a, uint32_t t) {
    if (p->ndig) qsort(p->by_digest, p->ndig, sizeof *p->by_digest, by_digest);
    nmap digests = { 0 };
    if (!hash_all(a, t, &digests)) { nmap_free(&digests); return false; }
    /* top down, each node owned by the innermost named subterm above it;
     * a node reached twice keeps its first owner */
    typedef struct { uint32_t node, row; } item;
    size_t cap = 256, top = 0;
    item *todo = malloc(cap * sizeof *todo);
    bool ok = todo != NULL;
    if (ok) todo[top++] = (item){ av_view(a, t), 0 };
    while (ok && top) {
        item it = todo[--top];
        uint64_t v;
        if (nmap_get(&p->owner, it.node, &v)) continue;
        uint64_t d;
        uint32_t row = nmap_get(&digests, it.node, &d) ? row_of(p, d) : 0;
        if (!row) row = it.row;
        if (av_tag(a, it.node) != AV_APP) continue;    /* leaves are shared */
        if (!nmap_put(&p->owner, it.node, row)) { ok = false; break; }
        if (top + 2 > cap) {
            item *q = realloc(todo, (cap *= 2) * sizeof *q);
            if (!q) { ok = false; break; }
            todo = q;
        }
        todo[top++] = (item){ av_view(a, av_right(a, it.node)), row };
        todo[top++] = (item){ av_view(a, av_left(a, it.node)), row };
    }
    free(todo);
    nmap_free(&digests);
    return ok;
}

void profile_charge(av_profile *p, const uint32_t *spine, unsigned k, ski_leaf c) {
    uint64_t row = c == SKI_S ? 1 : c == SKI_K ? 2 : 3;
    for (unsigned i = 1; i <= k; i++) {
        uint64_t r;
        if (nmap_get(&p->owner, spine[-(long)i], &r) && r != REWRITTEN) { row = r; break; }
    }
    p->counts[row]++;
    p->total++;
}

void profile_rewrote(av_profile *p, uint32_t node) {
    uint64_t r;
    if (nmap_get(&p->owner, node, &r) && r != REWRITTEN && !nmap_put(&p->owner, node, REWRITTEN))
        p->lost = true;
}

void profile_remap(av_profile *p, const av_gc *g) {
    nmap old = p->owner, fresh = { 0 };
    bool ok = true;
    for (size_t i = 0; ok && i < old.cap; i++) {
        if (old.key[i] == AV_NONE) continue;
        uint32_t j = av_gc_forwarded(g, old.key[i]);
        if (j != AV_NONE) ok = nmap_put(&fresh, j, old.val[i]);
    }
    nmap_free(&old);
    p->owner = fresh;
    if (!ok) p->lost = true;
}

static const av_profile *sorting;

static int by_count(const void *x, const void *y) {
    uint64_t a = sorting->counts[*(const uint32_t *)x];
    uint64_t b = sorting->counts[*(const uint32_t *)y];
    return (a < b) - (a > b);
}

void av_profile_report(const av_profile *p, FILE *out, size_t top) {
    uint32_t *ix = malloc(p->nrows * sizeof *ix);
    if (!ix) return;
    for (size_t i = 0; i < p->nrows; i++) ix[i] = (uint32_t)i;
    sorting = p;
    qsort(ix, p->nrows, sizeof *ix, by_count);
    fprintf(out, "profile: %llu contractions charged%s\n", (unsigned long long)p->total,
            p->lost ? " (ownership lost to memory: rows undercount)" : "");
    for (size_t k = 0; k < p->nrows && k < top; k++) {
        uint64_t c = p->counts[ix[k]];
        if (!c) break;
        fprintf(out, "%14llu %6.2f  %s\n", (unsigned long long)c,
                p->total ? 100.0 * (double)c / (double)p->total : 0.0, p->names[ix[k]]);
    }
    free(ix);
}

uint64_t av_profile_count(const av_profile *p, const char *name) {
    for (size_t i = 0; i < p->nrows; i++)
        if (strcmp(p->names[i], name) == 0) return p->counts[i];
    return 0;
}

uint64_t av_profile_total(const av_profile *p) { return p->total; }
