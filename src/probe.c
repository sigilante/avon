/**  probe.c
 *
 *  Reading values behaviourally (docs/DESIGN.md §0, §7): apply a term to
 *  fresh marker atoms, reduce to weak head normal form, and see which
 *  marker comes back with what.  A transcription of python/skijack/run.py's
 *  peel and decode and probe.py's read_nat.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "avon.h"

static uint32_t marker(av_arena *a, unsigned i) {
    char name[16];
    int n = snprintf(name, sizeof name, "@%u", i);
    return av_leaf(a, name, (size_t)n);
}

/*  Probe t with nmarks markers; on success the head's marker index and its
 *  arguments, first argument first. */
static bool probe(av_arena *a, uint32_t t, unsigned nmarks, const av_opts *o,
                  unsigned *which, uint32_t *args, unsigned maxargs,
                  unsigned *nargs, const char **err) {
    ski_leaf *ids = malloc((nmarks ? nmarks : 1) * sizeof *ids);
    if (!ids) { *err = "out of memory"; return false; }
    for (unsigned i = 0; i < nmarks; i++) {
        uint32_t m = marker(a, i);
        if (m == AV_NONE) { free(ids); *err = "out of memory"; return false; }
        ids[i] = av_right(a, m);
        t = av_app(a, t, m);
        if (t == AV_NONE) { free(ids); *err = "out of memory"; return false; }
    }
    av_opts po = *o;
    po.whnf_only = true;
    po.no_collect = true;
    av_result r = av_reduce(a, t, &po);
    a->probe_steps += r.steps;
    if (r.status != AV_WHNF && r.status != AV_NORMAL) {
        free(ids);
        *err = "probing did not reach weak head normal form";
        return false;
    }

    /* the spine: head, then arguments, collected last first */
    uint32_t spine[AV_PEEL_MAX + 1];
    unsigned n = 0;
    uint32_t h = av_view(a, r.term);
    while (av_tag(a, h) == AV_APP) {
        if (n == maxargs) {
            free(ids);
            *err = "a constructor carried too many fields";
            return false;
        }
        spine[n++] = av_right(a, h);
        h = av_view(a, av_left(a, h));
    }
    /* which marker, by its leaf id: no order among the ids is assumed */
    ski_leaf id = av_tag(a, h) == AV_LEAF ? av_right(a, h) : AV_NONE;
    unsigned w = 0;
    while (w < nmarks && ids[w] != id) w++;
    free(ids);
    if (id == AV_NONE || w == nmarks) {
        *err = "the head is not a marker: not a value of this type";
        return false;
    }
    *which = w;
    for (unsigned i = 0; i < n; i++) args[i] = spine[n - 1 - i];
    *nargs = n;
    return true;
}

bool av_peel(av_arena *a, uint32_t t, unsigned nctors, const av_opts *o,
             av_peeled *out, const char **err) {
    const char *msg = NULL;
    bool ok = probe(a, t, nctors, o, &out->ctor, out->field, AV_PEEL_MAX,
                    &out->nfields, &msg);
    if (!ok && err) *err = msg;
    return ok;
}

/*  -------------------------------------------------------------- decode */

/* An open-addressing map from node index to decoded term. */
typedef struct { uint32_t *key, *val; size_t cap, n; } memo;

static uint32_t memo_get(const memo *m, uint32_t k) {
    if (!m->cap) return AV_NONE;
    for (size_t i = (k * 2654435761u) & (m->cap - 1);; i = (i + 1) & (m->cap - 1)) {
        if (m->key[i] == AV_NONE) return AV_NONE;
        if (m->key[i] == k) return m->val[i];
    }
}

static bool memo_put(memo *m, uint32_t k, uint32_t v) {
    if (2 * (m->n + 1) > m->cap) {
        memo g = { NULL, NULL, m->cap ? m->cap * 2 : 1024, 0 };
        g.key = malloc(g.cap * sizeof *g.key);
        g.val = malloc(g.cap * sizeof *g.val);
        if (!g.key || !g.val) { free(g.key); free(g.val); return false; }
        for (size_t i = 0; i < g.cap; i++) g.key[i] = AV_NONE;
        for (size_t i = 0; i < m->cap; i++)
            if (m->key[i] != AV_NONE) memo_put(&g, m->key[i], m->val[i]);
        free(m->key);
        free(m->val);
        *m = g;
    }
    size_t i = (k * 2654435761u) & (m->cap - 1);
    while (m->key[i] != AV_NONE && m->key[i] != k) i = (i + 1) & (m->cap - 1);
    if (m->key[i] == AV_NONE) m->n++;
    m->key[i] = k;
    m->val[i] = v;
    return true;
}

uint32_t av_decode(av_arena *a, uint32_t datum, unsigned nctors,
                   const char *const *names, unsigned app_ctor,
                   size_t max_probes, const av_opts *o, const char **err) {
    /* work items: a node to decode, or (node | DONE) to build its App */
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 256, top = 0, nbuilt = 0, bcap = 256, probes = 0;
    item *todo = malloc(cap * sizeof *todo);
    uint32_t *built = malloc(bcap * sizeof *built);
    memo m = { NULL, NULL, 0, 0 };
    const char *msg = NULL;
    uint32_t out = AV_NONE;
    if (!todo || !built) { msg = "out of memory"; goto done; }

    todo[top++] = (item){ datum, false };
    while (top) {
        item it = todo[--top];
        if (nbuilt + 1 > bcap) {
            uint32_t *b = realloc(built, (bcap *= 2) * sizeof *b);
            if (!b) { msg = "out of memory"; goto done; }
            built = b;
        }
        if (it.done) {
            uint32_t r = built[--nbuilt], l = built[--nbuilt];
            uint32_t e = av_app(a, l, r);
            if (e == AV_NONE || !memo_put(&m, it.node, e)) { msg = "out of memory"; goto done; }
            built[nbuilt++] = e;
            continue;
        }
        uint32_t hit = memo_get(&m, it.node);
        if (hit != AV_NONE) {
            built[nbuilt++] = hit;
            continue;
        }
        if (++probes > max_probes) { msg = "datum has more nodes than the probe limit"; goto done; }
        unsigned which, nargs;
        uint32_t args[AV_PEEL_MAX];
        if (!probe(a, it.node, nctors, o, &which, args, AV_PEEL_MAX, &nargs, &msg))
            goto done;
        if (which == app_ctor) {
            if (nargs != 2) { msg = "the application constructor did not carry two fields"; goto done; }
            if (top + 3 > cap) {
                item *t = realloc(todo, (cap *= 2) * sizeof *t);
                if (!t) { msg = "out of memory"; goto done; }
                todo = t;
            }
            todo[top++] = (item){ it.node, true };
            todo[top++] = (item){ args[1], false };
            todo[top++] = (item){ args[0], false };
        } else {
            uint32_t leaf = av_leaf(a, names[which], strlen(names[which]));
            if (leaf == AV_NONE || !memo_put(&m, it.node, leaf)) { msg = "out of memory"; goto done; }
            built[nbuilt++] = leaf;
        }
    }
    out = built[--nbuilt];

done:
    free(todo);
    free(built);
    free(m.key);
    free(m.val);
    if (msg && err) *err = msg;
    return msg ? AV_NONE : out;
}

/*  ------------------------------------------------------------- numerals */

bool av_read_nat(av_arena *a, uint32_t t, size_t max_depth, const av_opts *o,
                 uint64_t *n, const char **err) {
    const char *msg = NULL;
    uint64_t k = 0;
    for (size_t d = 0; d < max_depth; d++) {
        unsigned which, nargs;
        uint32_t args[AV_PEEL_MAX];
        if (!probe(a, t, 2, o, &which, args, AV_PEEL_MAX, &nargs, &msg)) break;
        if (which == 0 && nargs == 0) { *n = k; return true; }         /* z */
        if (which == 1 && nargs == 1) { k++; t = args[0]; continue; }  /* s n */
        msg = "not a Scott numeral";
        break;
    }
    if (!msg) msg = "numeral deeper than the limit";
    if (err) *err = msg;
    return false;
}
