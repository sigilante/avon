/**  gc.c
 *
 *  Stop-and-copy collection.  Cheney's scan over a fresh to-space, keeping
 *  forwarding in a side array rather than being written into from-space.
 *  Indirections are short-circuited: an evacuated IND becomes the copy of
 *  what it points at.
 */

#include <stdlib.h>

#include "avon.h"
#include "jets.h"
#include "sstats.h"

struct av_gc {
    const av_node *from;
    av_node       *to;
    uint32_t      *fwd;         /* from-index -> to-index, or AV_NONE */
    uint32_t       top;
};

uint32_t av_gc_evac(av_gc *g, uint32_t i) {
    while ((g->from[i].l >> AV_TAG_SHIFT) == AV_IND)
        i = g->from[i].l & AV_PAYLOAD;
    if (g->fwd[i] != AV_NONE) return g->fwd[i];
    uint32_t j = g->top++;
    g->to[j] = g->from[i];
    g->fwd[i] = j;
    return j;
}

uint32_t av_gc_forwarded(const av_gc *g, uint32_t i) {
    while ((g->from[i].l >> AV_TAG_SHIFT) == AV_IND)
        i = g->from[i].l & AV_PAYLOAD;
    return g->fwd[i];
}

/*  A root may hold AV_NONE: a result slot rooted before it is filled. */
static uint32_t evac_opt(av_gc *g, uint32_t i) {
    return i == AV_NONE ? AV_NONE : av_gc_evac(g, i);
}

bool av_collect(av_arena *a, uint32_t need, av_roots_fn roots,
                av_roots_fn after, void *ctx) {
    av_gc g;
    g.from = a->nodes;
    g.to = malloc((size_t)a->cap * sizeof *g.to);
    g.fwd = malloc((size_t)a->used * sizeof *g.fwd);
    if (!g.to || !g.fwd) {
        free(g.to);
        free(g.fwd);
        return false;
    }
    for (uint32_t i = 0; i < a->used; i++) g.fwd[i] = AV_NONE;
    g.top = 0;

    /* Leaves first, in id order, so S, K, I stay at 0, 1, 2. */
    for (uint32_t id = 0; id < a->n_leaves; id++)
        a->atom_node[id] = av_gc_evac(&g, a->atom_node[id]);
    for (uint32_t k = 0; k < a->n_roots; k++)
        *a->roots[k] = evac_opt(&g, *a->roots[k]);
    for (uint32_t k = 0; k < AV_JET_ARITY_MAX; k++)
        if (a->jet_mark[k]) a->jet_mark[k] = av_gc_evac(&g, a->jet_mark[k]);
    for (uint32_t k = 0; k < a->njets; k++) {          /* the dashboard */
        a->jets[k].fallback = av_gc_evac(&g, a->jets[k].fallback);
        a->jets[k].residual = evac_opt(&g, a->jets[k].residual);
        for (uint32_t c = 0; c < a->jets[k].nconsts; c++)
            a->jets[k].consts[c] = av_gc_evac(&g, a->jets[k].consts[c]);
    }
    for (uint32_t k = 0; k < a->nglobals; k++) {        /* templates' globals */
        a->tmpl_globals[k] = av_gc_evac(&g, a->tmpl_globals[k]);
    }
    for (uint32_t k = 0; k < 2 * a->nnats; k++)          /* known numerals */
        a->nats[k] = av_gc_evac(&g, a->nats[k]);
    if (a->word_suc) a->word_suc = av_gc_evac(&g, a->word_suc);    /* words' SUC */
    if (a->compiler[0])                                 /* the compiler jet's terms */
        for (uint32_t k = 0; k < 9; k++) a->compiler[k] = av_gc_evac(&g, a->compiler[k]);
    for (uint32_t k = 0; k < a->ninterps; k++) {        /* interpreter specs */
        av_interp *p = &a->interps[k];
        for (unsigned c = 0; c < p->nobj; c++) {
            p->octor[c] = av_gc_evac(&g, p->octor[c]);
            p->oleaf[c] = av_gc_evac(&g, p->oleaf[c]);
        }
        for (unsigned c = 0; c < p->nres; c++)
            p->rctor[c] = av_gc_evac(&g, p->rctor[c]);
    }
    if (roots) roots(&g, ctx);
    for (av_active *r = a->active; r; r = r->next)
        if (r->roots) r->roots(&g, r->ctx);

    for (uint32_t s = 0; s < g.top; s++) {
        av_node *n = &g.to[s];
        uint32_t tag = n->l >> AV_TAG_SHIFT;
        if (tag == AV_APP) {
            uint32_t l = av_gc_evac(&g, n->l);
            uint32_t r = av_gc_evac(&g, n->r);
            n = &g.to[s];
            n->l = l;
            n->r = r;
        } else if (tag == AV_JET) {
            g.to[s].r = av_gc_evac(&g, g.to[s].r);
        }
    }

    if (after) after(&g, ctx);
    for (av_active *r = a->active; r; r = r->next)
        if (r->after) r->after(&g, r->ctx);
#ifdef AV_STRICT_STATS
    sstats_collect(a, g.fwd, a->used, g.top);
#endif
    free(g.fwd);
    if (a->pma) {                       /* back into the mapping: all of it dirty */
        pma_collected(a, g.to, g.top);
        free(g.to);
    } else {
        free(a->nodes);
        a->nodes = g.to;
    }
    a->used = g.top;
    a->collections++;

    /* Keep the live set at most half the arena, and `need` free. */
    uint64_t want = a->cap;
    while (want < AV_MAX_NODES &&
           (a->used > want / 2 || want - a->used < need))
        want *= 2;
    if (want > AV_MAX_NODES) want = AV_MAX_NODES;
    if (want > a->cap) {
        if (a->pma) {
            pma_grow(a, want);
        } else {
            av_node *n = realloc(a->nodes, (size_t)want * sizeof *n);
            if (n) {
                a->nodes = n;
                a->cap = (uint32_t)want;
            }
        }
    }
    return a->cap - a->used >= need;
}
