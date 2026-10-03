/**  arena.c
 *
 *  Allocation, leaf interning, and caller roots (docs/DESIGN.md §2).
 */

#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "jets.h"

static const char *const comb_name[SKI_ATOM_FIRST] = { "S", "K", "I" };

const char *av_status_name(av_status s) {
    switch (s) {
    case AV_WHNF:        return "WHNF";
    case AV_NORMAL:      return "NORMAL";
    case AV_FUEL:        return "FUEL";
    case AV_SIZE:        return "SIZE";
    case AV_INTERRUPTED: return "INTERRUPTED";
    }
    return "?";
}

static bool grow_nodes(av_arena *a) {
    if (a->cap >= AV_MAX_NODES) return false;
    uint64_t want = (uint64_t)a->cap * 2;
    if (a->pma) return pma_grow(a, want);          /* the base never moves */
    uint32_t cap = want > AV_MAX_NODES ? AV_MAX_NODES : (uint32_t)want;
    av_node *n = realloc(a->nodes, (size_t)cap * sizeof *n);
    if (!n) return false;
    a->nodes = n;
    a->cap = cap;
    return true;
}

static uint32_t alloc_node(av_arena *a, uint32_t l, uint32_t r) {
    if (a->used == a->cap && !grow_nodes(a)) return AV_NONE;
    uint32_t i = a->used++;
    a->nodes[i] = (av_node){ l, r };
    return i;
}

static uint32_t new_leaf(av_arena *a, ski_leaf id) {
    return alloc_node(a, AV_LEAF << AV_TAG_SHIFT, id);
}

av_arena *av_arena_new(uint32_t cap) {
    if (cap < 64) cap = 64;
    if (cap > AV_MAX_NODES) cap = AV_MAX_NODES;
    av_arena *a = calloc(1, sizeof *a);
    if (!a) return NULL;
    a->nodes = malloc((size_t)cap * sizeof *a->nodes);
    a->leaf_cap = 16;
    a->atom_name = calloc(a->leaf_cap, sizeof *a->atom_name);
    a->atom_node = calloc(a->leaf_cap, sizeof *a->atom_node);
    if (!a->nodes || !a->atom_name || !a->atom_node) {
        av_arena_free(a);
        return NULL;
    }
    a->cap = cap;
    for (ski_leaf id = 0; id < SKI_ATOM_FIRST; id++)
        a->atom_node[id] = new_leaf(a, id);        /* indices 0, 1, 2 */
    a->n_leaves = SKI_ATOM_FIRST;
    return a;
}

void av_arena_free(av_arena *a) {
    if (!a) return;
    for (uint32_t id = SKI_ATOM_FIRST; id < a->n_leaves; id++)
        free(a->atom_name[id]);
    free(a->atom_name);
    free(a->atom_node);
    free(a->roots);
    for (uint32_t k = 0; k < a->njets; k++) {
        free(a->jets[k].ops);
        free(a->jets[k].consts);
    }
    free(a->jets);
    free(a->jet_scratch);
    for (uint32_t k = 0; k < a->ntmpls; k++) {
        free(a->tmpls[k].ops);
        free(a->tmpls[k].consts);
        free(a->tmpls[k].sucop);
        free(a->tmpls[k].case_spine);
    }
    free(a->tmpls);
    free(a->tmpl_globals);
    free(a->tmpl_scratch);
    free(a->interps);
    free(a->nats);
    free(a->jet_index);
    if (a->pma) pma_release(a);
    else free(a->nodes);
    free(a);
}

bool av_reserve(av_arena *a, uint32_t k) {
    while (a->cap - a->used < k)
        if (!grow_nodes(a)) return false;
    return true;
}

uint32_t av_app(av_arena *a, uint32_t f, uint32_t x) {
    return alloc_node(a, f, x);
}

uint32_t av_leaf(av_arena *a, const char *name, size_t len) {
    for (ski_leaf id = 0; id < SKI_ATOM_FIRST; id++)
        if (len == 1 && name[0] == comb_name[id][0]) return a->atom_node[id];
    for (ski_leaf id = SKI_ATOM_FIRST; id < a->n_leaves; id++)
        if (strlen(a->atom_name[id]) == len &&
            memcmp(a->atom_name[id], name, len) == 0)
            return a->atom_node[id];

    if (a->n_leaves == a->leaf_cap) {
        uint32_t cap = a->leaf_cap * 2;
        char **nm = realloc(a->atom_name, cap * sizeof *nm);
        if (!nm) return AV_NONE;
        a->atom_name = nm;
        uint32_t *nd = realloc(a->atom_node, cap * sizeof *nd);
        if (!nd) return AV_NONE;
        a->atom_node = nd;
        a->leaf_cap = cap;
    }
    char *copy = malloc(len + 1);
    if (!copy) return AV_NONE;
    memcpy(copy, name, len);
    copy[len] = '\0';
    ski_leaf id = a->n_leaves;
    uint32_t node = new_leaf(a, id);
    if (node == AV_NONE) {
        free(copy);
        return AV_NONE;
    }
    a->atom_name[id] = copy;
    a->atom_node[id] = node;
    a->n_leaves++;
    return node;
}

const char *av_leaf_name(const av_arena *a, ski_leaf id) {
    if (id < SKI_ATOM_FIRST) return comb_name[id];
    return id < a->n_leaves ? a->atom_name[id] : "?";
}

void av_root_push(av_arena *a, uint32_t *idx) {
    if (a->n_roots == a->root_cap) {
        uint32_t cap = a->root_cap ? a->root_cap * 2 : 16;
        uint32_t **r = realloc(a->roots, cap * sizeof *r);
        if (!r) abort();            /* a lost root is a silent corruption */
        a->roots = r;
        a->root_cap = cap;
    }
    a->roots[a->n_roots++] = idx;
}

void av_root_pop(av_arena *a) {
    if (a->n_roots) a->n_roots--;
}
