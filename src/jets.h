/**  jets.h
 *
 *  Internal to the runtime: node-keyed maps, and what the reducer needs
 *  from the dashboard.  Not part of the public interface.
 */

#ifndef JETS_H
#define JETS_H

#include <assert.h>

#include "avon.h"

typedef struct { uint32_t *key; uint64_t *val; size_t cap, n; } nmap;

bool     nmap_get(const nmap *m, uint32_t k, uint64_t *v);
bool     nmap_put(nmap *m, uint32_t k, uint64_t v);
void     nmap_free(nmap *m);

/*  §5 digests: an atom's, from its name; an application's, from its
 *  two parts'. */
uint64_t digest_leaf(const char *name);
uint64_t digest_app(uint64_t f, uint64_t x);

/*  Every node's digest below t, keyed by viewed node. */
bool     hash_all(const av_arena *a, uint32_t t, nmap *m);

uint32_t jet_find(const av_arena *a, uint64_t digest);

/*  The profile's hooks (profile.c): charge one contraction of combinator
 *  c, whose partial applications are spine[-1] .. spine[-k], innermost
 *  first; follow a collection. */
void     profile_charge(av_profile *p, const uint32_t *spine, unsigned k, ski_leaf c);
void     profile_remap(av_profile *p, const av_gc *g);
/*  Templates (tmpl.c): an instance program's operands, as for residuals; a
 *  jet node wrapping inner for jet id (not the dashboard's term, so a run
 *  may write it); tmpl_instance, at the end of this file, an instance of
 *  T over args[0 .. T->k-1], allocating T->nops + T->nsuc nodes at most
 *  (reserve them first; it never collects).  With `into` a redex root, the
 *  instance is written there -- its root application over the node, or an
 *  indirection to it -- and `into` returned; AV_NONE, the instance's root. */
#define TMPL_CONST 0u
#define TMPL_ARG   1u
#define TMPL_RES   2u
#define TMPL_OPND(kind, i) ((kind) << 30 | (i))
uint32_t jet_wrap(av_arena *a, uint32_t id, uint32_t inner);
/*  The residual markers @x0 .. @x31, made if not yet: templates' formals. */
bool     jet_marks(av_arena *a);

/*  Words (words.c, §6.10): W (n+1) over pred, a numeral held (K or a
 *  word), in two reserved nodes, or AV_NONE if pred is not one; a word's
 *  predecessor; whether a numeral operation's term computes it on the
 *  operands 0 .. 5, run in share mode on private copies, never collecting. */
uint32_t word_succ(av_arena *a, uint32_t pred);
static inline uint32_t word_pred(const av_arena *a, uint32_t w) {
    return av_right(a, av_right(a, w));
}
bool     word_admit(av_arena *a, uint32_t term, unsigned op);
const char *av_word_pinned(unsigned op);

/*  The jet stats' hooks (jetstats.c): a fire of jet id at jet node `node`;
 *  a miss; a share-mode demotion, copied or not; a jet node made fresh
 *  from jet owner's residual or term; a collection. */
void     jetstats_fire(av_jetstats *s, uint32_t node, uint32_t id);
void     jetstats_miss(av_jetstats *s, uint32_t id);
void     jetstats_demote(av_jetstats *s, uint32_t id, bool copied);
void     jetstats_made(av_jetstats *s, uint32_t node, uint32_t owner, unsigned kind);
void     jetstats_remap(av_jetstats *s, const av_gc *g);

/*  A redex root rewritten in place is no longer loaded code. */
void     profile_rewrote(av_profile *p, uint32_t node);

/*  A fresh instance of jet id's residual over args[0 .. arity-1].  The
 *  caller has reserved jets[id].nodes nodes, so this never collects.
 *  With fresh_jets, the template's jet nodes are copied too, so a share-
 *  mode run can demote them without touching the template. */
uint32_t jet_instance(av_arena *a, uint32_t id, const uint32_t *args,
                      bool fresh_jets);

/*  A private copy of jet id's term, its inner jet nodes copied: what a
 *  share-mode run may write.  The caller has reserved jets[id].term_nodes
 *  nodes. */
uint32_t jet_term_copy(av_arena *a, uint32_t id);

/*  A dashboard entry for term t under its digest, with no residual: the
 *  key an interpreter jet (§7) attaches to.  The existing entry if any. */
uint32_t jet_entry_for(av_arena *a, uint64_t digest, uint32_t t);

/*  Fire the interpreter jet of dashboard entry id over argv[0 .. params+1]
 *  (the parameters, the fuel, the datum), spending at most host_left
 *  contractions.  1: fired, *out the outcome datum and *charge the
 *  contractions spent.  0: declined; the caller steps the interpreter.
 *  -1: stop the run with *st (and *fault if a nested check failed). */
int interp_fire(av_arena *a, uint32_t id, const uint32_t *argv,
                const av_opts *o, uint64_t host_left, uint32_t *out,
                uint64_t *charge, av_status *st, bool *fault);

/*  --jet-check for an interpreter jet: the unjetted interpreter over the
 *  same arguments must peel to the same result constructor and decode to
 *  the same payload.  False only on a definite disagreement. */
bool interp_check(av_arena *a, uint32_t id, uint32_t node, const uint32_t *argv,
                  uint32_t out);

/*  The unquoter's jet (install.c): UQ d, d the argument, installed
 *  natively; the charge is the probes' contractions.  1 fired, 0
 *  declined.  And its check against UQ's own reduction. */
int  install_fire(av_arena *a, uint32_t datum, const av_opts *o, uint64_t host_left,
                  uint32_t *out, uint64_t *charge);
bool install_check(av_arena *a, uint32_t node, uint32_t datum, uint32_t out);

/*  The compiler jet (compiler.c): abs x t, argv[0] x and argv[1] t,
 *  answered natively; and its check against the term's reduction. */
int  compile_fire(av_arena *a, const uint32_t *argv, const av_opts *o, uint64_t host_left,
                  uint32_t *out, uint64_t *charge);
bool compile_check(av_arena *a, uint32_t node, const uint32_t *argv, uint32_t out);

/*  The Poseidon2 jet's output (p2.c, §6.12): stateN s in P2_STATE_NODES
 *  reserved nodes at most; it never collects. */
#define P2_STATE_NODES (2u + 16u * 32u * 5u)
uint32_t p2_state_build(av_arena *a, const uint32_t s[16]);
/*  P's registration without the digest pin, for tests with a stand-in
 *  term; and whether x is jet id's term, node for node, within eight
 *  pairs per node of it (false past them, or out of memory). */
uint32_t p2_register(av_arena *a, uint32_t p, bool pin, const char **err);
bool     p2_same(const av_arena *a, uint32_t x, uint32_t id);

/*  The census's hook (census.c): x was put in function position with
 *  `avail` arguments at the head. */
void census_record(av_census *c, const av_arena *a, uint32_t x, size_t avail);

/*  The frame trace's hook (trace.c): before an S contraction of the head
 *  run, the slots stk[base..top).  False if the trace cannot follow. */
bool trace_step(av_trace *t, const av_arena *a, const uint32_t *stk, size_t base,
                size_t top, uint64_t step);

/*  The persistent arena (pma.c): an in-place write of node i marks its
 *  chunk; growth maps more of the reservation; a collection copies back
 *  into the mapping and marks everything; freeing unmaps. */
void pma_touch(av_arena *a, uint32_t i);
bool pma_grow(av_arena *a, uint64_t nodes);
void pma_collected(av_arena *a, const av_node *to, uint32_t used);
void pma_release(av_arena *a);

/*  An application in a node the caller has already reserved (ensure(),
 *  av_reserve): av_app with its check for room and its call inlined away,
 *  the reservation having made the room.  The instance loops' allocator. */
static inline uint32_t arena_app_reserved(av_arena *a, uint32_t f, uint32_t x) {
    assert(a->used < a->cap && "allocation past what was reserved");
    uint32_t i = a->used++;
    a->nodes[i] = (av_node){ f, x };
    return i;
}

/*  Every in-place write of an existing node goes through here. */
static inline void arena_set(av_arena *a, uint32_t i, av_node n) {
    if (a->pma) pma_touch(a, i);
    a->nodes[i] = n;
}

/*  The fact store, for the interpreter jet's native lookup (src/scry.c):
 *  which of the first n facts has path `path` (leaves leaf[i]): 1 with
 *  *which, 0 none, -1 unprintable; fact i's answer copied into a; whether
 *  t is fact i's answer; fact i's key path with the leaves leaf[i]. */
int      facts_find(const av_facts *f, size_t n, av_arena *a, uint32_t path,
                    const uint32_t *leaf, size_t *which);
uint32_t facts_answer(const av_facts *f, size_t i, av_arena *a);
bool     facts_same_answer(const av_facts *f, size_t i, const av_arena *a, uint32_t t);
uint32_t facts_live_path(const av_facts *f, size_t i, av_arena *a, const uint32_t *leaf);

/*  An instance of template T (declared above, with tmpl.c's other hooks):
 *  inlined into the reducer's two call sites, a fire's fixed cost being
 *  most of a small template's. */
static inline __attribute__((always_inline))
uint32_t tmpl_instance(av_arena *a, const av_tmpl *T, const uint32_t *args,
                                     uint32_t into) {
    /* scratch, sized at load for every template: the instructions'
     * results, then the constants' nodes */
    assert(a->tmpl_scratch_cap >= T->nops + T->nconsts);
    uint32_t *out = a->tmpl_scratch, *cv = out + T->nops;
    for (uint32_t j = 0; j < T->nconsts; j++) cv[j] = a->tmpl_globals[T->consts[j]];
    /* an operand is base[kind][index]: no branch on its kind */
    const uint32_t *const base[3] = { cv, args, out };
#define OPND(x) (base[(x) >> 30][(x) & AV_PAYLOAD])
    const uint32_t *ops = T->ops;
    uint32_t n = T->nops;
    /* the root application is written over the redex root, as S writes its
     * result: no node for it, no indirection to it */
    bool in_place = into != AV_NONE && T->root_last && !(T->sucop && T->sucop[n - 1]);
    uint32_t end = in_place ? n - 1 : n;
    if (!T->sucop) {
        /* the common loop, the arena's pointer and bump counter held in
         * locals: nothing it stores can move them */
        av_node *nodes = a->nodes;
        uint32_t used = a->used;
        assert(a->cap - used >= end && "allocation past what was reserved");
        for (uint32_t i = 0; i < end; i++) {
            nodes[used] = (av_node){ OPND(ops[2 * i]), OPND(ops[2 * i + 1]) };
            out[i] = used++;
        }
        a->used = used;
    } else {
        for (uint32_t i = 0; i < end; i++) {
            uint32_t f = OPND(ops[2 * i]), x = OPND(ops[2 * i + 1]), v;
            /* SUC of a numeral held: a word (§6.10), two nodes where one was */
            out[i] = T->sucop[i] && av_numeral(a, x, &v) && v < AV_WORD_MAX
                   ? word_succ(a, x) : arena_app_reserved(a, f, x);
        }
    }
    if (in_place) {
        arena_set(a, into, (av_node){ OPND(ops[2 * (n - 1)]), OPND(ops[2 * (n - 1) + 1]) });
        return into;
    }
    uint32_t root = OPND(T->root);
    if (into != AV_NONE)
        arena_set(a, into, (av_node){ (AV_IND << AV_TAG_SHIFT) | root, 0 });
    return into != AV_NONE ? into : root;
#undef OPND
}

#endif /* JETS_H */
