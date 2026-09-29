/**  jets.h
 *
 *  Internal to the runtime: node-keyed maps, and what the reducer needs
 *  from the dashboard.  Not part of the public interface.
 */

#ifndef JETS_H
#define JETS_H

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

/*  The census's hook (census.c): x was put in function position with
 *  `avail` arguments at the head. */
void census_record(av_census *c, const av_arena *a, uint32_t x, size_t avail);

/*  The persistent arena (pma.c): an in-place write of node i marks its
 *  chunk; growth maps more of the reservation; a collection copies back
 *  into the mapping and marks everything; freeing unmaps. */
void pma_touch(av_arena *a, uint32_t i);
bool pma_grow(av_arena *a, uint64_t nodes);
void pma_collected(av_arena *a, const av_node *to, uint32_t used);
void pma_release(av_arena *a);

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

#endif /* JETS_H */
