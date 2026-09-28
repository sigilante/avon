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

/*  Every node's digest below t, keyed by viewed node. */
bool     hash_all(const av_arena *a, uint32_t t, nmap *m);

uint32_t jet_find(const av_arena *a, uint64_t digest);

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

#endif /* JETS_H */
