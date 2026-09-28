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

#endif /* JETS_H */
