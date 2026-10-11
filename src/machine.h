/**  machine.h
 *
 *  Internal to the reducer: R, the state both machines run on, and what
 *  the copy machine (copy.c) and the share machine (reduce.c) both
 *  use---allocation, the stack's growth, the jet tests---with each one's
 *  entry points.  Not part of the public interface.
 */

#ifndef MACHINE_H
#define MACHINE_H

#include <stdlib.h>

#include "avon.h"
#include "jets.h"

/*  An allocation that ensure() has already reserved room for.  It cannot
 *  fail unless a `need` count is wrong, which the debug build catches.
 */
static inline uint32_t reserved_app(av_arena *a, uint32_t f, uint32_t x) {
    return arena_app_reserved(a, f, x);
}

typedef struct { uint32_t head; size_t base, n, i; } frame;

/*  A share-mode stack entry (stack.h), its kind in a node index's two
 *  spare bits: a node of the graph; a node whose update is deferred, its
 *  application this entry's argument (in dstk) and the entry above; or an
 *  application with no node, of the entry above to the argument the entry
 *  holds. */
enum { SK_REAL, SK_DEFER, SK_VIRT };
typedef struct { uint32_t at, arg; } dentry;     /* the stack stays below 2^32 entries */

typedef struct {
    av_arena      *a;
    const av_opts *o;
    uint64_t       steps;

    uint32_t      *stk;         /* copy: argument slots; share: the spine */
    size_t         top, cap;
    frame         *fr;          /* copy: normal-form frames               */
    size_t         nfr, frcap;
    uint32_t      *work;        /* share: nodes still to normalize        */
    size_t         nwork, workcap;

    uint32_t       head;        /* copy: the current position's head leaf */
    size_t         base;        /* copy: its first argument slot          */
    uint32_t       root;
    uint32_t       cur;         /* share: the node being reduced          */

    uint64_t      *marks;       /* share: nodes already normalized        */
    size_t         nmarks;      /* words                                  */

    uint64_t       jet_calls, jet_steps;
    uint64_t       tmpl_calls;
    uint64_t       dispatches, fused, word_ops, fix_calls, joins;
    uint64_t       p2_calls, p2_declines, p2_unbound, deferred;
    uint32_t      *p2c;         /* share: a chain of P calls, its call and
                                   jet node at each level, outermost first */
    size_t         p2cap;
    av_node        p2_seen;     /* share: the jet node last found P's, as  */
    uint32_t       p2_node;     /* it stood, and where, before collection  */
    uint64_t       p2_gen;      /* p2_gen - 1; 0 none                      */
    uint64_t       interp_calls;
    bool           jet_fault;
    uint32_t       jnode;       /* share: a jet node being demoted        */
    bool           normal;      /* share: making the normal form, or the
                                   root's term's head normal form, where a
                                   word must become its term's            */

    /* share: deferred roots (stack.h) */
    bool           defer;       /* instances may defer their roots        */
    dentry        *dstk;        /* the SK_DEFER entries, rising           */
    size_t         ndstk, dcap;
    size_t         nvirt;       /* SK_VIRT entries: the arena keeps that
                                   many nodes free, so writing them never
                                   fails                                  */
    uint32_t       hold;        /* share: the head, across a collection   */
    nmap           ymemo;       /* --memory: generator g -> y0, the
                                   one Y g every unfolding of g passes
                                   on, never written, and u0 = g y0, the
                                   one unfolding, updated as any node:
                                   y0 << 32 | u0, or YM_NONE once y0 is
                                   written; weak across collections       */
} R;

/*  Make room for k allocations, collecting if the arena is full.  False
 *  means the live set would exceed max_nodes, or memory ran out: SIZE.
 *  The test is inline; ensure_slow (reduce.c) reserves or collects.
 */
bool ensure_slow(R *r, size_t k);

static inline bool ensure(R *r, size_t k) {
    if (k > AV_MAX_NODES) return false;
    if (r->a->cap - r->a->used >= k) return true;
    return ensure_slow(r, k);
}

static inline bool grow(uint32_t **v, size_t *cap, size_t need) {
    if (need <= *cap) return true;
    size_t c = *cap ? *cap : 1024;
    while (c < need) c *= 2;
    uint32_t *p = realloc(*v, c * sizeof *p);
    if (!p) return false;
    *v = p;
    *cap = c;
    return true;
}

static inline bool push(R *r, uint32_t x) {
    if (r->top == r->cap && !grow(&r->stk, &r->cap, r->top + 1)) return false;
    r->stk[r->top++] = x;
    return true;
}

static inline bool interrupted(const R *r) {
    return r->o->interrupt && *r->o->interrupt;
}

/*  Whether a jet node at a position with `have` arguments fires: jets on,
 *  enough arguments, and the fuel left covers the charge, so that stepping
 *  instead would not have stopped part way. */
static inline bool fires(const R *r, uint32_t id, size_t have) {
    const av_jet *j = &r->a->jets[id];
    return r->o->jets && have >= j->arity &&
           r->o->max_steps - r->steps >= j->cost;
}

/*  Whether jet id has any of try_interp's roles: most jets have none, and
 *  the reducers skip the call for them. */
static inline bool interp_role(const av_arena *a, uint32_t id) {
    const av_jet *j = &a->jets[id];
    return j->unquote || j->compiler || j->interp >= 0;
}

/*  The jets, in reduce.c: --jet-check's comparison, the arguments
 *  a fire consumes, and an interpreter, unquoter or compiler jet's fire. */
bool      check_fire(R *r, uint32_t node, uint32_t id, const uint32_t *args);
unsigned  fire_nargs(const R *r, uint32_t id);
int       try_interp(R *r, uint32_t *nodep, size_t have, av_status *st, uint32_t *outp);

/*  The copy machine, in copy.c: a run from r->root, and the whole state
 *  as a term when a run stops early. */
av_status run_copy(R *r);
uint32_t  copy_state(R *r);

#endif
