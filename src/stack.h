/**  stack.h
 *
 *  The share machine's spine stack, with deferred roots.  Static, and
 *  included by reduce.c alone, so the share loop inlines it.
 *
 *  An instance writes its body over the redex root, and the reducer at
 *  once unwinds the body's spine again: those spine cells are 61 to 65% of
 *  what instances write, and most are contracted through at the next step
 *  (docs/BENCHMARK.md, "Most spine cells are contracted through at
 *  once").  The Reduceron writes no spine; neither does a deferred
 *  instance.  It leaves the redex root's node as it was, SK_DEFER, keeps
 *  the body's outermost argument in the root's stack entry, and pushes the
 *  rest of the root's spine as SK_VIRT entries, applications with no node,
 *  each the entry above applied to its argument (av_tmpl.vspine: the spine
 *  applications used by their parent alone).  A contraction at a virtual
 *  entry builds no node for its redex root either.
 *
 *  A deferred root is written, with the application its entries stand
 *  for, before anything else could read it:
 *  - before a contraction consumes it as a function part (prepare): it is
 *    then a value, the head lacking arguments, and the graph shares it;
 *  - when the reduction stops, at a weak head normal form or otherwise
 *    (materialize, stop);
 *  - before the rarer steps that read the stack as nodes: interpreter,
 *    Poseidon2 and residual jets (materialize from the bottom).
 *  A contraction whose redex root it is writes it as an undeferred root.
 *  The graph is acyclic (§2), so no reduction in progress can reach a
 *  deferred node through another path, so a deferred node is overwritten
 *  with I I, holding nothing; writing the deferred roots never fails,
 *  since the arena keeps a node free for each virtual entry (nvirt).
 *  Every contraction is the one the undeferred reducer makes, at the same
 *  step: the steps, the counts and every state reported are the same, and
 *  only nodes go unwritten -- unless a node cap binds, where the reserve
 *  and a stop's writes may move the step that hits it.
 *
 *  A real entry's node has the entry above it as its function part; a
 *  deferred or virtual entry's is the entry above it.  Virtual entries
 *  are pushed only above a deferred one, so no real entry is ever below a
 *  virtual one; the deferred entries' indices rise with the stack (dstk).
 */


#ifndef STACK_H
#define STACK_H

#include <assert.h>

#include "machine.h"

/*  An entry's kind and its node or argument. */
#define SK_KIND(e) ((e) >> AV_TAG_SHIFT)
#define SK_BODY(e) ((e) & AV_PAYLOAD)
#define SK_MAKE(k, x) ((uint32_t)(k) << AV_TAG_SHIFT | (x))

/*  The argument of stack entry i, unresolved.  A deferred entry is read
 *  only as a redex root's, the highest deferred entry then (prepare). */
static inline uint32_t sarg(const R *r, size_t i) {
    uint32_t e = r->stk[i];
    if (SK_KIND(e) == SK_REAL) return av_right(r->a, e);
    if (SK_KIND(e) == SK_VIRT) return SK_BODY(e);
    assert(r->ndstk && r->dstk[r->ndstk - 1].at == i);
    return r->dstk[r->ndstk - 1].arg;
}

/*  ensure() for k nodes and the virtual entries' reserve, the head *curp
 *  held across a collection. */
static bool hensure(R *r, size_t k, uint32_t *curp) {
    k += r->nvirt;
    if (r->a->cap - r->a->used >= k) return true;
    r->hold = *curp;
    bool ok = ensure(r, k);
    *curp = r->hold;
    r->hold = AV_NONE;
    return ok;
}

/*  Entry i, a deferred root's, is written: no longer deferred. */
static inline void undefer(R *r, size_t i) {
    if (SK_KIND(r->stk[i]) != SK_DEFER) return;
    assert(r->ndstk && r->dstk[r->ndstk - 1].at == i);
    r->ndstk--;
    r->stk[i] = SK_BODY(r->stk[i]);
}

/*  The entries from `from` to the top are popped: the virtual among them
 *  leave the reserve. */
static inline void vpop(R *r, size_t from) {
    if (!r->nvirt) return;
    for (size_t j = from; j < r->top; j++) r->nvirt -= SK_KIND(r->stk[j]) == SK_VIRT;
}

/*  Write every deferred and virtual entry from `from` up, `from` the
 *  stack's bottom or a deferred entry, the head *curp: each deferred node
 *  with its application, each virtual entry a fresh node.  False: SIZE. */
static bool materialize(R *r, size_t from, uint32_t *curp) {
    if (!r->ndstk || r->dstk[r->ndstk - 1].at < from) return true;
    av_arena *a = r->a;
    size_t nv = 0;
    for (size_t j = from; j < r->top; j++) nv += SK_KIND(r->stk[j]) == SK_VIRT;
    AV_ALWAYS(nv <= r->nvirt && a->cap - a->used >= r->nvirt, "virtual roots past the reserve");
    if (a->cap - a->used < nv) return false;        /* the reserve holds them */
    r->nvirt -= nv;
    uint32_t left = *curp;
    size_t k = r->ndstk;
    for (size_t j = r->top; j-- > from;) {
        uint32_t e = r->stk[j], node = SK_BODY(e);
        if (SK_KIND(e) == SK_VIRT) {
            node = reserved_app(a, left, node);
        } else if (SK_KIND(e) == SK_DEFER) {
            assert(k && r->dstk[k - 1].at == j);
            arena_set(a, node, (av_node){ left, r->dstk[--k].arg });
        }
        r->stk[j] = node;
        left = node;
    }
    assert(!k || r->dstk[k - 1].at < from);
    r->ndstk = k;
    return true;
}

/*  Before a contraction whose redex root is entry p: the deferred roots
 *  above it, which it consumes as function parts, written.  False: SIZE. */
static inline bool prepare(R *r, size_t p, uint32_t *curp) {
    if (!r->ndstk || r->dstk[r->ndstk - 1].at <= p) return true;
    size_t i = r->ndstk;
    while (i && r->dstk[i - 1].at > p) i--;
    return materialize(r, r->dstk[i].at, curp);
}

/*  The reduction stops with st: everything deferred written first. */
static av_status stop(R *r, size_t bottom, uint32_t cur, av_status st) {
    return materialize(r, bottom, &cur) ? st : AV_SIZE;
}

/*  The contraction at entry p rewrites its redex root to v, an
 *  indirection or an application; the head becomes the result.  A virtual
 *  root builds no node: an indirection's target is the head, and an
 *  application's argument stays in the entry, its function the head. */
static inline void root_set(R *r, size_t p, av_node v, uint32_t *curp) {
    vpop(r, p + 1);
    if (SK_KIND(r->stk[p]) == SK_VIRT) {
        if (v.l >> AV_TAG_SHIFT == AV_IND) {
            r->nvirt--;
            r->top = p;
            *curp = v.l & AV_PAYLOAD;
        } else {
            r->stk[p] = SK_MAKE(SK_VIRT, v.r);
            r->top = p + 1;
            *curp = v.l;
        }
        return;
    }
    undefer(r, p);
    arena_set(r->a, r->stk[p], v);
    r->top = p;
    *curp = r->stk[p];
}

/*  Room to make entry p head applied to m operands: the stack's entries
 *  and, when p is real, its place among the deferred. */
static bool defer_grow(R *r, size_t p, size_t m) {
    if (p + m > UINT32_MAX || !grow(&r->stk, &r->cap, p + m)) return false;
    if (SK_KIND(r->stk[p]) == SK_REAL && r->ndstk == r->dcap) {
        size_t c = r->dcap ? 2 * r->dcap : 64;
        dentry *d = realloc(r->dstk, c * sizeof *d);
        if (!d) return false;
        r->dstk = d;
        r->dcap = c;
    }
    return true;
}

static inline bool defer_room(R *r, size_t p, size_t m) {
    return (p + m <= r->cap && p + m <= UINT32_MAX &&
            (SK_KIND(r->stk[p]) != SK_REAL || r->ndstk < r->dcap)) ||
           defer_grow(r, p, m);
}

/*  Entry p, a root, takes the argument x, deferred if it was real; its
 *  room made. */
static inline void defer_root(R *r, size_t p, uint32_t x) {
    uint32_t e = r->stk[p];
    if (SK_KIND(e) == SK_VIRT) {
        r->stk[p] = SK_MAKE(SK_VIRT, x);
    } else if (SK_KIND(e) == SK_DEFER) {
        assert(r->ndstk && r->dstk[r->ndstk - 1].at == p);
        r->dstk[r->ndstk - 1].arg = x;
    } else {
        assert(!r->ndstk || r->dstk[r->ndstk - 1].at < p);
        r->dstk[r->ndstk++] = (dentry){ (uint32_t)p, x };
        r->stk[p] = SK_MAKE(SK_DEFER, e);
        /* nothing reads a deferred node before it is written, and its old
         * redex would keep alive what the undeferred reducer lets go.  An
         * application, not an indirection: a collection follows those, and
         * the entry would name the node it pointed to */
        arena_set(r->a, e, (av_node){ AV_NODE_I, AV_NODE_I });
    }
}

/*  Entry p becomes head applied to f[0] .. f[m-1], m >= 1, f[m-1] in entry
 *  p, the rest virtual above it: a real root deferred.  False: out of
 *  memory for the stack, nothing changed. */
static inline bool defer_apply(R *r, size_t p, uint32_t head, const uint32_t *f, unsigned m,
                               uint32_t *curp) {
    if (!defer_room(r, p, m)) return false;
    vpop(r, p + 1);
    defer_root(r, p, f[m - 1]);
    for (unsigned i = 1; i < m; i++) r->stk[p + i] = SK_MAKE(SK_VIRT, f[m - 1 - i]);
    r->nvirt += m - 1;
    r->top = p + m;
    *curp = head;
    return true;
}

#endif
