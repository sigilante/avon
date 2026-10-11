/**  ski.h
 *
 *  The SKI combinator calculus:  leaves (S, K, I and opaque atoms),
 *  their arities, and expressions as trees.
 */

#ifndef SKI_H
#define SKI_H

#include <stdbool.h>
#include <stdint.h>

/*  A leaf.  Ids 0, 1, 2 are the combinators; ids >= SKI_ATOM_FIRST are
 *  inert opaque atoms, which are named in a side table and never
 *  contracted.
 */
typedef uint32_t ski_leaf;

enum {
    SKI_S          = 0,
    SKI_K          = 1,
    SKI_I          = 2,
    SKI_ATOM_FIRST = 3,
};

static inline bool ski_is_comb(ski_leaf x) { return x < SKI_ATOM_FIRST; }

/*  Arguments a leaf needs before it contracts; 0 for an atom, which never
 *  does.
 *
 *      S x y z  ->  x z (y z)
 *      K x y    ->  x
 *      I x      ->  x
 */
static inline unsigned ski_arity(ski_leaf x) {
    switch (x) {
    case SKI_S: return 3;
    case SKI_K: return 2;
    case SKI_I: return 1;
    default:    return 0;
    }
}

/*  An expression as an immutable tree.  Subtrees may be shared, so a
 *  ski_expr graph is a DAG; walks over one must not assume a tree.
 */
typedef struct ski_expr ski_expr;

typedef enum { SKI_LEAF, SKI_APP } ski_kind;

struct ski_expr {
    ski_kind kind;
    union {
        ski_leaf leaf;                              /* SKI_LEAF */
        struct { const ski_expr *fn, *arg; } app;   /* SKI_APP  */
    };
};

#endif /* SKI_H */
