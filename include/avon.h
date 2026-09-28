/**  avon.h
 *
 *  The runtime's public interface.  Representation follows docs/DESIGN.md
 *  §2; statuses follow §3.4.
 */

#ifndef AVON_H
#define AVON_H

#include <stdint.h>

#include "ski.h"

/*  A node: eight bytes, tag in the top two bits of l.  Nodes are addressed
 *  by 32-bit index into one arena, never by pointer.
 */
typedef struct { uint32_t l, r; } av_node;

#define AV_TAG_SHIFT 30u
#define AV_TAG(n)    ((n).l >> AV_TAG_SHIFT)

#define AV_APP  0u   /* l = left index,   r = right index            */
#define AV_IND  1u   /* l = target index, r = unused   (share mode)  */
#define AV_LEAF 2u   /* l = tag only,     r = ski_leaf               */
#define AV_JET  3u   /* l = jet id,       r = fallback term index    */

/*  The leaf nodes of S, K, I are interned at indices 0, 1, 2. */
#define AV_NODE_S 0u
#define AV_NODE_K 1u
#define AV_NODE_I 2u

typedef enum {
    AV_WHNF,
    AV_NORMAL,
    AV_FUEL,
    AV_SIZE,
    AV_INTERRUPTED,
} av_status;

#endif /* AVON_H */
