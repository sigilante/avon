/**  avon.h
 *
 *  The runtime's public interface.  Representation follows docs/DESIGN.md
 *  §2; the reducer §3; statuses §3.4.
 */

#ifndef AVON_H
#define AVON_H

#include <signal.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "ski.h"

/*  A node: eight bytes, tag in the top two bits of l.  Nodes are addressed
 *  by 32-bit index into one arena, never by pointer.
 */
typedef struct { uint32_t l, r; } av_node;

#define AV_TAG_SHIFT 30u
#define AV_TAG(n)    ((n).l >> AV_TAG_SHIFT)
#define AV_PAYLOAD   ((1u << AV_TAG_SHIFT) - 1u)

#define AV_APP  0u   /* l = left index,   r = right index            */
#define AV_IND  1u   /* l = target index, r = unused   (share mode)  */
#define AV_LEAF 2u   /* l = tag only,     r = ski_leaf               */
#define AV_JET  3u   /* l = jet id,       r = fallback term index    */

/*  The leaf nodes of S, K, I are interned at indices 0, 1, 2. */
#define AV_NODE_S 0u
#define AV_NODE_K 1u
#define AV_NODE_I 2u

/*  No node: an allocation failure or an absent term. */
#define AV_NONE   UINT32_MAX

/*  The most nodes an arena can hold: indices must fit in 30 bits. */
#define AV_MAX_NODES (1u << AV_TAG_SHIFT)

typedef enum {
    AV_WHNF,
    AV_NORMAL,
    AV_FUEL,
    AV_SIZE,
    AV_INTERRUPTED,
} av_status;

const char *av_status_name(av_status s);

/*  ------------------------------------------------------------------ arena
 *
 *  One flat array of nodes, bump-allocated.  Atoms (leaf ids >= 3) have
 *  names in a side table and one interned leaf node each.  A collection
 *  (§2, stop-and-copy) moves nodes, so an index the caller holds across a
 *  reduction is valid afterwards only if it was registered with
 *  av_root_push.
 */
typedef struct {
    av_node   *nodes;
    uint32_t   used, cap;

    char     **atom_name;   /* by ski_leaf id; NULL for S, K, I     */
    uint32_t  *atom_node;   /* by ski_leaf id: its interned leaf     */
    uint32_t   n_leaves, leaf_cap;

    uint32_t **roots;       /* addresses of indices held by callers  */
    uint32_t   n_roots, root_cap;

    uint64_t   collections;
    bool       allow_bird_atoms;   /* §4.3: off unless asked for */
} av_arena;

av_arena *av_arena_new(uint32_t cap);
void      av_arena_free(av_arena *a);

/*  Allocate an application, growing the arena if it is full.  Returns
 *  AV_NONE if memory or index space runs out.  Never collects.
 */
uint32_t  av_app(av_arena *a, uint32_t f, uint32_t x);

/*  Grow the arena until k more nodes fit.  False if they cannot. */
bool      av_reserve(av_arena *a, uint32_t k);

/*  The interned leaf node for a name: S, K, I, or an opaque atom. */
uint32_t  av_leaf(av_arena *a, const char *name, size_t len);

const char *av_leaf_name(const av_arena *a, ski_leaf id);

void av_root_push(av_arena *a, uint32_t *idx);
void av_root_pop(av_arena *a);

static inline uint32_t av_tag(const av_arena *a, uint32_t i) {
    return a->nodes[i].l >> AV_TAG_SHIFT;
}
static inline uint32_t av_left(const av_arena *a, uint32_t i) {
    return a->nodes[i].l & AV_PAYLOAD;
}
static inline uint32_t av_right(const av_arena *a, uint32_t i) {
    return a->nodes[i].r;
}

/*  Follow indirections to the node they stand for. */
static inline uint32_t av_res(const av_arena *a, uint32_t i) {
    while (av_tag(a, i) == AV_IND) i = av_left(a, i);
    return i;
}

/*  ----------------------------------------------------------------- collect
 *
 *  Copy everything reachable from the roots into a fresh array, short-
 *  circuiting indirections, and free the old one.  The caller's roots
 *  function evacuates each index it holds with av_gc_evac.  Afterwards at
 *  least `need` nodes are free, growing the arena if the live set is more
 *  than half of it.  Returns false if that cannot be met.
 */
typedef struct av_gc av_gc;
typedef void (*av_roots_fn)(av_gc *g, void *ctx);

uint32_t av_gc_evac(av_gc *g, uint32_t i);

/*  After the scan, where a from-space node went, or AV_NONE if it died.
 *  For the `after` hook, which remaps side tables keyed by node index.
 */
uint32_t av_gc_forwarded(const av_gc *g, uint32_t i);

bool     av_collect(av_arena *a, uint32_t need, av_roots_fn roots,
                    av_roots_fn after, void *ctx);

/*  --------------------------------------------------------------- terms I/O
 *
 *  The printed form of aviary_kernel.terms.pretty: left-associative
 *  juxtaposition, parentheses only around an application in argument
 *  position.  Names are runs of characters other than space and parens.
 */
typedef struct { char *s; size_t len, cap; } av_buf;

void av_buf_free(av_buf *b);

typedef struct { size_t pos; const char *msg; } av_parse_error;

/*  Parse a whole term.  Returns its root, or AV_NONE with *err filled.
 *  A NUL byte anywhere is an error: atom names are C strings.  An atom
 *  named like one of the reference host's live combinators is an error
 *  unless a->allow_bird_atoms (§4.3).  An atom name may not begin with "@",
 *  reserved for probe markers, or contain "`", which marks the prefix form.
 */
uint32_t av_parse(av_arena *a, const char *src, size_t len,
                  av_parse_error *err);

/*  Append the printed form of a term to b, visiting at most `budget`
 *  nodes of its tree unfolding.  Returns false, leaving b holding a
 *  prefix, if the budget runs out: a reduced state's unfolding can be
 *  exponential in its size (§4.1).
 */
bool av_print(const av_arena *a, uint32_t t, size_t budget, av_buf *b);

/*  ------------------------------------------------------------ hygiene
 *
 *  True if aviary_kernel 0.1.0 would contract an atom of this name: one of
 *  its 52 live combinators other than S, K, I.  Avon holds such atoms
 *  inert, so a term carrying one would diverge from the oracle (§4.3).
 */
bool av_is_bird(const char *name, size_t len);

/*  -------------------------------------------------------------- sha-256 */

typedef struct { uint32_t h[8]; uint64_t len; uint8_t buf[64]; size_t fill; } av_sha256_ctx;

void av_sha256_init(av_sha256_ctx *s);
void av_sha256_update(av_sha256_ctx *s, const void *data, size_t n);
void av_sha256_final(av_sha256_ctx *s, uint8_t out[32]);
void av_sha256(const void *data, size_t n, uint8_t out[32]);

/*  ---------------------------------------------------------- wire format
 *
 *  A term at rest is a container (docs/DESIGN.md §4.2):
 *
 *      "SKIT"  u8 version = 1  u8[3] zero
 *      u32 atom count n, then n atoms, each u32 length and its bytes
 *      u64 bit count, then the bitstring, zero-padded to a whole byte
 *
 *  Integers are little-endian.  The bitstring is Tromp's encoding with a
 *  third leaf, bits packed least significant first, codes read first bit
 *  first:
 *
 *      00  S        01  K        11  application: function, then argument
 *      10  I or an atom, followed by w bits (least significant first),
 *          w the bit length of n: 0 is I, k is the k-th atom of the table
 *
 *  With no atoms w is 0 and the code is exactly 00 / 01 / 10 / 11.  The
 *  bitstring does not preserve sharing: jam walks the tree unfolding under
 *  a node budget, as the printer does.  Atoms are tabled in the order the
 *  walk first meets them, so jam is a function of the term.
 */
bool     av_jam(const av_arena *a, uint32_t t, size_t budget, av_buf *out,
                const char **err);

/*  Decode a container.  Never trusts its input: every length, index,
 *  and bit is checked, and anything malformed or non-canonical (padding
 *  not zero, bytes past the end, an atom table with a duplicate, S, K, I,
 *  or an empty name) returns AV_NONE with *err set.
 */
uint32_t av_cue(av_arena *a, const uint8_t *p, size_t n, const char **err);

/*  ------------------------------------------------------------- snapshots
 *
 *  An arena image, preserving sharing (§4.2, §19).  Save collects first,
 *  so the image holds the live graph only, and updates *root.  It writes
 *  the image, syncs it, then writes the sidecar PATH.sum -- the root, the
 *  node count, and the SHA-256 of image and root -- and syncs that, each
 *  through a temporary file and a rename.  Load verifies the checksum
 *  before reading anything else, then every node: tags, indices, interned
 *  leaves, and that the graph is acyclic.
 */
bool     av_snapshot_save(av_arena *a, uint32_t *root, const char *path,
                          const char **err);
av_arena *av_snapshot_load(const char *path, uint32_t *root, const char **err);

/*  ----------------------------------------------------------------- reduce */

typedef enum {
    AV_COPY,    /* no update in place: the reference host's counts (§1.1) */
    AV_SHARE,   /* update in place: same values, fewer contractions      */
} av_strategy;

typedef struct {
    av_strategy strategy;
    bool        whnf_only;      /* stop at weak head normal form        */
    uint64_t    max_steps;      /* fuel, checked before each attempt    */
    uint32_t    max_nodes;      /* live nodes after a collection        */
    volatile sig_atomic_t *interrupt;   /* polled with fuel; may be NULL */
    bool        no_collect;     /* grow instead of collecting, so every
                                   index the caller holds stays valid */
} av_opts;

typedef struct {
    uint32_t  term;     /* the state reached: the value, or where it stopped */
    uint64_t  steps;    /* host contractions                               */
    av_status status;
} av_result;

av_opts   av_opts_default(void);

/*  Reduce `t` under normal order.  May collect: see av_root_push. */
av_result av_reduce(av_arena *a, uint32_t t, const av_opts *o);

/*  ---------------------------------------------------------------- probing
 *
 *  Reading a value by running it, never by reading its syntax (docs/
 *  DESIGN.md §0, python/skijack/run.py): a Scott datum of an n-constructor
 *  type, applied to n fresh marker atoms and reduced to weak head normal
 *  form, returns the marker of its own constructor applied to its fields.
 *  Markers are atoms named "@" and a number.  The parser, cue and the
 *  snapshot loader refuse any atom name beginning with "@", so a loaded
 *  term cannot carry one; a caller building atoms with av_leaf must not
 *  either.
 *  Probes reduce with the caller's options but never collect, so the
 *  fields and memo keys they hand back stay valid.
 */
#define AV_PEEL_MAX 8

typedef struct {
    unsigned ctor;                      /* index in declaration order */
    unsigned nfields;
    uint32_t field[AV_PEEL_MAX];
} av_peeled;

/*  Which of nctors constructors t is, and its fields.  False, with *err
 *  set, if probing does not reach weak head normal form or the head is not
 *  one of the markers.
 */
bool av_peel(av_arena *a, uint32_t t, unsigned nctors, const av_opts *o,
             av_peeled *out, const char **err);

/*  Decode a quoted datum of an object type -- nctors constructors, names
 *  in declaration order, app_ctor the application constructor -- into a
 *  term whose leaves are the constructor names, for printing.  Memoized by
 *  node, and at most max_probes probes.
 */
uint32_t av_decode(av_arena *a, uint32_t datum, unsigned nctors,
                   const char *const *names, unsigned app_ctor,
                   size_t max_probes, const av_opts *o, const char **err);

/*  Read a Scott numeral: zero z s = z, suc n z s = s n. */
bool av_read_nat(av_arena *a, uint32_t t, size_t max_depth, const av_opts *o,
                 uint64_t *n, const char **err);

/*  ---------------------------------------------------------------- witness
 *
 *  The witness strategy (docs/DESIGN.md §17): lean-ski's heap machine,
 *  Air.stepG, run literally over its own append-only heap of the circuit's
 *  cells.  Its contraction count equals copy mode's, and its table is the
 *  one Ski/AirCheck.lean decides and bench/plonky3 proves.  Weak head normal
 *  form only.  Terms with atoms are refused for now (§17.3).
 */

/*  Cell tags, numbered as the Plonky3 tables' mem bus numbers them. */
enum {
    AV_CELL_S = 0, AV_CELL_K = 1, AV_CELL_I = 2, AV_CELL_APP = 3,
    AV_CELL_NIL = 4, AV_CELL_CONS = 5, AV_CELL_ATOM = 6,
};

typedef struct { uint32_t tag, a, b; } av_cell;   /* A f x, C x r */
typedef struct { uint32_t hd, stk, ctr; } av_row;

typedef struct {
    av_cell  *mem;              /* the heap: loaded, then every write */
    size_t    nmem, memcap;
    av_row   *rows;             /* one per state, the halted one last */
    size_t    nrows, rowcap;
    size_t    loaded;           /* cells of Mach.load t, the nil included */
    uint32_t  hd0, stk0;
    uint64_t  contractions;     /* rows whose head is not an application */
} av_witness;

/*  Load t and run it to weak head normal form.  AV_WHNF on success;
 *  AV_SIZE, with *err, if it needs more than max_rows rows or max_cells
 *  cells, or holds atoms or jets.  A diverging term stops at max_rows.
 */
av_status av_witness_run(const av_arena *a, uint32_t t, size_t max_rows,
                         size_t max_cells, av_witness *w, const char **err);
void      av_witness_free(av_witness *w);

/*  The table in Ski/AirCheck.lean's format: the term in prefix form (`
 *  for application), the memory table, the rows.  Both are padded to a
 *  power of two at least 2^min_log, rows by repeating the halted row and
 *  memory with nil cells, as bench/plonky3's table_of pads them (min_log
 *  4 there).
 */
bool av_witness_table(const av_arena *a, uint32_t t, const av_witness *w,
                      unsigned min_log, av_buf *out);

/*  A closed {S,K,I} term in prefix form, under a node budget. */
bool av_prefix(const av_arena *a, uint32_t t, size_t budget, av_buf *out);

/*  Parse the prefix form: S, K, I, and ` before an application's function
 *  and argument, surrounding whitespace allowed.  AV_NONE on anything else.
 */
uint32_t av_parse_prefix(av_arena *a, const char *src, size_t len,
                         const char **err);

#endif /* AVON_H */
