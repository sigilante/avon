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
#include <stdio.h>

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

/*  A jet node's id field: the jet id, and whether its term is the
 *  dashboard's (shared, never to be written) or its own (docs/DESIGN.md
 *  §6.5: share mode writes only nodes its run created). */
#define AV_JET_SHARED (1u << 29)

/*  A word (docs/DESIGN.md §6.10) is a jet node too, flagged here, and seen
 *  through by av_view like any jet node: W n, the numeral n >= 1 held as a
 *  number, its term SUC (W (n-1)), W 0 being K, so the predecessor is
 *  always its term's right child.  The id field of a word holds n; of any
 *  other jet node, the jet id. */
#define AV_JET_WORD   (1u << 28)
#define AV_JET_ID(l)  ((l) & (AV_JET_WORD - 1))
#define AV_WORD_MAX   (AV_JET_WORD - 1u)

/*  The most arguments a residual jet takes (§6.5).  Joy's words are
 *  constructors of a 12-way sum; Lit and Quote carry a field, so take 13. */
#define AV_JET_ARITY_MAX 32u

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
 *  av_root_push.  A root may hold AV_NONE, and a collection leaves it so.
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

    struct av_jet *jets;        /* the dashboard (§6): its terms are roots */
    uint32_t   njets, jetcap;
    uint32_t  *jet_index;       /* open addressing, hash -> jet id */
    uint32_t   jet_index_cap;
    uint32_t   jet_mark[AV_JET_ARITY_MAX];  /* residuals' atoms: @x0 .. */
    uint32_t  *jet_scratch;     /* an instance's intermediate results    */
    uint32_t   jet_scratch_cap;
    bool       jet_scratch_busy;   /* instances do not nest */

    struct av_active *active;   /* reductions in progress, innermost first */
    struct av_interp *interps;  /* interpreter jets (§7) */
    uint32_t   ninterps;
    uint64_t   probe_steps;     /* contractions probes have spent, all told */
    uint32_t  *nats;            /* known numerals: zero, suc pairs: roots  */
    uint32_t   nnats;
    const struct av_facts *facts;   /* the store resolvers here read (§8) */
    struct av_jetstats *jetstats;   /* set while a reduction counting jets
                                       runs, for the jet-node makers */
    struct av_tmpl *tmpls;      /* supercombinator templates (§6.9)       */
    uint32_t   ntmpls, tmplcap;
    uint32_t  *tmpl_globals;    /* their bodies' closed parts: roots      */
    uint32_t   nglobals, globcap;
    uint32_t  *tmpl_scratch;    /* an instance's intermediate results    */
    uint32_t   tmpl_scratch_cap;
    uint32_t   compiler[9];     /* the compiler jet's terms (§20.3), roots:
                                   abs, TS TK TI TV TA, Ap, Zero Suc; 0 none */
    uint32_t   word_suc;        /* words' successor term (§6.10), a root;
                                   0 while words are off                  */
    bool       fix_on;          /* Y unfolds in one step (§6.11): the next
                                   template load registers it             */
    struct av_pma *pma;         /* the persistent image (§19.1), or NULL  */
    uint64_t   lookups;         /* scries answered natively from it      */
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

/*  Register *idx as a root: a collection updates it in place.  Aborts the
 *  process if the root stack cannot grow -- a lost root would corrupt the
 *  heap silently.  Pop in reverse order. */
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

/*  A word (§6.10), and its value; a numeral held natively: K is 0. */
static inline bool av_is_word(const av_arena *a, uint32_t i) {
    return av_tag(a, i) == AV_JET && (a->nodes[i].l & AV_JET_WORD);
}
static inline uint32_t av_word_value(const av_arena *a, uint32_t i) {
    return a->nodes[i].l & AV_WORD_MAX;
}
static inline bool av_numeral(const av_arena *a, uint32_t i, uint32_t *n) {
    i = av_res(a, i);
    if (i == AV_NODE_K) { *n = 0; return true; }
    if (av_is_word(a, i)) { *n = av_word_value(a, i); return true; }
    return false;
}

/*  Follow indirections and jet wrappers: the term a node denotes.  Every
 *  reader but the reducers sees a jet node as the term it stands for.
 */
static inline uint32_t av_view(const av_arena *a, uint32_t i) {
    for (;;) {
        uint32_t tag = av_tag(a, i);
        if (tag == AV_IND) i = av_left(a, i);
        else if (tag == AV_JET) i = av_right(a, i);
        else return i;
    }
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

/*  A reduction in progress registers its roots, so a reduction nested in
 *  another -- a probe, or an interpreter jet's object run -- may collect
 *  without invalidating the outer one's indices.  av_collect evacuates
 *  every registered reduction's roots, and runs every `after` hook. */
typedef struct av_active {
    av_roots_fn        roots, after;
    void              *ctx;
    struct av_active  *next;
} av_active;

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
 *  An image of one term's graph, preserving sharing (§4.2, §19).  Save
 *  copies the graph below root out of the live arena, which it does not
 *  change -- indirections resolved, jet nodes seen through, and nothing
 *  else, so neither the caller's other terms nor the jet dashboard (never
 *  persisted, §19) reach the image -- and refuses a graph that carries a
 *  probe marker.  It writes the image, syncs it, then writes the sidecar
 *  PATH.sum -- the root, the node count, and the SHA-256 of image and root
 *  -- and syncs that, each through a temporary file and a rename.  Load
 *  verifies the checksum before reading anything else, then every node:
 *  tags, indices, interned leaves, no marker pointed at, and no cycle.
 */
bool     av_snapshot_save(const av_arena *a, uint32_t root, const char *path,
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
    bool        jets;           /* fire residual jets (§6.5); off, a jet
                                   node is only the term it stands for */
    bool        interp_jets;    /* fire interpreter jets (§7): these
                                   change counts, so off by default */
    bool        install_jets;   /* fire the unquoter's jet (§20.2):
                                   it changes counts too; off by default */
    bool        compile_jets;   /* fire the compiler jet (§20.3): it
                                   changes counts too; off by default */
    uint64_t    jet_check;      /* check every Nth fire against the
                                   unjetted run (§6.6); 0 never */
    struct av_census *census;   /* copy mode: record calls; NULL off */
    struct av_trace *trace;     /* copy mode: observe the head run (§22);
                                   NULL off                               */
    struct av_profile *profile; /* share mode: charge each contraction to
                                   a named term (§6.7); NULL off */
    struct av_jetstats *jetstats;   /* count each jet's fires, misses and
                                   demotions, and each fire's origin
                                   (§6.7); NULL off */
    bool        templates;      /* share mode: instantiate supercombinator
                                   templates (§6.9); copy mode ignores it */
    bool        data;           /* share mode: data jets (§6.10), numeral
                                   operations on words and constructor
                                   dispatch; copy mode ignores it         */
    bool        fix;            /* share mode: Y g unfolds to g (Y g) in
                                   one step (§6.11); copy mode ignores it */
    bool        fix_shared;     /* with fix: every unfolding of a g passes
                                   on one Y g, never written (§6.11,
                                   "Shared"): less memory, not less time  */
    bool        p2;             /* share mode: P applied to a state of
                                   sixteen 31-bit elements runs natively,
                                   one step (§6.12); copy mode ignores it */
    bool        no_join;        /* with data: never join a case to its
                                   instance (§6.10), for tests comparing
                                   the two; every count is the same       */
    bool        no_defer;       /* with templates: write every instance's
                                   root and spine at once (§6.13), for
                                   tests comparing the two; every count
                                   and state is the same                  */
} av_opts;

typedef struct {
    uint32_t  term;     /* the state reached: the value, or where it stopped */
    uint64_t  steps;    /* host contractions, a jet's charge included       */
    av_status status;
    uint64_t  jet_calls;    /* jets fired, reported beside steps (§6.5)   */
    uint64_t  interp_calls; /* interpreter jets fired, among jet_calls    */
    uint64_t  jet_steps;    /* contractions the fires charged, among steps */
    bool      jet_fault;    /* a jet check disagreed: status INTERRUPTED  */
    uint64_t  tmpl_calls;   /* template instantiations, one step each,
                               among steps (§6.9)                         */
    uint64_t  dispatches;   /* data jets (§6.10): a word or a constructor
                               template meeting its continuations, one
                               step each, among steps                     */
    uint64_t  fused;        /* dispatches that instantiated the branch's
                               template in the same step, among them      */
    uint64_t  word_ops;     /* numeral operations run on words, one step
                               each, among steps                          */
    uint64_t  fix_calls;    /* Y unfolded (§6.11), one step each, among
                               steps                                      */
    uint64_t  joins;        /* cases joined to their instances (§6.10):
                               an instantiation and the dispatch after
                               it, two steps each, among steps            */
    uint64_t  p2_calls;     /* P run natively (§6.12), one step each,
                               among steps                                */
    uint64_t  p2_declines;  /* P met an argument neither a state as it
                               stands nor a chain of P calls ending in
                               one, and ran a fresh copy of its term      */
    uint64_t  p2_unbound;   /* jet nodes whose term was not P's at a fire
                               or a decline, made indirections            */
    uint64_t  deferred;     /* instances whose root and spine were left in
                               the stack (§6.13), among tmpl_calls and
                               fused                                      */
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
 *  Markers are atoms named "@" and a number.  The parser and cue refuse
 *  any atom name beginning with "@", so a term read from outside cannot
 *  carry one; a caller building atoms with av_leaf must not either.  A
 *  snapshot may hold such leaves -- an arena that has probed or loaded
 *  jets interns them -- but the loader refuses an image in which any node
 *  or the root points at one.
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
    uint64_t  pops, wcells;     /* instantiations' argument pops and written
                                   cells: POP's and INSTW's rows */
    uint64_t  p2calls;          /* Poseidon2 jet steps: P2's rows, and 496
                                   rows each of P2IN and P2OUT */
} av_witness;

/*  Load t and run it to weak head normal form.  AV_WHNF on success;
 *  AV_SIZE, with *err, if it needs more than max_rows rows or max_cells
 *  cells, or holds atoms or jets.  A diverging term stops at max_rows.
 */
av_status av_witness_run(const av_arena *a, uint32_t t, size_t max_rows,
                         size_t max_cells, av_witness *w, const char **err);
void      av_witness_free(av_witness *w);

/*  -------------------------------------------------------- jetted witness
 *
 *  lean-ski's jet table for a term (`lake exe jets emit`, its
 *  JetTable.jetTable): licensed roots, addresses in the loaded heap, each
 *  naming a jet; and each jet's arity, root operand and body cells in
 *  ibuild order.  An operand is a cell the instantiation wrote (local, by
 *  offset), an argument (by index) or a public cell (global, by address).
 *  Nothing here is trusted: lean-ski's `lake exe jets check` checks the
 *  table a jetted witness writes against Air.AcceptsJ, recomputing the
 *  roots from the term.
 */

enum { AV_JOP_LOCAL = 0, AV_JOP_ARG = 1, AV_JOP_GLOBAL = 2 };

typedef struct { uint32_t kind, val; } av_jop;
typedef struct { uint32_t tag; av_jop a, b; } av_jcell;   /* tag 0..3 */
typedef struct {
    uint32_t  k;                /* arity */
    av_jop    root;
    av_jcell *cells;
    size_t    ncells;
} av_tjet;
typedef struct {
    uint32_t *root_addr, *root_jet;
    size_t    nroots;
    av_tjet  *jets;
    size_t    njets;
} av_jettable;

/*  Read a jet file (`roots R`, R lines `addr jet`, `jets G`, per jet a line
 *  `k n root` and n cell lines `tag` or `3 a b`, an operand `L j`, `A i` or
 *  `G a`).  False, with *err, on anything malformed or out of range.
 */
bool av_jettable_read(const char *src, size_t len, av_jettable *jt, const char **err);
void av_jettable_free(av_jettable *jt);

/*  av_witness_run, jetted: at a licensed root with at least k arguments on
 *  the stack, one row instantiates the jet (lean-ski's Mach.instStepG: pop
 *  k argument pointers, write the body's cells at the counter, the head
 *  the body's root, the stack the rest); otherwise a row is a machine
 *  transition.  That is lean-ski's policy (bench/JetCost.lean runJ,
 *  bench/plonky3/src/jets.rs run_jets), so the table is the one its prover
 *  writes.  *insts counts the instantiations; `contractions` counts the
 *  machine's contractions only.  jt NULL is av_witness_run.
 */
av_status av_witness_run_jets(const av_arena *a, uint32_t t, const av_jettable *jt,
                              size_t max_rows, size_t max_cells, av_witness *w,
                              uint64_t *insts, const char **err);

/*  -------------------------------------------------------- probe segments
 *
 *  lean-ski's output bound (Ski/AirProbe.lean, Air.AcceptsP): a jetted run
 *  proves a term halts; probe segments prove what it halts to.  A plan
 *  (`lake exe jets plan OUTCOME`) has one segment per constructor of the
 *  outcome, depth first.  Each segment probes a pointer -- the loaded
 *  head, or a field its parent popped -- by writing k fresh markers and a
 *  stack of them, running jetted to a halt, and requiring the marker
 *  ctor + base at the head over exactly `arity` fields.
 */
typedef struct { uint32_t base, k, ctor, arity, parent, field; } av_seg;
typedef struct { av_seg *segs; size_t n; } av_plan;

/*  Read `plan n` and n lines `base k ctor arity parent field`.  False,
 *  with *err, on anything malformed or of a shape Air.planOf never gives:
 *  each segment's markers follow the last's, from 0; ctor < k; segment 0
 *  has parent 0, field 0, and every other reads a field of an earlier
 *  one; each field is read exactly once, so n - 1 in all; the last
 *  segment has none. */
bool av_plan_read(const char *src, size_t len, av_plan *p, const char **err);
void av_plan_free(av_plan *p);

/*  What a probe run adds to its witness: each segment's probe row, and
 *  the pointers each segment's end popped, top first. */
typedef struct {
    char      why[160];         /* a failure's message, which *err names */
    uint32_t *starts;           /* n: the probe rows' indices */
    uint32_t *fields;           /* every segment's fields, in order */
    size_t   *field_off;        /* n + 1: segment j's fields are
                                   fields[field_off[j] .. field_off[j+1]) */
    size_t    n;
} av_probe;

/*  The probe run (bench/plonky3's run_probe): from the loaded term, per
 *  segment a probe row, the markers, and a jetted run to a halt with every
 *  row but the halted one; then the final state as the last row.  AV_WHNF
 *  on success; AV_INTERRUPTED, with *err naming the segment, when one ends
 *  anywhere but its marker over exactly its fields -- for a plan from
 *  `jets plan` and a licensed jet table, the term does not decode to the
 *  plan's outcome; AV_SIZE on a budget or a malformed plan.  *err may
 *  point into pr, valid until av_probe_free.  An accepted table's meaning
 *  is lean-ski's check-probe's (Air.checkPA_decodes), not Avon's exit.
 */
av_status av_witness_run_probe(const av_arena *a, uint32_t t, const av_jettable *jt,
                               const av_plan *plan, size_t max_rows, size_t max_cells,
                               av_witness *w, av_probe *pr, uint64_t *insts,
                               const char **err);
void      av_probe_free(av_probe *pr);

/*  The probe sections after av_witness_table's: `starts n+1`, each
 *  segment's probe row then the padded table's last row; `fields n`, per
 *  segment its count and pointers.  min_log as the table's. */
bool av_probe_table(const av_witness *w, const av_probe *pr, unsigned min_log,
                    av_buf *out);

/*  ------------------------------------------- composed statements, jetted
 *
 *  lean-ski's composed statement (`public.txt`, ComposedText.publicTextC):
 *  a header line, the region size, the log heights, the bit count, the
 *  segments' roots, the nil, the registers, and the composed machine's
 *  heap with its private cells -- the bits at 3 and the region after them
 *  -- blank (`W`).  A statement for the circuit with jets
 *  (docs/ZK-JETS.md, milestone 8) names four log heights, `log R M Lp Li`:
 *  the CPU's, the memory's, POP's and INSTW's, its public budgets.  Avon
 *  decides nothing here: lean-ski's `composed statement-jets` checks the
 *  statement, `composed check-cj` the table.
 */
typedef struct {
    char     *header;           /* the first line, as written */
    uint32_t  w, nbits;
    unsigned  log_rows, log_mem;
    unsigned  log_pop, log_instw;   /* 0: the statement names no budgets */
    bool      p2;               /* a `p2pre h J ROOT` statement: the Poseidon2
                                   jet at the atom J, the comb's root ROOT */
    uint32_t  p2_j, p2_root;
    unsigned  log_pin, log_pout, log_p2;   /* its jet tables' budgets */
    uint32_t *roots;
    size_t    nroots;
    uint32_t  nil, hd0, stk0, ctr0;
    av_cell  *cells;            /* ctr0 cells; the private ones are nil */
} av_cstmt;

/*  Read a statement, as bench/plonky3's parse_public does: every log
 *  height in [8, 20], a two-height line only when it is not the default
 *  (11, 11), and exactly the cells [3, 3 + nbits + w) blank.  False, with
 *  *err, otherwise. */
bool av_cstmt_read(const char *src, size_t len, av_cstmt *s, const char **err);
void av_cstmt_free(av_cstmt *s);

/*  Read a witness for s: nbits + w nonempty lines, the bits `1` (K) or `0`
 *  (A 0 1) or any cell, then the region's cells, into priv (nbits + w
 *  cells).  False, with *err, on anything malformed. */
bool av_cwitness_read(const char *src, size_t len, const av_cstmt *s, av_cell *priv,
                      const char **err);

/*  The composed machine with jets (bench/plonky3's compj run): the
 *  statement's heap with the private cells filled in, then per root a
 *  jetted run from the root over the nil to a halt, the next segment
 *  starting on the row after.  Each segment must halt at K over a nil.
 *  *ends gets the halted rows' indices (nroots of them, malloc'd).  AV_WHNF
 *  on success; AV_INTERRUPTED, with *err, when a segment halts elsewhere
 *  (the witness does not satisfy the statement); AV_SIZE, with *err, on a
 *  budget: the statement's 2^R rows, 2^M cells, 2^Lp pops, 2^Li written
 *  cells, or a statement with no budgets. */
av_status av_witness_run_composed(const av_cstmt *s, const av_cell *priv, const av_jettable *jt,
                                  av_witness *w, size_t **ends, uint64_t *insts,
                                  const char **err);

/*  The composed machine with the Poseidon2 jet (bench/plonky3's compp
 *  run, lean-ski's P2Jet.p2Row): as av_witness_run_composed with no code
 *  jets, and at the atom J, with k and the comb's root on the stack, the
 *  slots in place and each bit's slot K or A 0 1, the jet's step: the
 *  sixteen 31-bit elements of the slots' bits permuted (av_p2_permute),
 *  the outputs' 496 bits pushed for k as stack cells pointing at the K
 *  slot (0) or the K I slot (2).  Budgets: the statement's 2^R rows, 2^M
 *  cells, 496 jet bits per call within 2^Lin and 2^Lout, calls within
 *  2^L2.  Returns as av_witness_run_composed. */
av_status av_witness_run_p2(const av_cstmt *s, const av_cell *priv, av_witness *w, size_t **ends,
                            const char **err);

/*  Poseidon2 over BabyBear, width 16, as lean-ski's Ski/ZK/Poseidon2.lean
 *  specifies it: C printed by lean/P2Prog.lean, which proves it equal to
 *  the specification on every state of sixteen uint32_t values
 *  (AvonP2.permuteC).  The self-test checks the specification's three test
 *  vectors. */
void av_p2_permute(uint32_t s[16]);
bool av_p2_selftest(void);

/*  The Poseidon2 jet (docs/DESIGN.md §6.12).  lean-ski's term P
 *  (Ski/ZK/Poseidon2SKI.lean, printed by `lake exe p2run`) takes a state
 *  `stateN vs` -- sixteen 31-bit elements, each `bitsT 31 v`, least
 *  significant bit first, in pairs `pairT a b = S (S I (K a)) (K b)`, a
 *  bit K (1) or K I (0), each list ending in K -- to `stateN (permute vs)`
 *  (P_specN).  av_p2_register makes p a dashboard entry with the p2 flag,
 *  refusing p unless its full digest (av_p2_digest: §5's Merkle hash with
 *  every digest kept whole, 256 bits, over S, K and I) is P's,
 *  AV_P2_SHA256, pinned here;
 *  then, after av_jets_match, av_p2_bind keeps a jet node for it only
 *  where its term is p's, node for node, and makes every other one an
 *  indirection.  With av_opts.p2, share mode rewrites P at the head with
 *  an argument that is such a state, as it stands, to the permuted state,
 *  one step; over a chain P (P … x) ending in one, it fires the innermost
 *  call first, in place.  Any other argument runs a fresh copy of P's
 *  term, a decline counted, so the node's own term is never written.  At
 *  every fire and decline the jet node's term is checked against p's
 *  again, so a jet node made after the bind is held to it too.  av_p2_state_read reads a state through
 *  indirections and jet nodes: false unless t is one. */
#define AV_P2_DIGEST "skijack-1:43f97c21e068ebe7"   /* lean-ski's Poseidon2SKI.P, §5 */
#define AV_P2_SHA256 "391f7d9a5ad5e744711e18be27b9952a1bb802f8243672552fab4b2e870405b3"
bool     av_p2_digest(const av_arena *a, uint32_t t, char out[65]);
uint32_t av_p2_register(av_arena *a, uint32_t p, const char **err);
long     av_p2_bind(av_arena *a, uint32_t t, uint32_t id);   /* jet nodes kept, or -1 */
bool     av_p2_state_read(const av_arena *a, uint32_t t, uint32_t s[16]);

/*  The table in lean-ski's `composed check-cj` format, as bench/plonky3's
 *  compj-prove writes it: the header, `W w`, the memory padded with nil
 *  cells to 2^M, `ends n` and the segments' ends -- the restarts, then the
 *  padded table's last row -- and the rows padded to 2^R by repeating the
 *  last.  The statement's heights, not the run's: they are its public
 *  budgets (docs/DESIGN.md §17.2). */
bool av_composed_table(const av_cstmt *s, const av_witness *w, const size_t *ends,
                       av_buf *out);

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
/*  The DAG form, `dag <id>=<rhs> ... @<root>` on one line (docs/RUNTIME.md,
 *  "Frame traces"): AV_NONE with *msg on anything malformed. */
uint32_t av_parse_dag(av_arena *a, const char *src, size_t len, const char **msg);

uint32_t av_parse_prefix(av_arena *a, const char *src, size_t len,
                         const char **err);

/*  ------------------------------------------------------ structural hash
 *
 *  skijack's dictionary hash (python/skijack/dictionary.py, docs/DESIGN.md
 *  §5): a Merkle hash over the tree, a leaf hashing its name and an
 *  application "(" + h(fn) + " " + h(arg) + ")", each SHA-256 truncated to
 *  16 hex digits, published as "skijack-1:" and the digits.  For dispatch,
 *  never for commitment.  A digest is the hash's first 8 bytes.
 */
#define AV_HASH_VERSION "skijack-1"

/*  The published hash, "skijack-1:" and 16 hex digits, into out[27]. */
bool av_structural_hash(const av_arena *a, uint32_t t, char out[27]);

/*  Parse a published hash back to its digest. */
bool av_hash_parse(const char *s, uint64_t *digest);

/*  --------------------------------------------------------------- jets
 *
 *  The dashboard (docs/DESIGN.md §6): digest -> jet.  A jet is a residual
 *  jet (§6.5): its term g is reduced in copy mode, jets off, applied to k
 *  fresh atoms, until an atom reaches the head or the run halts; the
 *  state reached is the residual and the contractions its cost.  k is the
 *  least in 1..AV_JET_ARITY_MAX for which an atom reaches the head -- the
 *  genericity
 *  argument of §6.5 holds for any k, so this is a choice of how much work
 *  one fire does, not of correctness.  A jet fires when its node is at the
 *  head with at least k arguments and the fuel left covers the cost: the
 *  residual is instantiated over the arguments and the cost charged, so a
 *  copy-mode count is the unjetted count, contraction for contraction.
 */
/*  A Scott constructor (docs/DESIGN.md §6.8): the term takes `fields`
 *  fields, then `count` continuations, and applies continuation `index` to
 *  the fields, in order: C a1 .. af k0 .. k(n-1) = k_index a1 .. af.  K is
 *  (0, 0, 2), K I (0, 1, 2), T (1, 0, 1), V (2, 0, 1).  count 0: not one.
 */
typedef struct { unsigned fields, index, count; } av_ctor;

static inline bool av_ctor_is(av_ctor c) { return c.count != 0; }

typedef struct av_jet {
    uint64_t  digest;
    uint32_t  fallback;         /* the term g, its inner jets wrapped      */
    uint32_t  residual;         /* over jet_mark[0 .. arity-1]             */
    unsigned  arity;
    uint64_t  cost;             /* copy-mode contractions a fire replaces  */
    uint32_t  nodes;            /* nodes an instance allocates, at most    */
    uint32_t  term_nodes;       /* nodes a private copy of the term takes  */
    size_t    atoms;            /* the term's size, in leaves              */

    /*  The residual compiled (docs/DESIGN.md §6.5): one instruction per
     *  node an instance builds, in post-order, two operands each; an
     *  operand names a constant, an argument, or an earlier result.  The
     *  constants are node indices, and roots. */
    uint32_t *ops;
    uint32_t  nops;
    uint32_t *consts;
    uint32_t  nconsts;
    uint32_t  root;             /* the operand the instance is            */

    bool      residual_ok;      /* a residual jet (§6.5); else only an
                                   interpreter jet's key                   */
    int32_t   interp;           /* its interpreter jet (§7), or -1         */
    av_ctor   ctor;             /* its constructor shape (§6.8), if any    */
    uint32_t  resolves;         /* a fact store's resolver (§8): 1 + the
                                   facts it encodes; 0 if not one         */
    uint8_t   admitted;         /* its native lookup: 0 unchecked, 1 agrees
                                   with the term, 2 refused               */
    bool      unquote;          /* the unquoter, UQ (§20.2): install      */
    bool      compiler;         /* the compiler's abstraction (§20.3)     */
    uint32_t  tmpl;             /* 1 + its template in a->tmpls (§6.9), or 0 */
    uint8_t   word_op;          /* a numeral operation on words (§6.10):
                                   an AV_WOP_*, or 0                      */
    bool      fix;              /* Curry's Y (§6.11): Y g unfolds to g (Y g) */
    bool      p2;               /* Poseidon2's term P (§6.12): P applied to a
                                   state runs natively                    */
    uint32_t  p2_nodes;         /* its term's distinct nodes, the bound on
                                   comparing a jet node's term with it    */
} av_jet;

/*  The numeral operations (§6.10), skijack's natAdd .. natIfLe. */
enum { AV_WOP_ADD = 1, AV_WOP_SUB, AV_WOP_MUL, AV_WOP_IFEQ, AV_WOP_IFLE };

/*  Register the term t as a jet unless it has fewer than min_atoms leaves,
 *  no arity up to AV_JET_ARITY_MAX at which an atom reaches the head within max_steps, or
 *  a residual of cost 0.  Returns the jet id, or AV_NONE with *why.  A
 *  term already registered returns its id.  The runs may collect: root
 *  every index held across the call.
 */
uint32_t av_jet_register(av_arena *a, uint32_t t, size_t min_atoms,
                         uint64_t max_steps, const char **why);

/*  Load a dictionary export (dictionary.tsv: hash, atoms, printed term per
 *  line), checking every hash against the term, and register each row;
 *  then wrap the inner jets of every fallback and residual.  Returns the
 *  number registered, or -1 with *err.
 */
long av_jets_load(av_arena *a, const char *path, size_t min_atoms,
                  const char **err);

/*  The constructor jets (docs/DESIGN.md §6.8): register every distinct
 *  subterm of t, of 2 to max_atoms leaves, that is a Scott constructor --
 *  whatever its encoding, in a dictionary or not -- and wrap the inner
 *  jets.  Match t afterwards, as for a dictionary.  Returns the number of
 *  new jets, or -1 when out of memory.
 */
long av_jets_ctors(av_arena *a, uint32_t t, size_t max_atoms);

/*  t's constructor shape, by running it on fresh atoms (§6.8); count 0 if
 *  t is not a constructor within max_steps a run. */
av_ctor av_ctor_of(av_arena *a, uint32_t t, uint64_t max_steps);

/*  The loader's match (§6.3): a fresh copy of t -- no node of t is reused,
 *  so the result shares nothing with the dashboard -- in which every
 *  subterm whose hash is a jet's is wrapped in a jet node.  AV_NONE if out
 *  of memory.
 */
uint32_t av_jets_match(av_arena *a, uint32_t t);

/*  Whether two terms are the same tree, looking through indirections and
 *  jets: 1 same, 0 different, -1 past the node budget.
 */
int av_equal(const av_arena *a, uint32_t x, uint32_t y, size_t budget);

/*  ------------------------------------------------------- interpreter jets
 *
 *  The interpreter jet (docs/DESIGN.md §7): a generated interpreter's fuel
 *  loop, `loop params fuel <t>`, run natively.  The datum is decoded to a
 *  live object term by probing, reduced in copy mode with object fuel --
 *  so the fuel boundary is the interpreter's, attempt for attempt -- with
 *  residual jets as the host has them and interpreter jets off inside, and the outcome
 *  encoded with the program's own constructors.  The spec comes from
 *  skijack's interpreters.tsv, each arm classified there by running it; the
 *  constructor terms from its dictionary.tsv.  A `diverge` arm reached at
 *  the head makes the jet decline, so the unjetted interpreter diverges as
 *  it would.  These jets change counts: a fire charges the contractions it
 *  performs, object steps and probes together.
 */
enum { AV_OROLE_S, AV_OROLE_K, AV_OROLE_I, AV_OROLE_APP, AV_OROLE_ERR,
       AV_OROLE_DIVERGE, AV_OROLE_SCRY };
enum { AV_RROLE_VALUE, AV_RROLE_TIMEOUT, AV_RROLE_OTHER };
enum { AV_AROLE_HIT, AV_AROLE_MISS, AV_AROLE_NOTYET };
#define AV_INTERP_CTORS 16

typedef struct av_interp {
    uint64_t  digest;           /* the loop term's                         */
    uint32_t  jet;              /* its dashboard entry                     */
    unsigned  nparams;
    unsigned  nobj, nres, nans;
    uint8_t   orole[AV_INTERP_CTORS], oarg[AV_INTERP_CTORS];
    uint32_t  octor[AV_INTERP_CTORS];   /* constructor terms: roots        */
    uint32_t  oleaf[AV_INTERP_CTORS];   /* a leaf's live node: roots       */
    uint8_t   rrole[AV_INTERP_CTORS];
    uint32_t  rctor[AV_INTERP_CTORS];
    uint8_t   arole[AV_INTERP_CTORS], aarg[AV_INTERP_CTORS];
    unsigned  value, timeout;   /* result constructor indices              */
} av_interp;

/*  Load interpreters.tsv, taking constructor and loop terms from
 *  dictionary.tsv, and attach each to its loop's dashboard entry (made if
 *  the loop is not a residual jet).  Its `nat` lines name known numeral
 *  encodings.  Returns the number of interpreters loaded, or -1.
 *
 *  A fire reads what it can by structure before it probes: a datum node
 *  that is one of the object type's constructor terms, or the application
 *  constructor over two fields, and a fuel numeral that is a known zero or
 *  a known suc over a numeral, decode at once; anything else is probed.
 *  The runtime may recognize structure (§3 of RUNTIME-DESIGN.md), and a
 *  node that is a constructor applied to its fields behaves as one. */
long av_interps_load(av_arena *a, const char *interps, const char *dictionary,
                     const char **err);

/*  ------------------------------------------------------------ templates
 *
 *  Supercombinator templates (docs/DESIGN.md §6.9): each rule's formals and
 *  open body, from skijack's templates.tsv and template_terms.tsv, keyed
 *  by the §5 hash of the SKI term it compiles to.  Load them after every
 *  dictionary and before av_jets_match, then bind them to the matched
 *  term; nothing may collect between.  A template of more than
 *  AV_JET_ARITY_MAX formals is skipped.  A template is kept only if its body
 *  abstracts to its key, and fires only on a node whose term is that key,
 *  compared as trees in a hash-consed table, never by hash alone.  With
 *  av_opts.templates, share mode instantiates the body over the arguments
 *  where the key meets them at the head: one step for the plumbing.
 */
typedef struct av_tmpl {
    uint32_t  jet;              /* its dashboard entry                    */
    unsigned  k;                /* formals: the arguments one fire takes  */
    uint32_t *ops;              /* per open application, two operands    */
    uint32_t  nops;
    uint32_t *consts;           /* indices into a->tmpl_globals           */
    uint32_t  nconsts;
    uint32_t  root;             /* the operand the instance is            */
    uint32_t  key;              /* its term, canonical at load            */
    bool      root_last;        /* the root is the last instruction: an
                                   instance may write it over the redex   */
    bool      globals_made;
    uint8_t  *sucop;            /* per instruction: it applies SUC, so an
                                   instance may build a word (§6.10); NULL
                                   when none does                         */
    uint32_t  nsuc;             /* such instructions: an instance takes
                                   nops + nsuc nodes at most              */
    av_ctor   ctor;             /* a Scott constructor's shape (§6.8), if
                                   its body is v_h v0 .. v(m-1): data jets
                                   dispatch it (§6.10)                    */
    uint8_t   case_h, case_p;   /* a case (§6.10): the body is formal
                                   case_h - 1 applied to case_p operands,
                                   written over the redex root; 0 none    */
    uint8_t  *case_spine;       /* per instruction: on that spine, used by
                                   its parent alone; NULL when no case    */
    uint8_t  *vspine;           /* per instruction: on the root's spine,
                                   used by its parent alone, so a deferred
                                   instance leaves it unwritten (reduce.c,
                                   "Deferred roots"); NULL when none      */
    uint32_t  nvspine;          /* how many, a chain below the root       */
} av_tmpl;

typedef struct av_tmplset av_tmplset;

/*  Load DIR/templates.tsv and DIR/template_terms.tsv.  NULL, with *err, on
 *  a malformed file or a term that does not match its hash; a template
 *  whose body does not abstract to its key is counted as refused. */
av_tmplset *av_templates_load(av_arena *a, const char *dir, const char **err);
/*  After av_jets_match: unwrap every jet node of t for a template whose
 *  term the node's is not.  False if a collection intervened, or memory. */
bool        av_templates_bind(av_arena *a, av_tmplset *ts, uint32_t t);
void        av_templates_counts(const av_tmplset *ts, long *accepted, long *refused,
                                long *skipped, long *unbound);
void        av_templates_free(av_tmplset *ts);
/*  Numeral operations (§6.10) the templates' DIR/words.tsv offered: those
 *  admitted, and those whose terms failed their probes. */
void        av_templates_word_counts(const av_tmplset *ts, long *admitted, long *refused);
/*  Whether the load registered Y (§6.11): av_fix_on was called first. */
bool        av_templates_fix(const av_tmplset *ts);

/*  ------------------------------------------------------------ words
 *
 *  Data jets on numerals (docs/DESIGN.md §6.10).  Turn words on before
 *  av_templates_load, which then reads DIR/words.tsv, skijack's numeral
 *  operations; after av_templates_bind, av_words_scan turns the closed
 *  numerals of t and of the templates' globals into words, in place, and
 *  av_words_mark finds the template instructions that apply SUC.  With
 *  av_opts.data, share mode runs an operation natively when its operands
 *  are words already, and otherwise runs its term.  A word meeting its
 *  continuations dispatches in one step whether or not the option is on:
 *  it exists only where these calls made it.
 */
bool av_words_on(av_arena *a);

/*  ------------------------------------------------------------ frame traces
 *
 *  An observer of copy mode's head run (docs/DESIGN.md §22), for the pure S
 *  calculus with one opaque atom, the passenger: before each S contraction
 *  a line `n L positions d D event arity` (docs/RUNTIME.md, "Frame
 *  traces"), frames dumped as a node table at chosen steps, and, at the
 *  end, the halt and the records.  It decides nothing.  Set av_opts.trace
 *  with av_opts.no_collect, strategy copy and whnf_only.
 */
typedef struct av_trace av_trace;
typedef struct {
    const char *kind;           /* HALT-X HALT-B OPEN FUEL -              */
    size_t      nconf;          /* confirmed records                      */
    int64_t     last_restart;   /* -1: none                               */
} av_trace_summary;
/*  out NULL: a silent pass (steps and records only, for a second pass). */
av_trace *av_trace_new(av_arena *a, const char *passenger, bool steps_out, FILE *out);
void      av_trace_free(av_trace *t);
/*  Whether every node of the term is S, the passenger, or an application. */
bool      av_trace_check(av_trace *t, const av_arena *a, uint32_t root);
bool      av_trace_dump_at(av_trace *t, const uint64_t *steps, size_t n);
void      av_trace_dump_halt(av_trace *t, bool on);
bool      av_trace_end(av_trace *t, const av_arena *a, av_status status, uint64_t steps,
                       uint32_t term, size_t conf, bool want_records, av_trace_summary *sum);
/*  The confirmed records' steps n and n+1, for a second pass; malloc'd. */
size_t    av_trace_record_steps(const av_trace *t, size_t conf, uint64_t **out);
/*  The frames the census reads over the confirmed records, in its order
 *  (docs/RUNTIME.md, "Frame traces": --frame-dump=census); malloc'd. */
size_t    av_trace_census_steps(const av_trace *t, size_t conf, uint64_t **out);
uint64_t  av_trace_steps_seen(const av_trace *t);
void      av_trace_flush(av_trace *t);
/*  Y unfolded in one step (docs/DESIGN.md §6.11): call before
 *  av_templates_load, which then registers Curry's Y, found in the loaded
 *  term and the templates' globals by tree identity.  With av_opts.fix,
 *  share mode rewrites Y g, Y at the head with an argument, to g (Y g), a
 *  fresh Y g: convertible, acyclic, one step. */
void av_fix_on(av_arena *a);
long av_words_scan(av_arena *a, uint32_t t);    /* words made, or -1 */
bool av_words_mark(av_arena *a);

/*  ------------------------------------------------------------ jet stats
 *
 *  What each jet does on a run (docs/DESIGN.md §6.7): fires and the
 *  contractions they absorb; misses, reached at the head with fewer
 *  arguments than its arity; share-mode demotions, and those that copied
 *  its term.  And each fire's origin: its jet node from the program as
 *  loaded (top), from an instance of another jet's residual -- after that
 *  jet fired -- or from another jet's term, entered because that jet did
 *  not.  Keyed by §5 digest, across runs and arenas; av_jetstats_begin
 *  once per loaded, matched program, before its reductions.
 */
typedef struct av_jetstats av_jetstats;

enum { AV_FROM_RESIDUAL = 0, AV_FROM_TERM = 1 };

typedef struct {
    uint64_t fires, absorbed;       /* absorbed: fires times the cost      */
    uint64_t top, in_residual, in_term;   /* the fires, by origin          */
    uint64_t misses, demotions, copies;
    av_ctor  ctor;                  /* its constructor shape, if one */
    uint32_t nodes;                 /* nodes one fire's instance builds */
} av_jetstat_row;

typedef struct { size_t outer, inner; unsigned kind; uint64_t fires; } av_jetstat_pair;

av_jetstats *av_jetstats_new(void);
void         av_jetstats_free(av_jetstats *s);
bool         av_jetstats_begin(av_jetstats *s, const av_arena *a, uint32_t t);
size_t       av_jetstats_rows(const av_jetstats *s);
void         av_jetstats_row(const av_jetstats *s, size_t i, char hash[27],
                             unsigned *arity, uint64_t *cost, size_t *atoms,
                             av_jetstat_row *counts);
bool         av_jetstats_find(const av_jetstats *s, const char *hash, size_t *i);
/*  The (outer, inner, origin) triples and their fires; *out is malloc'd. */
size_t       av_jetstats_pairs(const av_jetstats *s, av_jetstat_pair **out);
/*  Whether an origin was lost to memory, so counts undercount. */
bool         av_jetstats_lost(const av_jetstats *s);

/*  av_jets_load, registering only the row whose hash is `only`. */
long av_jets_load_only(av_arena *a, const char *path, size_t min_atoms,
                       uint64_t only, const char **err);

/*  ------------------------------------------------------- the front end
 *
 *  The SKIjack-0 front end (docs/DESIGN.md §20.3): `front` applied to a
 *  program's 7-bit character codes reduces to ROk (OCons name tm ..) or
 *  RErr.  The terms are the front end's own: SCons, SNil and Code, Lo, Hi
 *  build the input, each code's datum once.
 */
typedef struct { uint32_t front, scons, snil, code, lo, hi; } av_front0;

/*  `front` applied to src; AV_NONE if src is not ASCII or out of memory. */
uint32_t av_front0_input(av_arena *a, const av_front0 *f, const char *src, size_t len);

/*  Reduce t, from av_front0_input, reading its result by probing with
 *  collection on: a line `name TAB hash` per name, in its order, or
 *  `RErr`.  0 for ROk, 1 for RErr, -1 with *err if it does not read.
 *  *steps counts every probe's contractions, and *tally (if not NULL)
 *  sums them with the template instantiations (§6.9), dispatches and
 *  numeral operations (§6.10) among them. */
int      av_front0_read(av_arena *a, uint32_t t, const av_opts *o, FILE *out,
                        uint64_t *steps, av_result *tally, const char **err);

/*  ---------------------------------------------------------------- profile
 *
 *  Which named terms a share-mode run executes (docs/DESIGN.md §6.7): at
 *  av_profile_begin every node of the loaded term belongs to the innermost
 *  subterm a name's §5 hash matches, and each contraction is charged to the
 *  owner of the first loaded node among its combinator's partial
 *  applications (`S f`, `S f g`; `K x`; the redex `I x`), or to a row for
 *  code the run built.
 *  Ownership follows the nodes through collections.  Diagnostic only: it
 *  changes no count and no result.
 */
typedef struct av_profile av_profile;

av_profile *av_profile_new(void);
void        av_profile_free(av_profile *p);
/*  Name the term whose published hash is `hash`; a second name for one
 *  hash joins the first with "/".  False on a bad hash or memory. */
bool        av_profile_name(av_profile *p, const char *hash, const char *name);
/*  Before the run, after every name: own the nodes of t. */
bool        av_profile_begin(av_profile *p, const av_arena *a, uint32_t t);
/*  The `top` rows with the most contractions, most first. */
void        av_profile_report(const av_profile *p, FILE *out, size_t top);
/*  The contractions charged to the row named exactly `name`, and to all. */
uint64_t    av_profile_count(const av_profile *p, const char *name);
uint64_t    av_profile_total(const av_profile *p);

/*  ----------------------------------------------------------------- census
 *
 *  Which terms a program calls, for choosing jets (docs/DESIGN.md §6.7).
 *  In copy mode a contraction puts a term in function position: the x of
 *  S x y z, K x y and I x; the run starts with the loaded term there.  The
 *  census records every left-spine prefix of
 *  it -- the nodes a jet could be matched on -- by a structural fingerprint,
 *  with how many arguments were there to meet it.  A second pass captures
 *  the chosen prefixes' terms into the census's own arena, and the analysis
 *  registers each as a residual jet (§6.5), for its arity and cost; a third
 *  pass measures what each alone would absorb, a call that falls inside a
 *  fire's own window counting as absorbed rather than as another fire.
 */
typedef struct av_census av_census;

typedef struct {
    uint64_t  fp;               /* the census's fingerprint, not §5's hash */
    uint64_t  calls;            /* times the prefix met the head           */
    uint64_t  hist[10];         /* arguments there: 0 .. 8, and 9 or more  */
    size_t    atoms;            /* its size, in leaves                     */
    uint32_t  term;             /* captured, in av_census_arena; or AV_NONE */
    unsigned  arity;            /* as a residual jet; 0 if it is not one   */
    uint64_t  cost;             /* contractions one fire absorbs           */
    uint64_t  fires, saved;     /* measured, this jet alone: a call inside
                                   a fire's own window is absorbed, not a
                                   fire (recursion re-enters its window)   */
    char      hash[27];         /* §5's, when captured                     */
    av_ctor   ctor;             /* its constructor shape (§6.8), if one    */
    int64_t   folds_into;       /* the higher-ranked row it folds into: a
                                   subterm of it (or the reverse), with as
                                   many calls -- one call's layers; -1 if
                                   rows fold into it instead               */
    size_t    folded;           /* rows folded into it, when it heads      */
} av_census_row;

av_census     *av_census_new(void);
void           av_census_free(av_census *c);

/*  After the first pass: keep the n most-called prefixes of at least
 *  min_atoms leaves, and capture their terms on the next pass. */
void           av_census_select(av_census *c, size_t n, size_t min_atoms);

/*  After the capture pass: register each captured term as a residual jet,
 *  for its arity and cost, and measure on the next pass. */
void           av_census_analyze(av_census *c);

/*  Before each run, with the term it loaded: only a subterm of loaded code
 *  can become a jet -- the matcher wraps loaded code, never what a run
 *  builds -- so only those are counted.  A fire's window does not cross
 *  from one run into the next. */
bool           av_census_begin_run(av_census *c, const av_arena *a, uint32_t loaded);

/*  After the measuring pass: the rows, most contractions saved first.
 *  They stay the census's. */
size_t         av_census_rows(av_census *c, av_census_row **rows);
av_arena      *av_census_arena(av_census *c);
uint64_t       av_census_calls(const av_census *c);

/*  ------------------------------------------------------------------- scry
 *
 *  §8: the fact store, the resolver it specifies, and the resume loop, as
 *  skijack's run.py has them (make_resolver, run_with_namespace).
 *
 *  A fact is (key datum, answer datum): the path a run blocked on, as the
 *  run left it, and the answer the namespace gave.  The store is append-
 *  only with unique keys -- keys compared as the object terms they decode
 *  to, as EQ5 compares encodings -- and keeps its terms in its own arena,
 *  which nothing reduces.  With a log, each fact is written and synced
 *  before it is used (§19's order), and av_facts_open replays the log.
 */
typedef struct av_facts av_facts;   /* src/scry.c */

/*  The object type a program's paths and values are data of: its
 *  constructors' names in declaration order, the application's index. */
typedef struct {
    const char *const *names;
    unsigned nctors, app;
} av_objtype;

/*  A store for paths of the object type obj, whose names it keeps by
 *  pointer: they must outlive the store. */
av_facts *av_facts_new(const av_objtype *obj);
/*  A store backed by a log at path: its facts are replayed, and every
 *  later fact appended and synced.  NULL, with *err, if it is unreadable. */
av_facts *av_facts_open(const av_objtype *obj, const char *path, const char **err);
void      av_facts_free(av_facts *f);
size_t    av_facts_count(const av_facts *f);
/*  Fact i's key as the path it decodes to, printed ("S K"). */
const char *av_facts_key(const av_facts *f, size_t i);

/*  Append (key datum, answer datum), both terms of arena a.  False, with
 *  *err, if the key is already known -- the store is append-only -- or the
 *  log cannot be written. */
bool av_facts_append(av_facts *f, av_arena *a, uint32_t key, uint32_t answer,
                     const char **err);

/*  Aviary's bracket abstraction, with eta: [x]x = I, [x]E = K E when x is
 *  not free in E, [x](E x) = E when x is not free in E, else S [x]E [x]F.
 *  x is a leaf.  AV_NONE when out of memory. */
uint32_t av_abstract(av_arena *a, uint32_t x, uint32_t body);

/*  The resolver over the store's first n facts, in arena a: skijack's
 *  resolver_term, [p] EQ5 p k1 (hit a1) (EQ5 p k2 (hit a2) (... notyet)),
 *  eq, hit and notyet being terms of a.  It is registered as a jet key
 *  tagged with n, so a matched program's interpreter jet may look paths up
 *  natively (§8) once the lookup agrees with this term. */
uint32_t av_facts_resolver(av_arena *a, const av_facts *f, size_t n,
                           uint32_t eq, uint32_t hit, uint32_t notyet);

/*  A level-1 program to resume: interp applied to the resolver, then
 *  params, then a fuel numeral (zero, suc), then datum.  Its terms live in
 *  arena `terms`, which the loop only copies from.  The result type has
 *  nres constructors: `block` (its second one-field constructor) and
 *  `timeout` (its last terminal), by index. */
typedef struct {
    av_arena *terms;
    uint32_t  interp, datum, zero, suc, eq, hit, notyet;
    uint32_t *params;           /* after the resolver */
    unsigned  nparams;
    unsigned  nres, block, timeout;
    av_objtype obj;
} av_nsprog;

/*  Where facts come from: the answer datum, in a, for a blocked path
 *  printed as `key`, or AV_NONE if the namespace has none. */
typedef uint32_t (*av_resolve_fn)(void *ctx, av_arena *a, const char *key);

/*  A fresh arena for one attempt, set up as the caller wants it (jets,
 *  interpreters); NULL uses av_arena_new. */
typedef av_arena *(*av_arena_fn)(void *ctx);

/*  One level-1 run the loop made. */
typedef struct { uint64_t fuel, steps, lookups; av_status status; } av_attempt;

typedef struct {
    char    **events;           /* run_with_namespace's trace */
    size_t    nevents;
    av_attempt *attempts;
    size_t    nattempts;
    int       ctor;             /* the final result constructor, or -1 */
    char     *payload;          /* its field decoded and printed, or NULL */
    unsigned  rounds;
} av_nsrun;

/*  The resume loop (§8; run_with_namespace): each round, build the
 *  resolver from every fact learned so far, run the program from scratch
 *  -- at `fuel`, or with fuel 0 deepening from start, doubling, to cap --
 *  and peel it.  A value or any constructor but `block` ends the run; a
 *  block decodes its path, and if the path is unknown to the store and the
 *  namespace answers it, the fact is appended and the next round starts;
 *  otherwise STUCK.  Events: "budget N", "BLOCK on P", "STUCK", a result
 *  constructor's name, "status:fuel", "EXCEEDED MAX ROUNDS".  o is each
 *  attempt's options (copy mode and WHNF are forced).  False only when out
 *  of memory. */
bool av_ns_run(const av_nsprog *p, av_facts *f, av_resolve_fn resolve, void *rctx,
               av_arena_fn fresh, void *actx, uint64_t fuel, uint64_t start,
               uint64_t cap, unsigned max_rounds, const av_opts *o,
               const char *const *result_names, av_nsrun *out);
void av_nsrun_free(av_nsrun *r);

/*  ---------------------------------------------------------------- install
 *
 *  §20.2: an encoded term -- a Scott datum of S | K | I | App t u, the
 *  constructors in that order -- becomes the live term it encodes.  This
 *  runs from data to a live term, the direction Proposition 3.1 permits;
 *  nothing here quotes a live term.  Install is where code arriving
 *  mid-run has its jets matched, as the loader matches a program's.
 */

/*  The live term datum encodes, found by probing, its jets matched; the
 *  probes' contractions are counted in a->probe_steps.  AV_NONE, with
 *  *err, if it does not decode. */
uint32_t av_install(av_arena *a, uint32_t datum, const av_opts *o, const char **err);

/*  t's datum, with constructors Avon builds by bracket abstraction:
 *  S = λs k i a. s, K = λs k i a. k, I = λs k i a. i, App t u = λs k i a.
 *  a t u.  AV_NONE for a term with atoms. */
uint32_t av_encode(av_arena *a, uint32_t t);

/*  Make uq the unquoter's jet key (UQ m = m S K I (UQA UQ), the paper's):
 *  admitted only if, on sample terms t, the normal form of uq applied to
 *  t's datum is t.  With install_jets, UQ d at the head is installed
 *  natively and charged the probes' contractions; --jet-check compares a
 *  fire with UQ's own reduction, by normal form. */
bool av_unquote_register(av_arena *a, uint32_t uq, const char **err);

/*  ----------------------------------------------------------------- kernel
 *
 *  §9: a kernel is a door, [[poke [peek load]] state], read by axis and
 *  never by name.  An arm is pulled Nock 9's way: (n@k) k arg, n@k the
 *  ABI's Scott pair selectors, hd = S I (K K) and tl = S I (K (K I)),
 *  applied down the bits of n after the leading 1.  A poke's value is
 *  [effects kernel']: the kernel installed is tl of it, unreduced, as the
 *  reference host's loop installs it, and the effects are hd of it.
 */
enum { AV_AXIS_POKE = 4, AV_AXIS_PEEK = 10, AV_AXIS_LOAD = 11, AV_AXIS_STATE = 3 };

/*  n@t: t under the selectors for axis n (n >= 1). */
uint32_t av_axis(av_arena *a, unsigned n, uint32_t t);

/*  (n@k) k arg. */
uint32_t av_pull(av_arena *a, unsigned n, uint32_t k, uint32_t arg);

/*  Whether t is a kernel: probed, it is a pair whose head is a pair whose
 *  tail is a pair.  Probing never collects and never writes. */
bool av_is_kernel(av_arena *a, uint32_t t, const av_opts *o);

typedef struct {
    av_arena *a;
    uint32_t  k;                /* the installed kernel; a root */
    av_opts   o;                /* every pull's reduction */
    uint64_t  events;           /* pokes and loads applied */
} av_kernel;

/*  Boot (§9, §20.1): apply the pill's term to the initial subject and
 *  reduce to weak head normal form.  If the value is a kernel it is
 *  installed and *is_kernel set; otherwise *value is it, reduced, as a
 *  program that is not a kernel is applied once.  k->k is rooted in a
 *  until av_kernel_free. */
av_status av_kernel_boot(av_kernel *k, av_arena *a, uint32_t pill, uint32_t subject,
                         const av_opts *o, bool *is_kernel, uint32_t *value,
                         av_result *r);

/*  Adopt an existing kernel term, as boot's value or a snapshot's. */
void av_kernel_adopt(av_kernel *k, av_arena *a, uint32_t kernel, const av_opts *o);
void av_kernel_free(av_kernel *k);

/*  Pull poke with event: *effects is hd of the value, a term of the
 *  program's effects type, valid until the arena next collects; the
 *  kernel installed is tl of it.  The status is the reduction's; the
 *  kernel is unchanged unless it is AV_WHNF. */
av_status av_kernel_poke(av_kernel *k, uint32_t event, uint32_t *effects, av_result *r);

/*  Pull peek with path: *answer is the value, reduced to WHNF. */
av_status av_kernel_peek(av_kernel *k, uint32_t path, uint32_t *answer, av_result *r);

/*  Upgrade: pull load from new_kernel with the installed kernel's state,
 *  3@k, and install the result, unreduced; the new battery migrates the
 *  state (§9, NockApp's rule). */
bool av_kernel_load(av_kernel *k, uint32_t new_kernel);

/*  3@k. */
uint32_t av_kernel_state(av_kernel *k);

/*  ------------------------------------------------------------------ pier
 *
 *  A kernel's durable home (§19, §20.4): a directory holding the event
 *  log, `events.log`, and snapshots, `snap-N` with `snap-N.sum`, N the
 *  events applied.  Each event is appended and synced before it is
 *  applied, and a snapshot is written image first, sidecar last
 *  (av_snapshot_save).  Opening a pier loads the newest snapshot that
 *  verifies and replays the log's later events, so a pier reopened after
 *  a crash holds the kernel the events it logged produce.  Log records:
 *  `poke N <event SKIT, hex>`, `load N <new kernel's pill SKIT, hex>
 *  <subject SKIT, hex>`, and, under entropy (below), `entropy 0` and
 *  `eny N <id SKIT, hex> <16 bytes, hex>`; a record without its newline was cut short by a
 *  crash, and is dropped.
 */
typedef struct av_pier av_pier;

/*  A new pier at dir, which must not hold one: boot pill on subject (both
 *  SKIT), which must give a kernel, and write snapshot 0. */
av_pier *av_pier_new(const char *dir, const uint8_t *pill, size_t npill,
                     const uint8_t *subject, size_t nsubject, const av_opts *o,
                     const char **err);
/*  The same, on a persistent arena (§19.1) in dir/pma: every event is
 *  committed to it after it is logged and applied, and a reopen maps it
 *  and replays only the log after its last commit. */
av_pier *av_pier_new_pma(const char *dir, const uint8_t *pill, size_t npill,
                         const uint8_t *subject, size_t nsubject, const av_opts *o,
                         const char **err);
/*  Reopen: the persistent arena if the pier has one, else the newest
 *  verified snapshot; then the log after it. */
av_pier *av_pier_open(const char *dir, const av_opts *o, const char **err);
void     av_pier_free(av_pier *p);
av_kernel *av_pier_kernel(av_pier *p);

/*  Log, sync, then poke with the SKIT event; *effects as av_kernel_poke. */
av_status av_pier_poke(av_pier *p, const uint8_t *event, size_t n, uint32_t *effects,
                       av_result *r, const char **err);
/*  Log, sync, then upgrade to the kernel pill boots to on subject. */
bool av_pier_load(av_pier *p, const uint8_t *pill, size_t npill, const uint8_t *subject,
                  size_t nsubject, const char **err);
/*  Snapshot the installed kernel at the current event count. */
bool av_pier_snapshot(av_pier *p, const char **err);

/*  Entropy (§9.1).  A pier made with AV_PIER_ENTROPY answers each
 *  request [0 id] in a poke's effects list with the event [0 [id bits]],
 *  bits 128 Scott Booleans, each reply logged as `eny N <id jammed> <16
 *  bytes>` before it is applied; one outside event draws AV_ENY_MAX
 *  replies at most.  An outside event is accepted only when probing shows
 *  it a cell [tag data] with tag a successor: tag 0 is the replies'.  The
 *  opt-in is the log's `entropy 0` record, written before the pier's
 *  image, and records whether the pier draws from a file
 *  (AV_PIER_ENTROPY_FILE, for tests) or from getentropy; it never mixes
 *  them.  av_pier_entropy gives this session's file (from byte 16 n, n the
 *  replies logged), NULL for getentropy, and answers
 *  boot's own request, [0 [0 bits]], if no reply is logged yet; the first
 *  poke does too, after a crash took it.  A failure while answering a
 *  poke's requests leaves the poke applied and successful, the failure in
 *  av_pier_entropy_error. */
#define AV_ENY_BYTES 16
#define AV_ENY_MAX   16
#define AV_ENY_WALK  1024           /* effects list elements probed */
#define AV_ENY_PROBE_STEPS 10000000 /* probe contractions one event's effects may spend */
#define AV_PIER_PMA     1u
#define AV_PIER_ENTROPY 2u
#define AV_PIER_ENTROPY_FILE 4u     /* entropy from a file only, for tests */
av_pier *av_pier_new_ex(const char *dir, const uint8_t *pill, size_t npill, const uint8_t *subject,
                        size_t nsubject, const av_opts *o, unsigned flags, const char **err);
typedef void (*av_pier_event_fn)(void *ctx, uint64_t event, uint64_t steps, uint32_t effects,
                                 bool reply);
bool     av_pier_entropy(av_pier *p, const char *file, const char **err);
/*  Why the last poke's (or av_pier_entropy's) replies stopped short, or
 *  NULL: a spent file, a probe budget, out of memory. */
const char *av_pier_entropy_error(const av_pier *p);
/*  Called as each event av_pier_poke applies, the outside event and then
 *  its replies, with its number, contractions and effects. */
void     av_pier_on_event(av_pier *p, av_pier_event_fn fn, void *ctx);
/*  The replies the last poke (or boot) drew, and the requests it left
 *  unanswered at the cap. */
uint64_t av_pier_replies(const av_pier *p, uint64_t *unanswered);

/*  ---------------------------------------------------------- the compiler
 *
 *  §20.3: the compiler's core as a term -- bracket abstraction written in
 *  SKIjack (tests/selfhost/abstract.ascii.ski), `abs x t` over encoded
 *  terms tm = TS | TK | TI | TV nat | TA ap, ap = Ap tm tm -- and its jet,
 *  native abstraction (av_abstract), licensed by differential against the
 *  term.  A term here is S, K, I and atoms `vN`, the variable numbered N.
 */
typedef struct {
    uint32_t abs, ts, tk, ti, tv, ta, ap, zero, suc;   /* terms of one arena */
} av_compiler;

/*  t (S, K, I, atoms vN) as a tm datum with c's constructors; AV_NONE for
 *  any other atom. */
uint32_t av_tm_encode(av_arena *a, const av_compiler *c, uint32_t t);

/*  A tm datum, read by probing, as a term; AV_NONE with *err if it is not
 *  one.  Probes never collect. */
uint32_t av_tm_decode(av_arena *a, uint32_t datum, const av_opts *o, const char **err);

/*  The numeral n with c's Zero and Suc. */
uint32_t av_tm_nat(av_arena *a, const av_compiler *c, uint64_t n);

/*  Make c.abs the compiler jet's key: admitted only if, on sample terms,
 *  abs x t -- reduced, decoded -- is native abstraction's [vx] t.  With
 *  compile_jets, `abs x t` at the head is answered natively, charged its
 *  probes' contractions; --jet-check compares a fire with the term's own
 *  reduction, decoded. */
bool av_compiler_register(av_arena *a, const av_compiler *c, const char **err);

/*  -------------------------------------------------------- persistent arena
 *
 *  §19.1: an arena whose node array is an image file mapped copy-on-write
 *  into reserved address space.  Opening reads the header and the leaf
 *  names, not the nodes; a commit writes the chunks changed since the last
 *  one, through a redo journal, so a crash at any point leaves the image
 *  as it was before the commit or after it.  An arena with a jet
 *  dashboard is refused a commit: jet nodes carry dashboard ids, and the
 *  dashboard is never persisted (§19).
 */
typedef struct av_pma av_pma;

/*  Give the arena a persistent image in dir, which must hold none: its
 *  nodes move into a mapping, and the first commit writes them all. */
bool      av_pma_attach(av_arena *a, const char *dir, const char **err);

/*  Reopen the image in dir: a journal left by a crash is applied first.
 *  *root and *events are the last commit's. */
av_arena *av_pma_open(const char *dir, uint32_t *root, uint64_t *events, const char **err);

/*  Commit the arena as it stands, with root (AV_NONE for none) and the
 *  number of events it reflects. */
bool      av_pma_commit(av_arena *a, uint32_t root, uint64_t events, const char **err);

/*  Check every node of the image: tags, indices, leaves, no jet nodes. */
bool      av_pma_verify(const av_arena *a, uint32_t root, const char **err);

/*  Bytes the last commit wrote to the journal, and chunks it carried. */
uint64_t  av_pma_last_bytes(const av_arena *a);
uint64_t  av_pma_last_chunks(const av_arena *a);

/*  For tests: a commit stops the process (_exit) at this point: 1 after
 *  the journal is written, before its rename; 2 after the rename; 3 half
 *  way through applying it; 4 after applying it, before removing it. */
extern int av_pma_crash_at;

#endif /* AVON_H */
