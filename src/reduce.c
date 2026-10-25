/**  reduce.c
 *
 *  Normal-order reduction, two strategies.
 *
 *  copy   The reference host's algorithm, aviary_kernel.reduce, on nodes:
 *         nothing is ever mutated, and its contraction counts are the
 *         paper's.  It is copy.c.
 *  share  Turner's machine: walk down the spine, overwrite the redex root
 *         in place, so a duplicated redex is contracted once.  It is
 *         here, with the jet, template and data-jet dispatch it runs; its
 *         spine stack, with deferred roots, is stack.h.
 *
 *  This file also holds the collector's view of a run (memory), the jet
 *  helpers both machines call, and the driver, av_reduce.  machine.h is
 *  R, the state they share.  Neither machine recurses.  Fuel is checked before every attempt to contract,
 *  the last of which finds no redex, so s contractions need fuel s + 1.
 */

#include <assert.h>
#include <stdlib.h>
#include <string.h>

#include "machine.h"
#include "sstats.h"
#include "stack.h"

#ifdef AV_STRICT_STATS
av_sstats *sstats_g;
#endif

/*  ---------------------------------------------------------------- memory */

static void roots(av_gc *g, void *ctx) {
    R *r = ctx;
    r->root = av_gc_evac(g, r->root);
    if (r->head != AV_NONE) r->head = av_gc_evac(g, r->head);
    if (r->cur != AV_NONE) r->cur = av_gc_evac(g, r->cur);
    if (r->jnode != AV_NONE) r->jnode = av_gc_evac(g, r->jnode);
    if (r->hold != AV_NONE) r->hold = av_gc_evac(g, r->hold);
    for (size_t i = 0; i < r->top; i++) {      /* a share-mode entry keeps its kind */
        uint32_t e = r->stk[i];
        r->stk[i] = (e & ~AV_PAYLOAD) | av_gc_evac(g, e & AV_PAYLOAD);
    }
    for (size_t i = 0; i < r->ndstk; i++) r->dstk[i].arg = av_gc_evac(g, r->dstk[i].arg);
    for (size_t i = 0; i < r->nfr; i++)
        r->fr[i].head = av_gc_evac(g, r->fr[i].head);
    for (size_t i = 0; i < r->nwork; i++)
        r->work[i] = av_gc_evac(g, r->work[i]);
}

static bool mark_get(const R *r, uint32_t i) {
    size_t w = i / 64;
    return w < r->nmarks && (r->marks[w] >> (i % 64) & 1u);
}

static bool mark_set(R *r, uint32_t i) {
    size_t w = i / 64;
    if (w >= r->nmarks) {
        size_t n = r->nmarks ? r->nmarks : 1024;
        while (n <= w) n *= 2;
        uint64_t *m = realloc(r->marks, n * sizeof *m);
        if (!m) return false;
        memset(m + r->nmarks, 0, (n - r->nmarks) * sizeof *m);
        r->marks = m;
        r->nmarks = n;
    }
    r->marks[w] |= (uint64_t)1 << (i % 64);
    return true;
}

#define YM_NONE UINT64_MAX          /* ymemo: g's y0 was written; none yet */

static void remap_marks(av_gc *g, void *ctx) {
    R *r = ctx;
    if (r->o->profile) profile_remap(r->o->profile, g);
    if (r->o->jetstats) jetstats_remap(r->o->jetstats, g);
    if (r->ymemo.n) {               /* an entry with a node dead goes */
        nmap old = r->ymemo, fresh = { 0 };
        for (size_t i = 0; i < old.cap; i++) {
            if (old.key[i] == AV_NONE || old.val[i] == YM_NONE) continue;
            uint32_t k = av_gc_forwarded(g, old.key[i]);
            uint32_t y = av_gc_forwarded(g, (uint32_t)(old.val[i] >> 32));
            uint32_t u = av_gc_forwarded(g, (uint32_t)old.val[i]);
            if (k != AV_NONE && y != AV_NONE && u != AV_NONE &&
                !nmap_put(&fresh, k, (uint64_t)y << 32 | u))
                break;
        }
        nmap_free(&old);
        r->ymemo = fresh;          /* out of memory: entries lost, not wrong */
    }
    if (!r->marks) return;
    uint64_t *old = r->marks;
    size_t nold = r->nmarks;
    r->marks = NULL;
    r->nmarks = 0;
    for (size_t w = 0; w < nold; w++) {
        for (uint64_t bits = old[w]; bits; bits &= bits - 1) {
            uint32_t i = (uint32_t)(w * 64 + (size_t)__builtin_ctzll(bits));
            uint32_t j = av_gc_forwarded(g, i);
            if (j != AV_NONE) mark_set(r, j);
        }
    }
    free(old);
}

/*  ensure()'s other half (machine.h): reserve without collecting, or
 *  collect. */
bool ensure_slow(R *r, size_t k) {
    av_arena *a = r->a;
    if (r->o->no_collect || r->o->census)   /* a census keys on node identity */
        return av_reserve(a, (uint32_t)k) && a->used <= r->o->max_nodes;
    /* every active reduction's roots, this one's among them */
    if (!av_collect(a, (uint32_t)k, NULL, NULL, NULL)) return false;
    return a->used <= r->o->max_nodes;
}

/*  ------------------------------------------------------------------ jets */

/*  --jet-check: run the jet node's own term over the arguments in
 *  copy mode, jets off, for exactly the charge, and compare the state it
 *  reaches with an instance.  Allocates without collecting.  False only on
 *  a definite disagreement; a check that runs out of memory or of its
 *  comparison budget is inconclusive, not a fault. */
bool check_fire(R *r, uint32_t node, uint32_t id, const uint32_t *args) {
    av_arena *a = r->a;
    const av_jet *j = &a->jets[id];
    uint32_t t = av_right(a, node);
    for (unsigned i = 0; i < j->arity && t != AV_NONE; i++) t = av_app(a, t, args[i]);
    if (t == AV_NONE) return true;                  /* out of memory */
    av_opts co = av_opts_default();
    co.strategy = AV_COPY;
    co.whnf_only = true;
    co.max_steps = j->cost;
    co.no_collect = true;
    co.jets = false;
    av_result cr = av_reduce(a, t, &co);
    if (cr.status == AV_SIZE) return true;          /* out of memory */
    if (cr.status != AV_FUEL || cr.steps != j->cost) return false;
    uint32_t inst = jet_instance(a, id, args, false);
    if (inst == AV_NONE) return true;               /* out of memory */
    return av_equal(a, cr.term, inst, 100000000) != 0;   /* -1: too large */
}

/*  An interpreter jet at the head of a position with `have` arguments:
 *  1 fired (the arguments replaced by the outcome and its charge added),
 *  0 declined, -1 stop with *st.  The arguments are read again after the
 *  fire, which may collect. */
/*  How many arguments a fire of jet id consumes: the unquoter's one, an
 *  interpreter's parameters, fuel and datum. */
unsigned fire_nargs(const R *r, uint32_t id) {
    const av_arena *a = r->a;
    if (a->jets[id].unquote && r->o->install_jets) return 1;
    if (a->jets[id].compiler && r->o->compile_jets) return 2;
    return a->interps[a->jets[id].interp].nparams + 2;
}

int try_interp(R *r, uint32_t *nodep, size_t have, av_status *st,
               uint32_t *outp) {
    av_arena *a = r->a;
    uint32_t node = *nodep;
    uint32_t id = AV_JET_ID(av_left(a, node));
    bool uq = a->jets[id].unquote && r->o->install_jets;    /* install */
    bool cj = !uq && a->jets[id].compiler && r->o->compile_jets;   /* compile */
    if (!uq && !cj && (!r->o->interp_jets || a->jets[id].interp < 0)) return 0;
    unsigned nargs = fire_nargs(r, id);
    if (have < nargs || r->steps >= r->o->max_steps) return 0;
    uint32_t argv[AV_INTERP_CTORS + 2];
    for (unsigned i = 0; i < nargs; i++)
        argv[i] = av_res(a, r->o->strategy == AV_COPY
                                ? r->stk[r->top - 1 - i]
                                : av_right(a, r->stk[r->top - 1 - i]));
    uint32_t out;
    uint64_t charge;
    bool fault;
    r->jnode = node;
    fault = false;
    int rc = uq ? install_fire(a, argv[0], r->o, r->o->max_steps - r->steps, &out, &charge)
           : cj ? compile_fire(a, argv, r->o, r->o->max_steps - r->steps, &out, &charge)
                : interp_fire(a, id, argv, r->o, r->o->max_steps - r->steps,
                              &out, &charge, st, &fault);
    node = r->jnode;                    /* where the node is now */
    r->jnode = AV_NONE;
    *nodep = node;
    if (rc < 0) { r->jet_fault |= fault; return -1; }
    if (rc == 0) return 0;
    if (r->o->jet_check && (r->jet_calls + 1) % r->o->jet_check == 0) {
        for (unsigned i = 0; i < nargs; i++)           /* reread: may have moved */
            argv[i] = av_res(a, r->o->strategy == AV_COPY
                                    ? r->stk[r->top - 1 - i]
                                    : av_right(a, r->stk[r->top - 1 - i]));
        av_root_push(a, &out);
        bool same = uq ? install_check(a, node, argv[0], out)
                  : cj ? compile_check(a, node, argv, out)
                       : interp_check(a, id, node, argv, out);
        av_root_pop(a);
        if (!same) { r->jet_fault = true; *st = AV_INTERRUPTED; return -1; }
    }
    r->steps += charge;
    r->jet_steps += charge;
    r->jet_calls++;
    if (!uq && !cj) r->interp_calls++;
    *outp = out;
    return 1;
}

/*  ----------------------------------------------------------------- share */

/*  Whether an instance of T may defer its root: written in place, no SUC
 *  to make a word of. */
static inline bool defers(const R *r, const av_tmpl *T) {
    return r->defer && T->root_last && !T->sucop;
}

/*  A deferred instance of T at entry p, its nodes reserved: the body's
 *  other applications written, its root's spine left in the stack, the
 *  root's argument in entry p and each spine application's above it, the
 *  innermost highest.  False: out of memory for the stack, nothing
 *  written. */
static inline bool tmpl_defer(R *r, const av_tmpl *T, const uint32_t *args, size_t p,
                              uint32_t *curp) {
    av_arena *a = r->a;
    const uint32_t *ops = T->ops;
    uint32_t n = T->nops;
    if (!defer_room(r, p, (size_t)T->nvspine + 1)) return false;
    assert(a->tmpl_scratch_cap >= T->nops + T->nconsts);
    uint32_t *out = a->tmpl_scratch, *cv = out + n;
    for (uint32_t j = 0; j < T->nconsts; j++) cv[j] = a->tmpl_globals[T->consts[j]];
    const uint32_t *const base[3] = { cv, args, out };
#define OPND(o) (base[(o) >> 30][(o) & AV_PAYLOAD])
    const uint8_t *vs = T->vspine;
    av_node *nodes = a->nodes;
    uint32_t used = a->used;
    AV_ALWAYS(a->cap - used >= n - 1, "allocation past what was reserved");
    for (uint32_t i = 0; i + 1 < n; i++) {
        if (vs && vs[i]) continue;                  /* used by its parent alone */
        nodes[used] = (av_node){ OPND(ops[2 * i]), OPND(ops[2 * i + 1]) };
        out[i] = used++;
    }
    a->used = used;
    vpop(r, p + 1);
    defer_root(r, p, OPND(ops[2 * (n - 1) + 1]));
    size_t q = p + 1;
    uint32_t x = ops[2 * (n - 1)];
    while (x >> 30 == 2 && vs && vs[x & AV_PAYLOAD]) {
        uint32_t j = x & AV_PAYLOAD;
        r->stk[q++] = SK_MAKE(SK_VIRT, OPND(ops[2 * j + 1]));
        x = ops[2 * j];
    }
    assert(q == p + 1 + T->nvspine);
    r->nvirt += T->nvspine;
    r->top = q;
    *curp = OPND(x);
#undef OPND
    r->deferred++;
    return true;
}

/*  The most nodes one numeral operation builds.  Beyond it the
 *  operation runs its term, which builds its result lazily: a product
 *  nobody reads past its first successor should not cost its whole size. */
#define WORD_BUILD_MAX (1u << 20)

/*  Data jets: a constructor template at the head with its fields
 *  and continuations, and the continuation its index selects, applied to
 *  the fields, replaces the redex root: one step.  When that continuation
 *  is a template's key applied to exactly the arguments that, with the
 *  fields, it takes---a case branch, lifted with what it captured---that
 *  template is instantiated in the same step, fused.  Otherwise the redex
 *  root is rewritten in place, as S rewrites. */
typedef struct {
    uint32_t       field[AV_JET_ARITY_MAX];
    uint32_t       cont;                    /* the selected continuation */
    const av_tmpl *U;                       /* its template, when fused   */
    uint32_t       uarg[AV_JET_ARITY_MAX];
} disp;

/*  Read the dispatch at the top of the stack: fields, continuation, and
 *  whether it fuses.  Reads only; the indices hold until a collection. */
static inline void dispatch_fuse(const av_arena *a, av_ctor sh, disp *d);

static void dispatch_read(const R *r, av_ctor sh, disp *d) {
    const av_arena *a = r->a;
    unsigned m = sh.fields;
    for (unsigned j = 0; j < m; j++)
        d->field[j] = av_res(a, sarg(r, r->top - 1 - j));
    d->cont = av_res(a, sarg(r, r->top - 1 - m - sh.index));
    dispatch_fuse(a, sh, d);
}

/*  Whether the dispatch of d's fields and continuation fuses, and how. */
static inline __attribute__((always_inline))
void dispatch_fuse(const av_arena *a, av_ctor sh, disp *d) {
    unsigned m = sh.fields;
    /* the continuation's spine: a template key and what it captured.  Not
     * for a nullary constructor: its continuation, applied to nothing, is
     * the redex itself, and must be updated where it stands, as shared */
    d->U = NULL;
    if (m == 0) return;
    uint32_t c = d->cont, cap[AV_JET_ARITY_MAX];
    unsigned j = 0;
    while (av_tag(a, c) == AV_APP) {
        if (j == AV_JET_ARITY_MAX) return;
        cap[j++] = av_res(a, av_right(a, c));
        c = av_res(a, av_left(a, c));
    }
    if (av_tag(a, c) != AV_JET || (av_left(a, c) & AV_JET_WORD) ||
        !a->jets[AV_JET_ID(av_left(a, c))].tmpl)
        return;
    const av_tmpl *U = &a->tmpls[a->jets[AV_JET_ID(av_left(a, c))].tmpl - 1];
    if (U->k != j + m) return;
    for (unsigned i = 0; i < j; i++) d->uarg[i] = cap[j - 1 - i];      /* in order */
    for (unsigned i = 0; i < m; i++) d->uarg[j + i] = d->field[i];
    d->U = U;
}

/*  The dispatch's write over the redex root nd, its nodes reserved. */
static inline __attribute__((always_inline))
bool dispatch_write(R *r, av_ctor sh, const disp *d, uint32_t nd) {
    av_arena *a = r->a;
    if (d->U) {
        if (r->o->profile) profile_rewrote(r->o->profile, nd);
        uint32_t inst = tmpl_instance(a, d->U, d->uarg, nd);
        AV_ALWAYS(inst != AV_NONE, "allocation past what ensure() reserved");
        if (inst == AV_NONE) return false;
        SSTATS_INSTANCE(a, d->U, d->uarg, r->steps);
        r->fused++;
    } else if (sh.fields == 0) {
        arena_set(a, nd, (av_node){ (AV_IND << AV_TAG_SHIFT) | d->cont, 0 });
    } else {
        uint32_t t = d->cont;
        for (unsigned j = 0; j + 1 < sh.fields; j++) t = reserved_app(a, t, d->field[j]);
        if (r->o->profile) profile_rewrote(r->o->profile, nd);
        arena_set(a, nd, (av_node){ t, d->field[sh.fields - 1] });
    }
    return true;
}

/*  The dispatch d over the redex root at entry p, its nodes reserved: the
 *  head becomes its result.  Deferring, a fused template's instance or the
 *  continuation's application to the fields is left in the stack.  False:
 *  SIZE. */
static bool dispatch_put(R *r, av_ctor sh, const disp *d, size_t p, uint32_t *curp) {
    av_arena *a = r->a;
    if (!r->defer) {                                /* every entry real */
        uint32_t nd = r->stk[p];
        if (!dispatch_write(r, sh, d, nd)) return false;
        r->top = p;
        *curp = nd;
    } else if (d->U && defers(r, d->U)) {           /* fused, deferred */
        if (!tmpl_defer(r, d->U, d->uarg, p, curp)) return false;
        r->fused++;
    } else if (d->U) {                              /* fused, written */
        uint32_t into = SK_KIND(r->stk[p]) == SK_VIRT ? AV_NONE : SK_BODY(r->stk[p]);
        uint32_t inst = tmpl_instance(a, d->U, d->uarg, into);
        AV_ALWAYS(inst != AV_NONE, "allocation past what ensure() reserved");
        if (inst == AV_NONE) return false;
        r->fused++;
        undefer(r, p);
        vpop(r, p);
        r->top = p;
        *curp = inst;
    } else if (sh.fields == 0) {
        root_set(r, p, (av_node){ (AV_IND << AV_TAG_SHIFT) | d->cont, 0 }, curp);
    } else if (!defer_apply(r, p, d->cont, d->field, sh.fields, curp)) {
        return false;
    }
    return true;
}

/*  The dispatch: k = m + n arguments, the redex root stk[top-k]. */
static av_status dispatch(R *r, av_ctor sh, unsigned k, uint32_t *curp) {
    av_arena *a = r->a;
    disp d;
    dispatch_read(r, sh, &d);
    size_t need = d.U ? d.U->nops + d.U->nsuc : (sh.fields ? sh.fields - 1 : 0);
    uint64_t gcs = a->collections;
    if (!hensure(r, need, curp)) return AV_SIZE;    /* and the virtual entries' reserve */
    if (a->collections != gcs) dispatch_read(r, sh, &d);      /* the collection moved them */
    if (!dispatch_put(r, sh, &d, r->top - k, curp)) return AV_SIZE;
    r->steps++;
    r->dispatches++;
    return AV_WHNF;
}

/*  A list word at the head with its two continuations: CONS x rest z c is
 *  c x rest, a constructor's dispatch (fields x and rest, index 1 of 2),
 *  fused as one when c is a case branch's template.  The redex root at
 *  stk[top-2], prepared. */
static const av_ctor LIST_CTOR = { 2, 1, 2 };

static void list_read(const R *r, uint32_t w, disp *d) {
    const av_arena *a = r->a;
    d->field[0] = av_res(a, list_head(a, w));
    d->field[1] = av_res(a, list_rest(a, w));
    d->cont = av_res(a, sarg(r, r->top - 2));
    dispatch_fuse(a, LIST_CTOR, d);
}

static av_status list_dispatch(R *r, uint32_t *curp) {
    av_arena *a = r->a;
    disp d;
    list_read(r, *curp, &d);
    size_t need = d.U ? d.U->nops + d.U->nsuc : 1;
    uint64_t gcs = a->collections;
    if (!hensure(r, need, curp)) return AV_SIZE;
    if (a->collections != gcs) list_read(r, *curp, &d);      /* the collection moved them */
    if (!dispatch_put(r, LIST_CTOR, &d, r->top - 2, curp)) return AV_SIZE;
    r->steps++;
    r->dispatches++;
    return AV_WHNF;
}

/*  A numeral operation at the head with its k operands, the two
 *  numerals first: 1 fired, both being held already (K or words), the
 *  redex root now its result; 0 declined, to run its term; -1 SIZE. */
static int list_fire(R *r, unsigned op, unsigned k, uint32_t *curp);

static int word_fire(R *r, unsigned op, unsigned k, uint32_t *curp) {
    if (av_wop_list(op)) return list_fire(r, op, k, curp);
    av_arena *a = r->a;
    uint32_t m, n;
    if (!av_numeral(a, sarg(r, r->top - 1), &m) || !av_numeral(a, sarg(r, r->top - 2), &n))
        return 0;
    uint64_t v = 0, need = 0;
    if (op == AV_WOP_ADD) { v = (uint64_t)m + n; need = 2 * (uint64_t)n; }
    if (op == AV_WOP_MUL) { v = (uint64_t)m * n; need = 2 * v; }
    /* by zero, the quotient is 0 and the remainder m, as skijack's are */
    if (op == AV_WOP_DIV) { v = n ? m / n : 0; need = 2 * v; }
    if (op == AV_WOP_REM) { v = n ? m % n : m; need = 2 * v; }
    if (v > AV_WORD_MAX || need > WORD_BUILD_MAX) return 0;
    if (need && !hensure(r, (size_t)need, curp)) return -1;
    uint32_t x = av_res(a, sarg(r, r->top - 1));                 /* m: reread */
    switch (op) {
    case AV_WOP_ADD:
        for (uint32_t i = 0; i < n; i++) x = word_succ(a, x);
        break;
    case AV_WOP_SUB:
        for (uint32_t i = 0; i < n && x != AV_NODE_K; i++) x = word_pred(a, x);
        break;
    case AV_WOP_MUL:
    case AV_WOP_DIV:
    case AV_WOP_REM:
        x = AV_NODE_K;
        for (uint64_t i = 0; i < v; i++) x = word_succ(a, x);
        break;
    case AV_WOP_IFEQ:
        x = av_res(a, sarg(r, r->top - (m == n ? 3 : 4)));
        break;
    case AV_WOP_IFLE:
        x = av_res(a, sarg(r, r->top - (m <= n ? 3 : 4)));
        break;
    default:
        return 0;
    }
    AV_ALWAYS(x != AV_NONE, "allocation past what ensure() reserved");
    if (x == AV_NONE) return -1;
    root_set(r, r->top - k, (av_node){ (AV_IND << AV_TAG_SHIFT) | x, 0 }, curp);
    r->steps++;
    r->word_ops++;
    return 1;
}

/*  The first m cells of the list word src, rebuilt as list words before
 *  tail, a list held of len tail_n: 3 m reserved nodes, built front to
 *  back, each cell's rest written once the next exists. */
static uint32_t list_prefix(av_arena *a, uint32_t src, uint32_t m, uint32_t tail, uint32_t tail_n) {
    uint32_t first = tail, prev_t = AV_NONE, prev_c = AV_NONE;
    for (uint32_t j = 0; j < m; j++) {
        uint32_t c = arena_app_reserved(a, a->word_cons, list_head(a, src));
        uint32_t t = arena_app_reserved(a, c, AV_NODE_K);
        uint32_t w = arena_app_reserved(a, t, t);
        if (w == AV_NONE) return AV_NONE;
        arena_set(a, w, (av_node){ (AV_JET << AV_TAG_SHIFT) | AV_JET_WORD | AV_JET_LIST |
                                   (m - j + tail_n), t });
        if (prev_t == AV_NONE) first = w;
        else arena_set(a, prev_t, (av_node){ prev_c, w });
        prev_t = t;
        prev_c = c;
        src = av_res(a, list_rest(a, src));
    }
    if (prev_t != AV_NONE) arena_set(a, prev_t, (av_node){ prev_c, tail });
    return first;
}

/*  A list operation at the head with its k operands, the list first: 1
 *  fired, the operands being held already (lists K or list words, an
 *  index K or a word), the redex root now its result; 0 declined, to run
 *  its term; -1 SIZE.  length builds its numeral, take and append their
 *  cells; at and drop walk to theirs. */
static int list_fire(R *r, unsigned op, unsigned k, uint32_t *curp) {
    av_arena *a = r->a;
    uint32_t n, i = 0, n2 = 0;
    if (!av_list(a, sarg(r, r->top - 1), &n)) return 0;
    if (op == AV_WOP_AT || op == AV_WOP_TAKE || op == AV_WOP_DROP) {
        if (!av_numeral(a, sarg(r, r->top - 2), &i)) return 0;
    } else if (op == AV_WOP_APP) {
        if (!av_list(a, sarg(r, r->top - 2), &n2)) return 0;
    } else if (op != AV_WOP_LEN) {
        return 0;
    }
    uint32_t m = i < n ? i : n;
    uint64_t need = op == AV_WOP_LEN ? 2 * (uint64_t)n
                  : op == AV_WOP_TAKE && m < n ? 3 * (uint64_t)m
                  : op == AV_WOP_APP && n && n2 ? 3 * (uint64_t)n : 0;
    if (op == AV_WOP_APP && (uint64_t)n + n2 > AV_WORD_MAX) return 0;
    if (need > WORD_BUILD_MAX) return 0;
    if (need && !hensure(r, (size_t)need, curp)) return -1;
    uint32_t l = av_res(a, sarg(r, r->top - 1)), x = l;              /* reread */
    switch (op) {
    case AV_WOP_LEN:
        x = AV_NODE_K;
        for (uint32_t j = 0; j < n; j++) x = word_succ(a, x);
        break;
    case AV_WOP_AT:
    case AV_WOP_DROP:
        for (uint32_t j = 0; j < m; j++) x = av_res(a, list_rest(a, x));
        if (op == AV_WOP_AT)
            x = i < n ? av_res(a, list_head(a, x)) : av_res(a, sarg(r, r->top - 3));
        break;
    case AV_WOP_TAKE:
        x = m == n ? l : list_prefix(a, l, m, AV_NODE_K, 0);
        break;
    case AV_WOP_APP: {
        uint32_t r2 = av_res(a, sarg(r, r->top - 2));
        x = n == 0 ? r2 : n2 == 0 ? l : list_prefix(a, l, n, r2, n2);
        break;
    }
    default:
        return 0;
    }
    AV_ALWAYS(x != AV_NONE, "allocation past what ensure() reserved");
    if (x == AV_NONE) return -1;
    root_set(r, r->top - k, (av_node){ (AV_IND << AV_TAG_SHIFT) | x, 0 }, curp);
    r->steps++;
    r->list_ops++;
    return 1;
}

/*  Whether jet node jn of Poseidon2 jet id has P's term: checked against
 *  the registered term, node for node, unless jn was found so since the
 *  last collection and stands as it stood then.  A node found otherwise is
 *  unbound, an indirection to its own term.  A jet node's term is written
 *  only to a reduct, so a term once found P's stays convertible to it. */
static bool p2_ok(R *r, uint32_t jn, uint32_t id) {
    av_arena *a = r->a;
    av_node v = a->nodes[jn];
    if (r->p2_gen == a->collections + 1 && r->p2_node == jn && r->p2_seen.l == v.l && r->p2_seen.r == v.r)
        return true;
    if (!p2_same(a, v.r, id)) {
        arena_set(a, jn, (av_node){ (AV_IND << AV_TAG_SHIFT) | v.r, 0 });
        r->p2_unbound++;
        return false;
    }
    r->p2_seen = v;
    r->p2_node = jn;
    r->p2_gen = a->collections + 1;
    return true;
}

/*  Down a chain P (P (… (P x))) from the argument t, into r->p2c: each
 *  call and its jet node, outermost first, and the innermost argument's
 *  state in s.  The number of calls; 0 when t is no such chain, or a state
 *  itself: some call's head not a Poseidon2 jet node, or the innermost
 *  argument not a state.  SIZE_MAX: out of memory.  Reads only; the heap
 *  is acyclic, so the walk ends. */
static size_t p2_walk(R *r, uint32_t t, uint32_t s[16]) {
    const av_arena *a = r->a;
    size_t m = 0;
    for (;;) {
        if (av_p2_state_read(a, t, s)) return m;
        t = av_res(a, t);
        if (av_tag(a, t) != AV_APP) return 0;
        uint32_t f = av_res(a, av_left(a, t));
        if (av_tag(a, f) != AV_JET || (av_left(a, f) & AV_JET_WORD) ||
            !a->jets[AV_JET_ID(av_left(a, f))].p2)
            return 0;
        if (!grow(&r->p2c, &r->p2cap, 2 * m + 2)) return SIZE_MAX;
        r->p2c[2 * m] = t;
        r->p2c[2 * m + 1] = f;
        m++;
        t = av_right(a, t);
    }
}

/*  The calls of a chain under the redex root, fired innermost first, as
 *  lazy reduction would fire each once the call outside it forced it: each
 *  rewritten in place to its permuted state, one step each.  One walk
 *  serves every call the free nodes and the fuel cover; the next pass
 *  walks again only after a collection or when fuel runs out, so a chain
 *  of m calls costs O(m) visits a collection, not O(m) a call.  A jet
 *  node not P's term is unbound, and the calls outside it are left.  1
 *  some done, the head and stack as they were; 0 no chain; -1 SIZE. */
static int p2_chain(R *r, uint32_t *curp) {
    av_arena *a = r->a;
    uint32_t s[16];
    for (;;) {
        size_t m = p2_walk(r, av_right(a, r->stk[r->top - 1]), s);
        if (m == SIZE_MAX) return -1;
        if (m == 0) return 0;
        size_t fuel = r->o->max_steps > r->steps ? (size_t)(r->o->max_steps - r->steps) : 0;
        if (fuel == 0) return 1;                    /* the loop stops at FUEL */
        size_t avail = a->cap - a->used, room = avail > r->nvirt ? (avail - r->nvirt) / P2_STATE_NODES : 0;
        if (room == 0) {
            /* a collection moves the nodes walked: walk again */
            if (!hensure(r, P2_STATE_NODES, curp)) return -1;
            continue;
        }
        size_t k = m < fuel ? m : fuel;
        if (k > room) k = room;
        for (size_t i = m; i-- > m - k;) {
            uint32_t c = r->p2c[2 * i], jn = r->p2c[2 * i + 1];
            if (!p2_ok(r, jn, AV_JET_ID(av_left(a, jn)))) return 1;
            av_p2_permute(s);                   /* the next call's argument, built */
            uint32_t x = p2_state_build(a, s);
            if (r->o->profile) profile_rewrote(r->o->profile, c);
            arena_set(a, c, (av_node){ (AV_IND << AV_TAG_SHIFT) | x, 0 });
            r->steps++;
            r->p2_calls++;
        }
        return 1;
    }
}

/*  The Poseidon2 jet, its jet node *curp, of jet id, at the head
 *  with its argument: 1 fired, the redex root now the permuted state; 3 an
 *  inner call of a chain fired or unbound, the head and stack as they
 *  were, for the next pass to take the next; 0 declined, the argument
 *  neither a state as it stands nor such a chain, to run P's term; 2
 *  unbound, the node's term not P's, the node now an indirection to it;
 *  -1 SIZE.  P_specN is the licence: P applied to stateN vs, sixteen
 *  31-bit elements, reduces to stateN (permute vs). */
static int p2_fire(R *r, uint32_t id, uint32_t *curp) {
    av_arena *a = r->a;
    uint32_t s[16];
    /* the term checked first, at every fire and every decline: a jet node
     * may have been made after av_p2_bind, in a copy of another jet's
     * term; a decline runs the registered term, not the node's; and a
     * chain is fired only under a P */
    if (!p2_ok(r, *curp, id)) return 2;
    if (!av_p2_state_read(a, av_right(a, r->stk[r->top - 1]), s)) {
        int pc = p2_chain(r, curp);
        if (pc) return pc < 0 ? -1 : 3;
        r->p2_declines++;
        return 0;
    }
    av_p2_permute(s);
    if (!ensure(r, P2_STATE_NODES)) return -1;
    uint32_t x = p2_state_build(a, s);
    uint32_t nd = r->stk[r->top - 1];               /* the redex root, reread */
    if (r->o->profile) profile_rewrote(r->o->profile, nd);
    arena_set(a, nd, (av_node){ (AV_IND << AV_TAG_SHIFT) | x, 0 });
    r->top -= 1;
    *curp = nd;
    r->steps++;
    r->p2_calls++;
    return 1;
}

/*  A case joined to its instance.  T's body is its formal h applied to p
 *  operands (T->case_h, T->case_p), and h arrived as a value the step after
 *  the instance would dispatch on: a constructor with its fields and p
 *  continuations, or, with two, a word or zero (K).  The instance writes
 *  the body's other applications, not its spine or root, and the dispatch
 *  writes over the redex root nd what it would have written there after the
 *  instance: the same graph but for the spine, the same two steps, each
 *  counted as before.  False, nothing written, when h is no such value or
 *  the free nodes do not cover both writes without a collection; the caller
 *  then instantiates as before. */
enum { CJ_NONE, CJ_CTOR, CJ_WORD, CJ_ZERO, CJ_LIST };

/*  Both writes of a join from the free nodes: the instance's T->nops +
 *  T->nsuc at most, the dispatch's a fused template's (at most twice the
 *  scratch every template fits) or its fields' applications.  The caller
 *  reserves them before it asks, so whether a case joins never depends on
 *  how full the arena is. */
static inline size_t join_need(const av_arena *a, const av_tmpl *T) {
    return (size_t)T->nops + T->nsuc + 2 * (size_t)a->tmpl_scratch_cap + AV_JET_ARITY_MAX;
}

/*  Which value, if any, T's case meets its formal as: CJ_NONE, or the kind
 *  case_join takes.  Inline: it is asked at nearly every instance of a
 *  case, and most answers are no. */
static inline __attribute__((always_inline))
unsigned case_kind(const av_arena *a, const av_tmpl *T, const uint32_t *args) {
    uint32_t h = av_res(a, args[T->case_h - 1]);
    unsigned m = 0, p = T->case_p;
    while (av_tag(a, h) == AV_APP) {
        if (++m > AV_JET_ARITY_MAX) return CJ_NONE;
        h = av_res(a, av_left(a, h));
    }
    uint32_t l = a->nodes[h].l;
    if (l >> AV_TAG_SHIFT == AV_JET) {
        if (l & AV_JET_WORD)
            return m == 0 && p == 2 ? (l & AV_JET_LIST ? CJ_LIST : CJ_WORD) : CJ_NONE;
        uint32_t t = a->jets[AV_JET_ID(l)].tmpl;
        if (!t) return CJ_NONE;
        av_ctor sh = a->tmpls[t - 1].ctor;
        return av_ctor_is(sh) && sh.fields == m && sh.count == p ? CJ_CTOR : CJ_NONE;
    }
    return h == AV_NODE_K && m == 0 && p == 2 ? CJ_ZERO : CJ_NONE;
}

__attribute__((noinline))
static int case_join(R *r, const av_tmpl *T, const uint32_t *args, size_t at, unsigned kind,
                     uint32_t *curp) {
    av_arena *a = r->a;
    unsigned p = T->case_p;
    uint32_t h = av_res(a, args[T->case_h - 1]);
    uint32_t sp[AV_JET_ARITY_MAX];      /* its arguments, outermost first */
    unsigned m = 0;
    while (av_tag(a, h) == AV_APP) {
        sp[m++] = av_right(a, h);
        h = av_res(a, av_left(a, h));
    }
    av_ctor sh = { 0, 0, 0 };
    if (kind == CJ_CTOR) sh = a->tmpls[a->jets[AV_JET_ID(av_left(a, h))].tmpl - 1].ctor;
    if (a->cap - a->used < join_need(a, T)) return 0;

    /* the instance, its spine and root left out */
    uint32_t *out = a->tmpl_scratch, *cv = out + T->nops;
    for (uint32_t j = 0; j < T->nconsts; j++) cv[j] = a->tmpl_globals[T->consts[j]];
    const uint32_t *const base[3] = { cv, args, out };
#define OPND(x) (base[(x) >> 30][(x) & AV_PAYLOAD])
    const uint32_t *ops = T->ops;
    for (uint32_t i = 0; i < T->nops; i++) {
        if (T->case_spine[i]) continue;
        uint32_t f = OPND(ops[2 * i]), x = OPND(ops[2 * i + 1]), w;
        out[i] = T->sucop && T->sucop[i] && av_numeral(a, x, &w) && w < AV_WORD_MAX
               ? word_succ(a, x) : arena_app_reserved(a, f, x);
    }
    /* the p operands h is applied to, in order, from the root down */
    uint32_t c[AV_JET_ARITY_MAX];
    uint32_t j = T->nops - 1;
    for (unsigned q = p; q-- > 0;) {
        c[q] = av_res(a, OPND(ops[2 * j + 1]));
        if (q) j = ops[2 * j] & AV_PAYLOAD;
    }
#undef OPND
    r->steps++;                                 /* the instance */
    r->tmpl_calls++;
    if (kind == CJ_ZERO) {                      /* K z s -> z */
        root_set(r, at, (av_node){ (AV_IND << AV_TAG_SHIFT) | c[0], 0 }, curp);
    } else if (kind == CJ_WORD) {               /* W n z s -> s (W (n-1)) */
        root_set(r, at, (av_node){ c[1], word_pred(a, h) }, curp);
        r->dispatches++;
    } else if (kind == CJ_LIST) {               /* L n z c -> c x (L (n-1)), fused or not */
        disp d;
        d.field[0] = av_res(a, list_head(a, h));
        d.field[1] = av_res(a, list_rest(a, h));
        d.cont = c[1];
        dispatch_fuse(a, LIST_CTOR, &d);
        if (!dispatch_put(r, LIST_CTOR, &d, at, curp)) return -1;     /* SIZE */
        r->dispatches++;
    } else {
        disp d;
        for (unsigned i = 0; i < m; i++) d.field[i] = av_res(a, sp[m - 1 - i]);
        d.cont = c[sh.index];
        dispatch_fuse(a, sh, &d);
        if (!dispatch_put(r, sh, &d, at, curp)) return -1;     /* SIZE */
        r->dispatches++;
    }
    r->steps++;                                 /* the dispatch */
    r->joins++;
    return 1;
}

/*  Reduce r->cur to weak head normal form in place.  The spine lives on
 *  r->stk above its entry height, which is restored on success.  D is
 *  r->defer, a constant in each of the two copies whnf_share makes, so a
 *  run that defers nothing reads and writes the stack as plain nodes.
 */

/*  The stack's accessors, every entry real when D is false. */
static inline uint32_t ssarg(const R *r, const bool D, size_t i) {
    return D ? sarg(r, i) : av_right(r->a, r->stk[i]);
}

static inline void sroot_set(R *r, const bool D, size_t p, av_node v, uint32_t *curp) {
    if (D) {
        root_set(r, p, v, curp);
        return;
    }
    arena_set(r->a, r->stk[p], v);
    r->top = p;
    *curp = r->stk[p];
}

static inline bool sprepare(R *r, const bool D, size_t p, uint32_t *curp) {
    return !D || prepare(r, p, curp);
}

static inline __attribute__((always_inline)) av_status whnf_share_d(R *r, const bool D) {
    av_arena *a = r->a;
    const av_opts *o = r->o;
    size_t bottom = r->top;
    uint32_t cur = r->cur;
    assert(r->ndstk == 0 && r->nvirt == 0);

    for (;;) {
        cur = av_res(a, cur);
        if (av_tag(a, cur) == AV_APP) {
            SSTATS_FORCE(a, cur, r->steps);
            if (!push(r, cur)) return stop(r, bottom, cur, AV_SIZE);
            /* path compression: point past an indirection for good, or
             * chains grow by one per contraction and walks go quadratic */
            uint32_t l = av_left(a, cur), rl = av_res(a, l);
            if (rl != l) arena_set(a, cur, (av_node){ rl, a->nodes[cur].r });
            cur = rl;
            continue;
        }
        if (interrupted(r)) return stop(r, bottom, cur, AV_INTERRUPTED);
        if (r->steps >= o->max_steps) return stop(r, bottom, cur, AV_FUEL);
        if (av_tag(a, cur) == AV_JET && (av_left(a, cur) & AV_JET_LIST)) {
            /* a list word: with its two continuations, L n z c is c x
             * (L (n-1)), over the redex root, x its head; short of them,
             * a value---but, making the normal form, its term CONS x
             * (L (n-1)), fresh so the word's own stays whole */
            if (r->top - bottom < 2) {
                if (!r->normal) break;
                r->jnode = cur;
                if (!ensure(r, 2 + r->nvirt)) return stop(r, bottom, r->jnode, AV_SIZE);
                cur = r->jnode;
                r->jnode = AV_NONE;
                uint32_t t = reserved_app(a, reserved_app(a, a->word_cons, list_head(a, cur)),
                                          list_rest(a, cur));
                arena_set(a, cur, (av_node){ (AV_IND << AV_TAG_SHIFT) | t, 0 });
                cur = t;
                continue;
            }
            if (!sprepare(r, D, r->top - 2, &cur)) return stop(r, bottom, cur, AV_SIZE);
            av_status ls = list_dispatch(r, &cur);
            if (ls != AV_WHNF) return stop(r, bottom, cur, ls);
            continue;
        }
        if (av_tag(a, cur) == AV_JET && (av_left(a, cur) & AV_JET_WORD)) {
            /* a word: with its two continuations, W n z s is s (W (n-1)),
             * written over the redex root; short of them, a value---but,
             * making the normal form, its term SUC (W (n-1)), a redex,
             * fresh so the word's own stays whole */
            if (r->top - bottom < 2) {
                if (!r->normal) break;
                r->jnode = cur;
                if (!ensure(r, 1 + r->nvirt)) return stop(r, bottom, r->jnode, AV_SIZE);
                cur = r->jnode;
                r->jnode = AV_NONE;
                uint32_t t = reserved_app(a, a->word_suc, word_pred(a, cur));
                arena_set(a, cur, (av_node){ (AV_IND << AV_TAG_SHIFT) | t, 0 });
                cur = t;
                continue;
            }
            size_t p = r->top - 2;
            if (!sprepare(r, D, p, &cur)) return stop(r, bottom, cur, AV_SIZE);
            uint32_t sk = av_res(a, ssarg(r, D, p));
            if (o->profile) profile_rewrote(o->profile, r->stk[p]);
            sroot_set(r, D, p, (av_node){ sk, word_pred(a, cur) }, &cur);
            r->steps++;
            r->dispatches++;
            continue;
        }
        if (av_tag(a, cur) == AV_JET) {
            uint32_t id = AV_JET_ID(av_left(a, cur));
            av_status ist;
            uint32_t iout;
            /* the steps below that read the stack as nodes: everything
             * deferred written first */
            if (interp_role(a, id) && !materialize(r, bottom, &cur))
                return stop(r, bottom, cur, AV_SIZE);
            int ir = interp_role(a, id) ? try_interp(r, &cur, r->top - bottom, &ist, &iout) : 0;
            if (ir < 0) return stop(r, bottom, cur, ist);
            if (ir > 0) {                       /* the redex root becomes it */
                unsigned k = fire_nargs(r, id);
                uint32_t n = r->stk[r->top - k];     /* reread: the fire may collect */
                arena_set(a, n, (av_node){ (AV_IND << AV_TAG_SHIFT) | iout, 0 });
                r->top -= k;
                cur = n;
                continue;
            }
            if (o->fix && a->jets[id].fix) {
                /* Y: with its argument, Y g is rewritten to g (Y g), a
                 * fresh Y g, one step---convertible, not a reduct, and
                 * acyclic; short of it, its term */
                if (r->top - bottom >= 1) {
                    size_t p = r->top - 1;                  /* the redex root */
                    if (!hensure(r, 1, &cur)) return stop(r, bottom, cur, AV_SIZE);
                    uint32_t g = ssarg(r, D, p);
                    bool real = SK_KIND(r->stk[p]) == SK_REAL;
                    uint32_t yf = real ? av_left(a, r->stk[p]) : cur;
                    if (o->fix_shared) {
                        /* --memory: every unfolding of g passes on one
                         * Y g, y0, never written, and every Y g of g leads
                         * to one unfolding u0 = g y0, written as any node
                         * is: no unfolding chains to the next, and u0's
                         * value is made once.  The link y0 -> u0 is this
                         * table's, not the graph's, which stays acyclic;
                         * following it is a step, so a Y g that needs
                         * itself runs out of fuel, as SKI does. */
                        uint32_t gr = av_res(a, g), y0, u0;
                        uint64_t v;
                        bool have = nmap_get(&r->ymemo, gr, &v) && v != YM_NONE;
                        if (real && p == bottom && (!have || r->stk[p] == (uint32_t)(v >> 32))) {
                            /* the node this call reduces, which its caller
                             * reads: unfolded in place as --fix does, and
                             * never shared again, being written */
                            if (have && !nmap_put(&r->ymemo, gr, YM_NONE))
                                return stop(r, bottom, cur, AV_SIZE);
                            uint32_t y = reserved_app(a, yf, g);
                            sroot_set(r, D, p, (av_node){ gr, y }, &cur);
                            r->steps++;
                            r->fix_calls++;
                            continue;
                        }
                        if (have) {
                            y0 = (uint32_t)(v >> 32);
                            u0 = (uint32_t)v;
                        } else {
                            if (!hensure(r, 2, &cur)) return stop(r, bottom, cur, AV_SIZE);
                            g = ssarg(r, D, p);             /* reread */
                            gr = av_res(a, g);
                            yf = real ? av_left(a, r->stk[p]) : cur;
                            y0 = real ? r->stk[p] : reserved_app(a, yf, g);
                            u0 = reserved_app(a, gr, y0);
                            if (!nmap_put(&r->ymemo, gr, (uint64_t)y0 << 32 | u0))
                                return stop(r, bottom, cur, AV_SIZE);
                        }
                        if (real && r->stk[p] == y0) {
                            r->top = p;                     /* y0 stays Y g */
                            cur = u0;
                        } else {
                            if (o->profile) profile_rewrote(o->profile, r->stk[p]);
                            sroot_set(r, D, p, (av_node){ (AV_IND << AV_TAG_SHIFT) | u0, 0 }, &cur);
                        }
                        r->steps++;
                        r->fix_calls++;
                        continue;
                    }
                    uint32_t y = reserved_app(a, yf, g);
                    if (o->profile) profile_rewrote(o->profile, r->stk[p]);
                    sroot_set(r, D, p, (av_node){ av_res(a, g), y }, &cur);
                    r->steps++;
                    r->fix_calls++;
                    continue;
                }
                if (!(av_left(a, cur) & AV_JET_SHARED)) {
                    cur = av_right(a, cur);
                    continue;
                }
            }
            if (o->p2 && a->jets[id].p2) {
                /* the Poseidon2 jet: natively on a state as it
                 * stands; else a fresh copy of P's term, so the node's own
                 * term is never written and stays P's for the next call */
                if (r->top - bottom >= 1) {
                    if (!materialize(r, bottom, &cur)) return stop(r, bottom, cur, AV_SIZE);
                    int pf = p2_fire(r, id, &cur);
                    if (pf < 0) return stop(r, bottom, cur, AV_SIZE);
                    if (pf > 0) continue;       /* fired, or unbound */
                } else if (!p2_ok(r, cur, id)) {
                    continue;                   /* bare, as a normal form reaches it: its own term */
                }
                r->jnode = cur;
                if (!ensure(r, a->jets[id].term_nodes + r->nvirt))
                    return stop(r, bottom, r->jnode, AV_SIZE);
                r->jnode = AV_NONE;
                cur = jet_term_copy(a, id);
                AV_ALWAYS(cur != AV_NONE, "allocation past what ensure() reserved");
                if (cur == AV_NONE) return AV_SIZE;
                continue;
            }
            if (o->data && a->jets[id].word_op) {
                /* a numeral operation: natively on words; else its
                 * term, the node kept for the next call */
                unsigned op = a->jets[id].word_op, k = av_wop_operands(op);
                if (r->top - bottom >= k) {
                    if (!sprepare(r, D, r->top - k, &cur)) return stop(r, bottom, cur, AV_SIZE);
                    int wf = word_fire(r, op, k, &cur);
                    if (wf < 0) return stop(r, bottom, cur, AV_SIZE);
                    if (wf > 0) continue;
                }
                if (!(av_left(a, cur) & AV_JET_SHARED)) {
                    cur = av_right(a, cur);
                    continue;
                }
            }
            if (o->templates && a->jets[id].tmpl) {
                /* a supercombinator template: its body over the
                 * arguments, one step; short of them, its term, the node
                 * left a root for the next full application */
                const av_tmpl *T = &a->tmpls[a->jets[id].tmpl - 1];
                if (o->data && av_ctor_is(T->ctor) && r->top - bottom >= T->k) {
                    /* a constructor with every argument */
                    if (!sprepare(r, D, r->top - T->k, &cur)) return stop(r, bottom, cur, AV_SIZE);
                    av_status ds = dispatch(r, T->ctor, T->k, &cur);
                    if (ds != AV_WHNF) return stop(r, bottom, cur, ds);
                    continue;
                }
                if (r->top - bottom >= T->k) {
                    if (o->jetstats) jetstats_fire(o->jetstats, cur, id);
                    size_t p = r->top - T->k;               /* the redex root */
                    if (!sprepare(r, D, p, &cur)) return stop(r, bottom, cur, AV_SIZE);
                    bool joins = o->data && T->case_p && !o->no_join && !o->profile &&
                                 !o->jetstats && o->max_steps - r->steps >= 2;
                    if (!hensure(r, joins ? join_need(a, T) : T->nops + T->nsuc, &cur))
                        return stop(r, bottom, cur, AV_SIZE);
                    uint32_t args[AV_JET_ARITY_MAX];
                    for (unsigned i = 0; i < T->k; i++)
                        args[i] = av_res(a, ssarg(r, D, r->top - 1 - i));
                    unsigned ck;
                    if (joins && (ck = case_kind(a, T, args)) != CJ_NONE) {
                        int cj = case_join(r, T, args, p, ck, &cur);
                        if (cj < 0) return stop(r, bottom, cur, AV_SIZE);
                        if (cj > 0) continue;
                    }
                    /* a virtual root has no node to write an undeferred
                     * instance over */
                    uint32_t n = SK_KIND(r->stk[p]) == SK_VIRT ? AV_NONE : SK_BODY(r->stk[p]);
                    if (defers(r, T)) {
                        if (!tmpl_defer(r, T, args, p, &cur)) return stop(r, bottom, cur, AV_SIZE);
                    } else {
                        if (o->profile) profile_rewrote(o->profile, n);
                        uint32_t inst = tmpl_instance(a, T, args, n);
                        AV_ALWAYS(inst != AV_NONE, "allocation past what ensure() reserved");
                        if (inst == AV_NONE) return stop(r, bottom, cur, AV_SIZE);
                        SSTATS_INSTANCE(a, T, args, r->steps);
                        undefer(r, p);
                        vpop(r, p);
                        r->top = p;
                        cur = inst;
                    }
                    r->steps++;
                    r->tmpl_calls++;
                    continue;
                }
                if (!(av_left(a, cur) & AV_JET_SHARED) &&
                    !(a->jets[id].residual_ok && fires(r, id, r->top - bottom))) {
                    if (o->jetstats) jetstats_miss(o->jetstats, id);
                    cur = av_right(a, cur);
                    continue;
                }
            }
            if (!(a->jets[id].residual_ok && fires(r, id, r->top - bottom))) {
                if (o->jetstats) {
                    if (o->jets && a->jets[id].residual_ok && r->top - bottom < a->jets[id].arity)
                        jetstats_miss(o->jetstats, id);
                    jetstats_demote(o->jetstats, id, (av_left(a, cur) & AV_JET_SHARED) != 0);
                }
                /* Unwrapped, and demoted: this run may write inside the
                 * term from here on, so the jet node becomes an
                 * indirection to a term it owns---a private copy when
                 * the term is the dashboard's---and no jet node's term
                 * is ever written. */
                uint32_t inner = av_right(a, cur);
                if (av_left(a, cur) & AV_JET_SHARED) {
                    r->jnode = cur;
                    if (!ensure(r, a->jets[id].term_nodes + r->nvirt))
                    return stop(r, bottom, r->jnode, AV_SIZE);
                    cur = r->jnode;
                    r->jnode = AV_NONE;
                    inner = jet_term_copy(a, id);
                    AV_ALWAYS(inner != AV_NONE, "allocation past what ensure() reserved");
                    if (inner == AV_NONE) return stop(r, bottom, cur, AV_SIZE);
                }
                arena_set(a, cur, (av_node){ (AV_IND << AV_TAG_SHIFT) | inner, 0 });
                cur = inner;
                continue;
            }
            /* a residual jet fires: everything deferred written first */
            if (!materialize(r, bottom, &cur)) return stop(r, bottom, cur, AV_SIZE);
            unsigned k = a->jets[id].arity;
            uint32_t args[AV_JET_ARITY_MAX];
            if (o->jet_check && (r->jet_calls + 1) % o->jet_check == 0) {
                for (unsigned i = 0; i < k; i++)
                    args[i] = av_res(a, av_right(a, r->stk[r->top - 1 - i]));
                if (!check_fire(r, cur, id, args)) {
                    r->jet_fault = true;
                    return AV_INTERRUPTED;
                }
            }
            if (!ensure(r, a->jets[id].nodes)) return AV_SIZE;
            for (unsigned i = 0; i < k; i++)
                args[i] = av_res(a, av_right(a, r->stk[r->top - 1 - i]));
            if (o->jetstats) jetstats_fire(o->jetstats, cur, id);
            uint32_t inst = jet_instance(a, id, args, true);
            AV_ALWAYS(inst != AV_NONE, "allocation past what ensure() reserved");
            if (inst == AV_NONE) return AV_SIZE;
            uint32_t n = r->stk[r->top - k];    /* the redex root */
            arena_set(a, n, (av_node){ (AV_IND << AV_TAG_SHIFT) | inst, 0 });
            r->top -= k;
            cur = n;
            r->steps += a->jets[id].cost;
            r->jet_steps += a->jets[id].cost;
            r->jet_calls++;
            continue;
        }
        ski_leaf c = av_right(a, cur);
        unsigned k = ski_arity(c);
        if (k == 0 || r->top - bottom < k) break;

        if (o->profile)                         /* S f, S f g; K x; I x */
            profile_charge(o->profile, r->stk + r->top, c == SKI_S ? 2 : 1, c);
        size_t p = r->top - k;                  /* the redex root */
        if (!sprepare(r, D, p, &cur)) return stop(r, bottom, cur, AV_SIZE);
        if (c == SKI_S) {                       /* S f g x -> f x (g x) */
            if (!hensure(r, 2, &cur)) return stop(r, bottom, cur, AV_SIZE);
            uint32_t f = av_res(a, ssarg(r, D, r->top - 1));
            uint32_t g = av_res(a, ssarg(r, D, r->top - 2));
            uint32_t x = av_res(a, ssarg(r, D, p));
            uint32_t fx = reserved_app(a, f, x);
            uint32_t gx = reserved_app(a, g, x);
            if (o->profile) profile_rewrote(o->profile, r->stk[p]);
            sroot_set(r, D, p, (av_node){ fx, gx }, &cur);
        } else {                                /* K x y -> x;  I x -> x */
            uint32_t x = av_res(a, ssarg(r, D, r->top - 1));
            if (o->profile) profile_rewrote(o->profile, r->stk[p]);
            sroot_set(r, D, p, (av_node){ (AV_IND << AV_TAG_SHIFT) | x, 0 }, &cur);
        }
        r->steps++;
    }
    /* a weak head normal form: the value the deferred roots stand for
     * written, so the graph shares it */
    if (!materialize(r, bottom, &cur)) return AV_SIZE;
    r->top = bottom;
    return AV_WHNF;
}

static av_status whnf_share(R *r) {
    return r->defer ? whnf_share_d(r, true) : whnf_share_d(r, false);
}

/*  Whether t's head is a word. */
static bool word_head(const av_arena *a, uint32_t t) {
    t = av_res(a, t);
    while (av_tag(a, t) == AV_APP) t = av_res(a, av_left(a, t));
    return av_is_word(a, t);
}

static av_status run_share(R *r) {
    const av_arena *a = r->a;
    r->top = 0;
    r->cur = r->root;
    av_status s = whnf_share(r);
    if (s == AV_WHNF && r->o->whnf_only && word_head(a, r->root)) {
        /* a word at the head: the state reported is its term's weak head
         * normal form, the one the unjetted run reaches */
        r->normal = true;
        r->cur = r->root;
        s = whnf_share(r);
    }
    if (s != AV_WHNF || r->o->whnf_only) return s;

    /* normalize every argument of every spine, left to right, each shared
     * node once */
    r->normal = true;
    r->nwork = 0;
    if (!grow(&r->work, &r->workcap, 1)) return AV_SIZE;
    r->work[r->nwork++] = r->root;
    while (r->nwork) {
        r->cur = r->work[--r->nwork];
        if (mark_get(r, av_view(a, r->cur))) continue;
        s = whnf_share(r);
        if (s != AV_WHNF) return s;
        uint32_t t = av_view(a, r->cur);        /* jet nodes are their terms */
        if (!mark_set(r, t)) return AV_SIZE;
        /* push the last argument first, so the first pops first */
        while (av_tag(a, t) == AV_APP) {
            if (r->nwork == r->workcap &&
                !grow(&r->work, &r->workcap, r->nwork + 1))
                return AV_SIZE;
            r->work[r->nwork++] = av_right(a, t);
            t = av_view(a, av_left(a, t));
        }
    }
    return AV_NORMAL;
}

/*  --------------------------------------------------------------- driver */

av_opts av_opts_default(void) {
    return (av_opts){
        .strategy  = AV_SHARE,
        .whnf_only = false,
        .max_steps = UINT64_MAX,
        .max_nodes = av_default_max_nodes(),
        .interrupt = NULL,
        .no_collect = false,
        .jets      = true,
        .interp_jets = false,
        .install_jets = false,
        .compile_jets = false,
        .jet_check = 0,
        .census    = NULL,
        .trace     = NULL,
        .profile   = NULL,
        .jetstats  = NULL,
        .templates = false,
        .data      = false,
        .fix       = false,
        .fix_shared = false,
        .no_join   = false,
        .no_defer  = false,
    };
}

av_result av_reduce(av_arena *a, uint32_t t, const av_opts *o) {
    R r = { .a = a, .o = o, .root = t, .head = AV_NONE, .cur = AV_NONE,
            .jnode = AV_NONE, .hold = AV_NONE };
    /* deferred roots: share mode's instances, not where a profile or the
     * jet stats key on the nodes rewritten, nor in the stats build, which
     * counts the cells instances write */
    r.defer = o->strategy == AV_SHARE && o->templates && !o->no_defer && !o->profile &&
              !o->jetstats;
#ifdef AV_STRICT_STATS
    r.defer = false;
#endif
    av_active me = { roots, remap_marks, &r, a->active };
    a->active = &me;
    struct av_jetstats *outer_stats = a->jetstats;  /* a nested run keeps its own */
    a->jetstats = o->jetstats;
    av_status s = o->strategy == AV_COPY ? run_copy(&r) : run_share(&r);
    a->jetstats = outer_stats;

    uint32_t term = r.root;
    if (o->strategy == AV_COPY && s != AV_WHNF && s != AV_NORMAL) {
        term = s == AV_SIZE ? AV_NONE : copy_state(&r);
        /* a stopped state too large to rebuild is a SIZE outcome: never
         * report FUEL or INTERRUPTED without the term it stopped on */
        if (term == AV_NONE) s = AV_SIZE;
    } else if (term != AV_NONE) {
        term = av_res(a, term);
    }

    a->active = me.next;
    free(r.stk);
    free(r.dstk);
    nmap_free(&r.ymemo);
    free(r.p2c);
    free(r.fr);
    free(r.work);
    free(r.marks);
    av_result res = { term, r.steps, s, r.jet_calls, r.interp_calls,
                      r.jet_steps, r.jet_fault, r.tmpl_calls,
                      r.dispatches, r.fused, r.word_ops, r.fix_calls, r.joins,
                      r.p2_calls, r.p2_declines, r.p2_unbound, r.deferred, r.list_ops };
    return res;
}
