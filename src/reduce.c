/**  reduce.c
 *
 *  Normal-order reduction, two strategies (docs/DESIGN.md §1.1, §3).
 *
 *  copy   The reference host's algorithm, aviary_kernel.reduce, on nodes:
 *         the position is a head leaf and a flat argument vector, a
 *         contraction builds the combinator body fresh and re-decomposes
 *         it, and nothing is ever mutated.  Its contraction counts are the
 *         paper's.
 *  share  Turner's machine: walk down the spine, overwrite the redex root
 *         in place, so a duplicated redex is contracted once.
 *
 *  Neither recurses.  Fuel is checked before every attempt to contract,
 *  the last of which finds no redex, so s contractions need fuel s + 1.
 */

#include <assert.h>
#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "jets.h"

/*  An allocation that ensure() has already reserved room for.  It cannot
 *  fail unless a `need` count is wrong, which the debug build catches.
 */
static inline uint32_t reserved_app(av_arena *a, uint32_t f, uint32_t x) {
    uint32_t i = av_app(a, f, x);
    assert(i != AV_NONE && "allocation past what ensure() reserved");
    return i;
}

typedef struct { uint32_t head; size_t base, n, i; } frame;

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
    uint64_t       dispatches, fused, word_ops;
    uint64_t       interp_calls;
    bool           jet_fault;
    uint32_t       jnode;       /* share: a jet node being demoted        */
    bool           normal;      /* share: making the normal form, or the
                                   root's term's head normal form, where a
                                   word must become its term's            */
} R;

/*  ---------------------------------------------------------------- memory */

static void roots(av_gc *g, void *ctx) {
    R *r = ctx;
    r->root = av_gc_evac(g, r->root);
    if (r->head != AV_NONE) r->head = av_gc_evac(g, r->head);
    if (r->cur != AV_NONE) r->cur = av_gc_evac(g, r->cur);
    if (r->jnode != AV_NONE) r->jnode = av_gc_evac(g, r->jnode);
    for (size_t i = 0; i < r->top; i++) r->stk[i] = av_gc_evac(g, r->stk[i]);
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

static void remap_marks(av_gc *g, void *ctx) {
    R *r = ctx;
    if (r->o->profile) profile_remap(r->o->profile, g);
    if (r->o->jetstats) jetstats_remap(r->o->jetstats, g);
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

/*  Make room for k allocations, collecting if the arena is full.  False
 *  means the live set would exceed max_nodes, or memory ran out: SIZE.
 */
static bool ensure(R *r, size_t k) {
    av_arena *a = r->a;
    if (k > AV_MAX_NODES) return false;
    if (a->cap - a->used >= k) return true;
    if (r->o->no_collect || r->o->census)   /* a census keys on node identity */
        return av_reserve(a, (uint32_t)k) && a->used <= r->o->max_nodes;
    /* every active reduction's roots, this one's among them */
    if (!av_collect(a, (uint32_t)k, NULL, NULL, NULL)) return false;
    return a->used <= r->o->max_nodes;
}

static bool grow(uint32_t **v, size_t *cap, size_t need) {
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

static bool interrupted(const R *r) {
    return r->o->interrupt && *r->o->interrupt;
}

/*  ------------------------------------------------------------------ copy */

/*  Push t's arguments, first argument on top, and make its head current. */
static bool decompose(R *r, uint32_t t) {
    const av_arena *a = r->a;
    t = av_res(a, t);
    while (av_tag(a, t) == AV_APP) {
        if (!push(r, av_right(a, t))) return false;
        t = av_res(a, av_left(a, t));
    }
    r->head = t;
    return true;
}

/*  head applied to the n slots above base, first argument at the top. */
static uint32_t apply_slots(R *r, uint32_t head, size_t base, size_t n) {
    uint32_t t = head;
    for (size_t j = 0; j < n; j++)
        t = reserved_app(r->a, t, r->stk[base + n - 1 - j]);
    return t;
}

/*  The whole state as a term, for FUEL, SIZE and INTERRUPTED: the current
 *  position, placed into each enclosing frame's slot.
 */
static uint32_t copy_state(R *r) {
    size_t need = r->top - r->base;
    for (size_t k = 0; k < r->nfr; k++) need += r->fr[k].n;
    if (!ensure(r, need)) return AV_NONE;
    uint32_t t = apply_slots(r, r->head, r->base, r->top - r->base);
    for (size_t k = r->nfr; k-- > 0;) {
        frame *f = &r->fr[k];
        r->stk[f->base + f->n - 1 - f->i] = t;
        t = apply_slots(r, f->head, f->base, f->n);
    }
    return t;
}

/*  ------------------------------------------------------------------ jets */

/*  Whether a jet node at a position with `have` arguments fires: jets on,
 *  enough arguments, and the fuel left covers the charge, so that stepping
 *  instead would not have stopped part way (§6.5). */
static bool fires(const R *r, uint32_t id, size_t have) {
    const av_jet *j = &r->a->jets[id];
    return r->o->jets && have >= j->arity &&
           r->o->max_steps - r->steps >= j->cost;
}

/*  --jet-check (§6.6): run the jet node's own term over the arguments in
 *  copy mode, jets off, for exactly the charge, and compare the state it
 *  reaches with an instance.  Allocates without collecting.  False only on
 *  a definite disagreement; a check that runs out of memory or of its
 *  comparison budget is inconclusive, not a fault. */
static bool check_fire(R *r, uint32_t node, uint32_t id, const uint32_t *args) {
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

/*  Fire the jet at the head of the copy-mode position: its arity's
 *  arguments are replaced by an instance of its residual. */
static av_status fire_copy(R *r) {
    av_arena *a = r->a;
    uint32_t id = AV_JET_ID(av_left(a, r->head));
    unsigned k = a->jets[id].arity;
    uint32_t args[AV_JET_ARITY_MAX];
    if (r->o->jet_check && (r->jet_calls + 1) % r->o->jet_check == 0) {
        for (unsigned i = 0; i < k; i++) args[i] = r->stk[r->top - 1 - i];
        if (!check_fire(r, r->head, id, args)) {
            r->jet_fault = true;
            return AV_INTERRUPTED;
        }
    }
    if (!ensure(r, a->jets[id].nodes)) return AV_SIZE;
    for (unsigned i = 0; i < k; i++) args[i] = r->stk[r->top - 1 - i];
    if (r->o->jetstats) jetstats_fire(r->o->jetstats, r->head, id);
    uint32_t inst = jet_instance(a, id, args, false);   /* copy mode writes nothing */
    assert(inst != AV_NONE && "allocation past what ensure() reserved");
    if (inst == AV_NONE) return AV_SIZE;
    r->top -= k;
    if (!decompose(r, inst)) return AV_SIZE;
    r->steps += a->jets[id].cost;
    r->jet_steps += a->jets[id].cost;
    r->jet_calls++;
    return AV_WHNF;
}

/*  An interpreter jet at the head of a position with `have` arguments:
 *  1 fired (the arguments replaced by the outcome and its charge added),
 *  0 declined, -1 stop with *st.  The arguments are read again after the
 *  fire, which may collect. */
/*  How many arguments a fire of jet id consumes: the unquoter's one, an
 *  interpreter's parameters, fuel and datum. */
static unsigned fire_nargs(const R *r, uint32_t id) {
    const av_arena *a = r->a;
    if (a->jets[id].unquote && r->o->install_jets) return 1;
    if (a->jets[id].compiler && r->o->compile_jets) return 2;
    return a->interps[a->jets[id].interp].nparams + 2;
}

static int try_interp(R *r, uint32_t *nodep, size_t have, av_status *st,
                      uint32_t *outp) {
    av_arena *a = r->a;
    uint32_t node = *nodep;
    uint32_t id = AV_JET_ID(av_left(a, node));
    bool uq = a->jets[id].unquote && r->o->install_jets;    /* §20.2 */
    bool cj = !uq && a->jets[id].compiler && r->o->compile_jets;   /* §20.3 */
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

static av_status run_copy(R *r) {
    av_arena *a = r->a;
    const av_opts *o = r->o;
    r->top = r->base = 0;
    if (!decompose(r, r->root)) return AV_SIZE;
    if (o->census) census_record(o->census, a, r->root, r->top - r->base);

    for (;;) {
        /* bring the current position to weak head normal form */
        for (;;) {
            if (interrupted(r)) return AV_INTERRUPTED;
            if (r->steps >= o->max_steps) return AV_FUEL;
            if (av_tag(a, r->head) == AV_JET && (av_left(a, r->head) & AV_JET_WORD)) {
                /* a word (§6.10): copy mode runs its term */
                if (!decompose(r, av_right(a, r->head))) return AV_SIZE;
                continue;
            }
            if (av_tag(a, r->head) == AV_JET) {
                av_status ist;
                uint32_t out;
                int ir = try_interp(r, &r->head, r->top - r->base, &ist, &out);
                if (ir < 0) return ist;
                if (ir > 0) {
                    r->top -= fire_nargs(r, AV_JET_ID(av_left(a, r->head)));
                    if (!decompose(r, out)) return AV_SIZE;
                    continue;
                }
                /* A fire that cannot have its nodes steps instead: the node
                 * cap then stops the run where stepping would, or later. */
                if (a->jets[AV_JET_ID(av_left(a, r->head))].residual_ok &&
                    fires(r, AV_JET_ID(av_left(a, r->head)), r->top - r->base) &&
                    ensure(r, a->jets[AV_JET_ID(av_left(a, r->head))].nodes)) {
                    av_status js = fire_copy(r);
                    if (js != AV_WHNF) return js;
                } else {
                    uint32_t id = AV_JET_ID(av_left(a, r->head));
                    if (o->jetstats && o->jets && a->jets[id].residual_ok &&
                        r->top - r->base < a->jets[id].arity)
                        jetstats_miss(o->jetstats, id);
                    if (!decompose(r, av_right(a, r->head)))
                        return AV_SIZE;         /* unwrapped: the term itself */
                }
                continue;
            }
            ski_leaf c = av_right(a, r->head);
            unsigned k = ski_arity(c);
            if (k == 0 || r->top - r->base < k) break;
            uint32_t x;
            if (c == SKI_S) {                   /* S x y z -> x z (y z) */
                if (!ensure(r, 1)) return AV_SIZE;
                x = r->stk[r->top - 1];
                uint32_t y = r->stk[r->top - 2], z = r->stk[r->top - 3];
                r->top -= 3;
                r->stk[r->top++] = reserved_app(a, y, z);
                r->stk[r->top++] = z;
            } else {                            /* K x y -> x;  I x -> x */
                x = r->stk[r->top - 1];
                r->top -= k;
            }
            if (!decompose(r, x)) return AV_SIZE;
            r->steps++;
            if (o->census) census_record(o->census, a, x, r->top - r->base);
        }

        size_t n = r->top - r->base;
        if (o->whnf_only && r->nfr == 0) {
            if (!ensure(r, n)) return AV_SIZE;
            r->root = apply_slots(r, r->head, r->base, n);
            return AV_WHNF;
        }
        if (n > 0) {                            /* normalize each argument */
            if (r->nfr == r->frcap) {
                size_t cap = r->frcap ? r->frcap * 2 : 64;
                frame *f = realloc(r->fr, cap * sizeof *f);
                if (!f) return AV_SIZE;
                r->fr = f;
                r->frcap = cap;
            }
            r->fr[r->nfr++] = (frame){ r->head, r->base, n, 0 };
            uint32_t arg = r->stk[r->top - 1];
            r->base = r->top;
            if (!decompose(r, arg)) return AV_SIZE;
            continue;
        }

        /* the position is normal: store it, and move to the next argument */
        uint32_t res = r->head;
        for (;;) {
            if (r->nfr == 0) {
                r->root = res;
                return AV_NORMAL;
            }
            frame *f = &r->fr[r->nfr - 1];
            r->stk[f->base + f->n - 1 - f->i] = res;
            if (++f->i < f->n) {
                r->top = r->base = f->base + f->n;
                if (!decompose(r, r->stk[f->base + f->n - 1 - f->i]))
                    return AV_SIZE;
                break;
            }
            if (!ensure(r, f->n)) return AV_SIZE;
            f = &r->fr[r->nfr - 1];
            res = apply_slots(r, f->head, f->base, f->n);
            r->top = r->base = f->base;
            r->nfr--;
        }
    }
}

/*  ----------------------------------------------------------------- share */

/*  The most nodes one numeral operation builds (§6.10).  Beyond it the
 *  operation runs its term, which builds its result lazily: a product
 *  nobody reads past its first successor should not cost its whole size. */
#define WORD_BUILD_MAX (1u << 20)

/*  Data jets (§6.10): a constructor template at the head with its fields
 *  and continuations, and the continuation its index selects, applied to
 *  the fields, replaces the redex root: one step.  When that continuation
 *  is a template's key applied to exactly the arguments that, with the
 *  fields, it takes -- a case branch, lifted with what it captured -- that
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
static void dispatch_read(const R *r, av_ctor sh, disp *d) {
    const av_arena *a = r->a;
    unsigned m = sh.fields;
    for (unsigned j = 0; j < m; j++)
        d->field[j] = av_res(a, av_right(a, r->stk[r->top - 1 - j]));
    d->cont = av_res(a, av_right(a, r->stk[r->top - 1 - m - sh.index]));
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

/*  The dispatch: k = m + n arguments, the redex root stk[top-k]. */
static av_status dispatch(R *r, av_ctor sh, unsigned k, uint32_t *curp) {
    av_arena *a = r->a;
    disp d;
    dispatch_read(r, sh, &d);
    size_t need = d.U ? d.U->nops + d.U->nsuc : (sh.fields ? sh.fields - 1 : 0);
    if (need && a->cap - a->used < need) {
        if (!ensure(r, need)) return AV_SIZE;
        dispatch_read(r, sh, &d);                   /* the collection moved them */
    }
    uint32_t nd = r->stk[r->top - k];
    if (d.U) {
        uint32_t inst = tmpl_instance(a, d.U, d.uarg);
        assert(inst != AV_NONE && "allocation past what ensure() reserved");
        if (inst == AV_NONE) return AV_SIZE;
        arena_set(a, nd, (av_node){ (AV_IND << AV_TAG_SHIFT) | inst, 0 });
        r->fused++;
    } else if (sh.fields == 0) {
        arena_set(a, nd, (av_node){ (AV_IND << AV_TAG_SHIFT) | d.cont, 0 });
    } else {
        uint32_t t = d.cont;
        for (unsigned j = 0; j + 1 < sh.fields; j++) t = reserved_app(a, t, d.field[j]);
        if (r->o->profile) profile_rewrote(r->o->profile, nd);
        arena_set(a, nd, (av_node){ t, d.field[sh.fields - 1] });
    }
    r->top -= k;
    *curp = nd;
    r->steps++;
    r->dispatches++;
    return AV_WHNF;
}

/*  A numeral operation (§6.10) at the head with its k operands, the two
 *  numerals first: 1 fired, both being held already (K or words), the
 *  redex root now its result; 0 declined, to run its term; -1 SIZE. */
static int word_fire(R *r, unsigned op, unsigned k, uint32_t *curp) {
    av_arena *a = r->a;
    uint32_t m, n;
    if (!av_numeral(a, av_right(a, r->stk[r->top - 1]), &m) ||
        !av_numeral(a, av_right(a, r->stk[r->top - 2]), &n))
        return 0;
    uint64_t v = 0, need = 0;
    if (op == AV_WOP_ADD) { v = (uint64_t)m + n; need = 2 * (uint64_t)n; }
    if (op == AV_WOP_MUL) { v = (uint64_t)m * n; need = 2 * v; }
    if (v > AV_WORD_MAX || need > WORD_BUILD_MAX) return 0;
    if (need && !ensure(r, (size_t)need)) return -1;
    uint32_t x = av_res(a, av_right(a, r->stk[r->top - 1]));     /* m: reread */
    switch (op) {
    case AV_WOP_ADD:
        for (uint32_t i = 0; i < n; i++) x = word_succ(a, x);
        break;
    case AV_WOP_SUB:
        for (uint32_t i = 0; i < n && x != AV_NODE_K; i++) x = word_pred(a, x);
        break;
    case AV_WOP_MUL:
        x = AV_NODE_K;
        for (uint64_t i = 0; i < v; i++) x = word_succ(a, x);
        break;
    case AV_WOP_IFEQ:
        x = av_res(a, av_right(a, r->stk[r->top - (m == n ? 3 : 4)]));
        break;
    case AV_WOP_IFLE:
        x = av_res(a, av_right(a, r->stk[r->top - (m <= n ? 3 : 4)]));
        break;
    default:
        return 0;
    }
    assert(x != AV_NONE && "allocation past what ensure() reserved");
    if (x == AV_NONE) return -1;
    uint32_t nd = r->stk[r->top - k];               /* the redex root */
    arena_set(a, nd, (av_node){ (AV_IND << AV_TAG_SHIFT) | x, 0 });
    r->top -= k;
    *curp = nd;
    r->steps++;
    r->word_ops++;
    return 1;
}

/*  Reduce r->cur to weak head normal form in place.  The spine lives on
 *  r->stk above its entry height, which is restored on success.
 */
static av_status whnf_share(R *r) {
    av_arena *a = r->a;
    const av_opts *o = r->o;
    size_t bottom = r->top;
    uint32_t cur = r->cur;

    for (;;) {
        cur = av_res(a, cur);
        if (av_tag(a, cur) == AV_APP) {
            if (!push(r, cur)) return AV_SIZE;
            /* path compression: point past an indirection for good, or
             * chains grow by one per contraction and walks go quadratic */
            uint32_t l = av_left(a, cur), rl = av_res(a, l);
            if (rl != l) arena_set(a, cur, (av_node){ rl, a->nodes[cur].r });
            cur = rl;
            continue;
        }
        if (interrupted(r)) return AV_INTERRUPTED;
        if (r->steps >= o->max_steps) return AV_FUEL;
        if (av_tag(a, cur) == AV_JET && (av_left(a, cur) & AV_JET_WORD)) {
            /* a word (§6.10): with its two continuations, W n z s is
             * s (W (n-1)), written over the redex root; short of them, a
             * value -- but, making the normal form, its term SUC (W (n-1)),
             * a redex, fresh so the word's own stays whole */
            if (r->top - bottom < 2) {
                if (!r->normal) break;
                r->jnode = cur;
                if (!ensure(r, 1)) return AV_SIZE;
                cur = r->jnode;
                r->jnode = AV_NONE;
                uint32_t t = reserved_app(a, a->word_suc, word_pred(a, cur));
                arena_set(a, cur, (av_node){ (AV_IND << AV_TAG_SHIFT) | t, 0 });
                cur = t;
                continue;
            }
            uint32_t n = r->stk[r->top - 2];
            uint32_t sk = av_res(a, av_right(a, n));
            if (o->profile) profile_rewrote(o->profile, n);
            arena_set(a, n, (av_node){ sk, word_pred(a, cur) });
            r->top -= 2;
            cur = n;
            r->steps++;
            r->dispatches++;
            continue;
        }
        if (av_tag(a, cur) == AV_JET) {
            uint32_t id = AV_JET_ID(av_left(a, cur));
            av_status ist;
            uint32_t iout;
            int ir = try_interp(r, &cur, r->top - bottom, &ist, &iout);
            if (ir < 0) return ist;
            if (ir > 0) {                       /* the redex root becomes it */
                unsigned k = fire_nargs(r, id);
                uint32_t n = r->stk[r->top - k];     /* reread: the fire may collect */
                arena_set(a, n, (av_node){ (AV_IND << AV_TAG_SHIFT) | iout, 0 });
                r->top -= k;
                cur = n;
                continue;
            }
            if (o->data && a->jets[id].word_op) {
                /* a numeral operation (§6.10): natively on words; else its
                 * term, the node kept for the next call */
                unsigned op = a->jets[id].word_op, k = op >= AV_WOP_IFEQ ? 4u : 2u;
                if (r->top - bottom >= k) {
                    int wf = word_fire(r, op, k, &cur);
                    if (wf < 0) return AV_SIZE;
                    if (wf > 0) continue;
                }
                if (!(av_left(a, cur) & AV_JET_SHARED)) {
                    cur = av_right(a, cur);
                    continue;
                }
            }
            if (o->templates && a->jets[id].tmpl) {
                /* a supercombinator template (§6.9): its body over the
                 * arguments, one step; short of them, its term, the node
                 * left a root for the next full application */
                const av_tmpl *T = &a->tmpls[a->jets[id].tmpl - 1];
                if (o->data && av_ctor_is(T->ctor) && r->top - bottom >= T->k) {
                    /* a constructor with every argument (§6.10) */
                    av_status ds = dispatch(r, T->ctor, T->k, &cur);
                    if (ds != AV_WHNF) return ds;
                    continue;
                }
                if (r->top - bottom >= T->k) {
                    if (o->jetstats) jetstats_fire(o->jetstats, cur, id);
                    if (!ensure(r, T->nops + T->nsuc)) return AV_SIZE;
                    uint32_t args[AV_JET_ARITY_MAX];
                    for (unsigned i = 0; i < T->k; i++)
                        args[i] = av_res(a, av_right(a, r->stk[r->top - 1 - i]));
                    uint32_t inst = tmpl_instance(a, T, args);
                    assert(inst != AV_NONE && "allocation past what ensure() reserved");
                    if (inst == AV_NONE) return AV_SIZE;
                    uint32_t n = r->stk[r->top - T->k];     /* the redex root */
                    arena_set(a, n, (av_node){ (AV_IND << AV_TAG_SHIFT) | inst, 0 });
                    r->top -= T->k;
                    cur = n;
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
                 * indirection to a term it owns -- a private copy when
                 * the term is the dashboard's -- and no jet node's term
                 * is ever written (§6.5). */
                uint32_t inner = av_right(a, cur);
                if (av_left(a, cur) & AV_JET_SHARED) {
                    r->jnode = cur;
                    if (!ensure(r, a->jets[id].term_nodes)) return AV_SIZE;
                    cur = r->jnode;
                    r->jnode = AV_NONE;
                    inner = jet_term_copy(a, id);
                    assert(inner != AV_NONE && "allocation past what ensure() reserved");
                    if (inner == AV_NONE) return AV_SIZE;
                }
                arena_set(a, cur, (av_node){ (AV_IND << AV_TAG_SHIFT) | inner, 0 });
                cur = inner;
                continue;
            }
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
            assert(inst != AV_NONE && "allocation past what ensure() reserved");
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
        uint32_t n;
        if (c == SKI_S) {                       /* S f g x -> f x (g x) */
            if (!ensure(r, 2)) return AV_SIZE;
            n = r->stk[r->top - 3];
            uint32_t f = av_res(a, av_right(a, r->stk[r->top - 1]));
            uint32_t g = av_res(a, av_right(a, r->stk[r->top - 2]));
            uint32_t x = av_res(a, av_right(a, n));
            uint32_t fx = reserved_app(a, f, x);
            uint32_t gx = reserved_app(a, g, x);
            if (o->profile) profile_rewrote(o->profile, n);
            arena_set(a, n, (av_node){ fx, gx });
        } else {                                /* K x y -> x;  I x -> x */
            n = r->stk[r->top - k];
            uint32_t x = av_res(a, av_right(a, r->stk[r->top - 1]));
            if (o->profile) profile_rewrote(o->profile, n);
            arena_set(a, n, (av_node){ (AV_IND << AV_TAG_SHIFT) | x, 0 });
        }
        r->top -= k;
        cur = n;
        r->steps++;
    }
    r->top = bottom;
    return AV_WHNF;
}

/*  Whether t's head is a word (§6.10). */
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
        .max_nodes = AV_MAX_NODES,
        .interrupt = NULL,
        .no_collect = false,
        .jets      = true,
        .interp_jets = false,
        .install_jets = false,
        .compile_jets = false,
        .jet_check = 0,
        .census    = NULL,
        .profile   = NULL,
        .jetstats  = NULL,
        .templates = false,
        .data      = false,
    };
}

av_result av_reduce(av_arena *a, uint32_t t, const av_opts *o) {
    R r = { .a = a, .o = o, .root = t, .head = AV_NONE, .cur = AV_NONE,
            .jnode = AV_NONE };
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
    free(r.fr);
    free(r.work);
    free(r.marks);
    return (av_result){ term, r.steps, s, r.jet_calls, r.interp_calls,
                        r.jet_steps, r.jet_fault, r.tmpl_calls,
                        r.dispatches, r.fused, r.word_ops };
}
