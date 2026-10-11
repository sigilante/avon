/**  copy.c
 *
 *  The copy machine: the reference host's algorithm, aviary_kernel.reduce,
 *  on nodes.  The position is a head leaf and a flat argument vector, a
 *  contraction builds the combinator body fresh and re-decomposes it, and
 *  nothing is ever mutated.  Its contraction counts are the paper's.  It
 *  does not recurse: an argument being normalized is a frame (r->fr).
 */

#include <stdlib.h>

#include "machine.h"

/*  Push t's arguments, first argument on top, and make its head current.
 *  Inline: clang leaves it out of line in this file otherwise, and copy
 *  mode retires 24% more instructions. */
static inline bool decompose(R *r, uint32_t t) {
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
uint32_t copy_state(R *r) {
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
    AV_ALWAYS(inst != AV_NONE, "allocation past what ensure() reserved");
    if (inst == AV_NONE) return AV_SIZE;
    r->top -= k;
    if (!decompose(r, inst)) return AV_SIZE;
    r->steps += a->jets[id].cost;
    r->jet_steps += a->jets[id].cost;
    r->jet_calls++;
    return AV_WHNF;
}

av_status run_copy(R *r) {
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
                /* a word: copy mode runs its term */
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
                if (o->trace && r->nfr == 0 &&
                    !trace_step(o->trace, a, r->stk, r->base, r->top, r->steps))
                    return AV_INTERRUPTED;      /* the trace cannot follow */
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
