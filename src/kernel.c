/**  kernel.c
 *
 *  The kernel door (docs/DESIGN.md §9; SKIjack SPEC.md §4.1): pulled by
 *  axis, never by name, and installed as the reference host's loop
 *  installs it (skijack tests/test_examples.py): tl of a poke's value,
 *  unreduced, so a sharing strategy computes each state once.
 */

#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "jets.h"

/*  The ABI's Scott pair selectors: hd p = p K, tl p = p (K I), abstracted:
 *  S I (K K) and S I (K (K I)). */
static uint32_t sel_hd(av_arena *a) {
    uint32_t kk = av_app(a, AV_NODE_K, AV_NODE_K);
    uint32_t si = av_app(a, AV_NODE_S, AV_NODE_I);
    return kk == AV_NONE || si == AV_NONE ? AV_NONE : av_app(a, si, kk);
}

static uint32_t sel_tl(av_arena *a) {
    uint32_t ki = av_app(a, AV_NODE_K, AV_NODE_I);
    uint32_t kki = ki == AV_NONE ? AV_NONE : av_app(a, AV_NODE_K, ki);
    uint32_t si = av_app(a, AV_NODE_S, AV_NODE_I);
    return kki == AV_NONE || si == AV_NONE ? AV_NONE : av_app(a, si, kki);
}

uint32_t av_axis(av_arena *a, unsigned n, uint32_t t) {
    if (n == 0) return AV_NONE;
    int top = 31;
    while (!(n >> top & 1u)) top--;
    for (int b = top - 1; b >= 0 && t != AV_NONE; b--) {
        uint32_t sel = n >> b & 1u ? sel_tl(a) : sel_hd(a);
        t = sel == AV_NONE ? AV_NONE : av_app(a, sel, t);
    }
    return t;
}

uint32_t av_pull(av_arena *a, unsigned n, uint32_t k, uint32_t arg) {
    uint32_t arm = av_axis(a, n, k);
    uint32_t t = arm == AV_NONE ? AV_NONE : av_app(a, arm, k);
    return t == AV_NONE ? AV_NONE : av_app(a, t, arg);
}

/*  A pair, probed: one constructor with two fields. */
static bool is_pair(av_arena *a, uint32_t t, const av_opts *o, uint32_t *hd, uint32_t *tl) {
    av_peeled p;
    if (!av_peel(a, t, 1, o, &p, NULL) || p.ctor != 0 || p.nfields != 2) return false;
    *hd = p.field[0];
    *tl = p.field[1];
    return true;
}

bool av_is_kernel(av_arena *a, uint32_t t, const av_opts *o) {
    av_opts po = *o;
    po.strategy = AV_COPY;                  /* probes write nothing */
    po.no_collect = true;
    uint32_t battery, state, poke, rest, peek, load;
    return is_pair(a, t, &po, &battery, &state) && is_pair(a, battery, &po, &poke, &rest) &&
           is_pair(a, rest, &po, &peek, &load);
}

void av_kernel_adopt(av_kernel *k, av_arena *a, uint32_t kernel, const av_opts *o) {
    k->a = a;
    k->k = kernel;
    k->o = *o;
    k->o.whnf_only = true;
    k->events = 0;
    av_root_push(a, &k->k);
}

void av_kernel_free(av_kernel *k) {
    if (k->a) av_root_pop(k->a);
    k->a = NULL;
}

av_status av_kernel_boot(av_kernel *k, av_arena *a, uint32_t pill, uint32_t subject,
                         const av_opts *o, bool *is_kernel, uint32_t *value,
                         av_result *r) {
    memset(k, 0, sizeof *k);
    *is_kernel = false;
    *value = AV_NONE;
    uint32_t t = av_app(a, pill, subject);
    if (t == AV_NONE) { r->status = AV_SIZE; return AV_SIZE; }
    t = av_jets_match(a, t);
    av_opts ro = *o;
    ro.whnf_only = true;
    *r = av_reduce(a, t, &ro);
    if (r->status != AV_WHNF) return r->status;
    *value = r->term;
    av_root_push(a, value);
    *is_kernel = av_is_kernel(a, *value, o);
    av_root_pop(a);
    if (*is_kernel) av_kernel_adopt(k, a, *value, o);
    return AV_WHNF;
}

av_status av_kernel_poke(av_kernel *k, uint32_t event, uint32_t *effects, av_result *r) {
    av_arena *a = k->a;
    uint32_t t = av_pull(a, AV_AXIS_POKE, k->k, event);
    if (t == AV_NONE) { r->status = AV_SIZE; return AV_SIZE; }
    *r = av_reduce(a, t, &k->o);
    if (r->status != AV_WHNF) return r->status;
    uint32_t v = r->term;
    uint32_t hd = sel_hd(a), tl = sel_tl(a);
    uint32_t e = hd == AV_NONE ? AV_NONE : av_app(a, hd, v);
    uint32_t k2 = tl == AV_NONE ? AV_NONE : av_app(a, tl, v);
    if (e == AV_NONE || k2 == AV_NONE) { r->status = AV_SIZE; return AV_SIZE; }
    k->k = k2;
    k->events++;
    *effects = e;
    return AV_WHNF;
}

av_status av_kernel_peek(av_kernel *k, uint32_t path, uint32_t *answer, av_result *r) {
    uint32_t t = av_pull(k->a, AV_AXIS_PEEK, k->k, path);
    if (t == AV_NONE) { r->status = AV_SIZE; return AV_SIZE; }
    *r = av_reduce(k->a, t, &k->o);
    *answer = r->status == AV_WHNF ? r->term : AV_NONE;
    return r->status;
}

uint32_t av_kernel_state(av_kernel *k) {
    return av_axis(k->a, AV_AXIS_STATE, k->k);
}

bool av_kernel_load(av_kernel *k, uint32_t new_kernel) {
    uint32_t state = av_kernel_state(k);
    uint32_t k2 = state == AV_NONE ? AV_NONE : av_pull(k->a, AV_AXIS_LOAD, new_kernel, state);
    if (k2 == AV_NONE) return false;
    k->k = k2;
    k->events++;
    return true;
}
