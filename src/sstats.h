/**  sstats.h
 *
 *  Strictness measurement: what becomes of the cells a template instance
 *  writes, in share mode.
 *  Built only with -DAV_STRICT_STATS (`make stats`, build/stats/avon), so
 *  the release and debug builds carry none of it.
 *
 *  An instance writes its body's open applications.  The root is written
 *  over the redex root.  Every other cell is a *spine* cell, only ever the
 *  function part of another application in the body, unwound as soon as
 *  the instance is; or an *argument* cell, passed somewhere as an operand.
 *  An argument cell is a *value* when it is already in weak head normal
 *  form---a partial application, a constructor short of its continuations
 *  ---or a word; otherwise a *thunk*, a redex nobody has asked for yet.
 *  A thunk is *forced* when the reducer first unwinds through it; one the
 *  collector finds dead, or the run ends with, was never forced.  The
 *  steps between writing a thunk and forcing it are what strictness could
 *  save; the never-forced are what laziness saves.
 *
 *  Also counted, for the cheaper levers:
 *  - a thunk whose head is a numeral operation with both numerals already
 *    held (primitive-redex speculation could compute it at once);
 *  - an instance whose body cases on a formal that arrived as a
 *    constructor value or a word (its dispatch could join the instance);
 *  - SUC applications an instance could not make a word, and how many of
 *    those were applied to a thunk;
 *  - spine cells by what follows their instance.  The body's head, with
 *    the arguments it already holds and the body's own, is *saturated* when
 *    it can step at once: then the reducer contracts through the spine it
 *    has just written, a write that deferring the redex root's update (the
 *    Reduceron's way) would skip.  Otherwise the instance is a value, or
 *    waits for arguments its context supplies, and its spine may be kept.
 */

#ifndef SSTATS_H
#define SSTATS_H

#ifdef AV_STRICT_STATS

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "avon.h"

typedef struct av_sstats {
    uint8_t  *kind;             /* per node: 1 an unforced thunk cell     */
    uint64_t *born;             /* the step it was written at             */
    uint32_t  cap;
    uint64_t  instances, cells, spine, arg_value, arg_word, arg_thunk;
    uint64_t  forced, dead, hist[7];     /* delays: 0, <=1, <=10, ... >1e5 */
    uint64_t  prs, case_ctor, case_word;
    uint64_t  suc_word, suc_cell, suc_on_thunk;
    uint64_t  spine_saturated, spine_open;
} av_sstats;

/*  The one table, for the one arena a run measures (defined in reduce.c). */
extern av_sstats *sstats_g;

static inline void sstats_fit(const av_arena *a) {
    av_sstats *s = sstats_g;
    if (s->cap >= a->cap) return;
    uint32_t c = a->cap;
    uint8_t *k = realloc(s->kind, c);
    uint64_t *b = realloc(s->born, (size_t)c * sizeof *b);
    if (!k || !b) { fprintf(stderr, "sstats: out of memory\n"); abort(); }
    memset(k + s->cap, 0, c - s->cap);
    s->kind = k;
    s->born = b;
    s->cap = c;
}

/*  The head of t's spine and its argument count; args[] the arguments,
 *  outermost first, up to max. */
static inline uint32_t sstats_head(const av_arena *a, uint32_t t, unsigned *n,
                                   uint32_t *args, unsigned max) {
    unsigned k = 0;
    t = av_res(a, t);
    while (av_tag(a, t) == AV_APP) {
        if (k < max) args[k] = av_right(a, t);
        k++;
        t = av_res(a, av_left(a, t));
    }
    *n = k;
    return t;
}

/*  The arguments a head takes before it steps in share mode with
 *  templates and data jets; 0 for one that never steps (an atom). */
static inline unsigned sstats_arity(const av_arena *a, uint32_t h) {
    uint32_t tag = av_tag(a, h);
    if (tag == AV_LEAF) return ski_arity(av_right(a, h));
    if (tag != AV_JET) return 0;
    if (a->nodes[h].l & AV_JET_WORD) return 2;
    const struct av_jet *j = &a->jets[AV_JET_ID(av_left(a, h))];
    if (j->fix) return 1;
    if (j->word_op) return j->word_op >= AV_WOP_IFEQ ? 4 : 2;
    if (j->tmpl) return a->tmpls[j->tmpl - 1].k;
    return j->arity;
}

static inline bool sstats_is_ctor_value(const av_arena *a, uint32_t t) {
    unsigned n;
    uint32_t args[1];
    uint32_t h = sstats_head(a, t, &n, args, 0);
    if (av_is_word(a, h)) return n == 0;
    if (av_tag(a, h) != AV_JET) return false;
    const struct av_jet *j = &a->jets[AV_JET_ID(av_left(a, h))];
    return j->tmpl && av_ctor_is(a->tmpls[j->tmpl - 1].ctor) && n < a->tmpls[j->tmpl - 1].k;
}

/*  After tmpl_instance(a, T, args, into) wrote its cells into
 *  a->tmpl_scratch, at step `now`. */
static inline void sstats_instance(av_arena *a, const av_tmpl *T, const uint32_t *args,
                                   uint64_t now) {
    av_sstats *s = sstats_g;
    if (!s) return;
    sstats_fit(a);
    s->instances++;
    uint32_t n = T->nops;
    const uint32_t *ops = T->ops, *out = a->tmpl_scratch;
    bool in_place = T->root_last && !(T->sucop && T->sucop[n - 1]);
    uint32_t root = in_place ? n - 1 : ((T->root >> 30) == 2 ? (T->root & AV_PAYLOAD) : UINT32_MAX);
    uint32_t end = in_place ? n - 1 : n;
    uint8_t asf[256], asx[256];
    if (n > 256) return;
    memset(asf, 0, n);
    memset(asx, 0, n);
    for (uint32_t i = 0; i < n; i++) {
        if ((ops[2 * i] >> 30) == 2) asf[ops[2 * i] & AV_PAYLOAD] = 1;
        if ((ops[2 * i + 1] >> 30) == 2) asx[ops[2 * i + 1] & AV_PAYLOAD] = 1;
    }
    if (!in_place && (T->root >> 30) == 2) asx[T->root & AV_PAYLOAD] = 1;
    uint64_t nspine = 0;
    for (uint32_t i = 0; i < end; i++) {
        if (T->sucop && T->sucop[i]) {
            uint32_t x = ops[2 * i + 1];
            uint32_t xn = (x >> 30) == 0 ? a->tmpl_globals[T->consts[x & AV_PAYLOAD]]
                        : (x >> 30) == 1 ? args[x & AV_PAYLOAD] : out[x & AV_PAYLOAD];
            if (av_is_word(a, out[i])) s->suc_word++;
            else {
                s->suc_cell++;
                unsigned m;
                uint32_t h = sstats_head(a, xn, &m, NULL, 0);
                unsigned k = sstats_arity(a, h);
                if (k && m >= k) s->suc_on_thunk++;
            }
        }
        if (i == root) continue;
        s->cells++;
        if (!asx[i]) { s->spine++; nspine++; continue; }
        uint32_t c = out[i];
        if (av_is_word(a, c)) { s->arg_word++; continue; }
        unsigned m;
        uint32_t ar[4];
        uint32_t h = sstats_head(a, c, &m, ar, 4);
        unsigned k = sstats_arity(a, h);
        if (!k || m < k) { s->arg_value++; continue; }
        s->arg_thunk++;
        s->kind[c] = 1;
        s->born[c] = now;
        if (av_tag(a, h) == AV_JET && !(a->nodes[h].l & AV_JET_WORD) &&
            a->jets[AV_JET_ID(av_left(a, h))].word_op && m == k) {
            uint32_t v;     /* the numerals are the innermost two arguments */
            if (av_numeral(a, ar[m - 1], &v) && av_numeral(a, ar[m - 2], &v)) s->prs++;
        }
    }
    /* the body's head: a formal that arrived as a value its case reads */
    if (!in_place && (T->root >> 30) != 2) return;     /* the body is no application */
    uint32_t x = in_place ? ops[2 * (n - 1)] : ops[2 * (T->root & AV_PAYLOAD)];
    unsigned d = 1;                                     /* the body's arguments */
    while ((x >> 30) == 2) { x = ops[2 * (x & AV_PAYLOAD)]; d++; }
    if (nspine) {
        uint32_t hn = (x >> 30) == 0 ? a->tmpl_globals[T->consts[x & AV_PAYLOAD]] : args[x & AV_PAYLOAD];
        unsigned m;
        uint32_t hd = sstats_head(a, hn, &m, NULL, 0);
        unsigned k = sstats_arity(a, hd);
        if (k && m + d >= k) s->spine_saturated += nspine;
        else s->spine_open += nspine;
    }
    if ((x >> 30) == 1) {
        uint32_t v = av_res(a, args[x & AV_PAYLOAD]);
        if (av_is_word(a, v) || v == AV_NODE_K) s->case_word++;
        else if (sstats_is_ctor_value(a, v)) s->case_ctor++;
    }
}

/*  The reducer unwinds through t at step `now`. */
static inline void sstats_force(const av_arena *a, uint32_t t, uint64_t now) {
    av_sstats *s = sstats_g;
    if (!s || t >= s->cap || s->kind[t] != 1) return;
    s->kind[t] = 0;
    s->forced++;
    uint64_t d = now - s->born[t];
    unsigned b = d == 0 ? 0 : d <= 1 ? 1 : d <= 10 ? 2 : d <= 100 ? 3 :
                 d <= 1000 ? 4 : d <= 100000 ? 5 : 6;
    s->hist[b]++;
    (void)a;
}

/*  A collection: carry each live thunk's record to its new index; one
 *  left behind is dead, never forced. */
static inline void sstats_collect(const av_arena *a, const uint32_t *fwd, uint32_t from_used,
                                  uint32_t to_used) {
    av_sstats *s = sstats_g;
    if (!s) return;
    uint8_t *k = calloc(to_used > a->cap ? to_used : a->cap, 1);
    uint64_t *b = malloc((size_t)(to_used > a->cap ? to_used : a->cap) * sizeof *b);
    if (!k || !b) { fprintf(stderr, "sstats: out of memory\n"); abort(); }
    for (uint32_t i = 0; i < from_used && i < s->cap; i++) {
        if (s->kind[i] != 1) continue;
        if (fwd[i] == AV_NONE) { s->dead++; continue; }
        k[fwd[i]] = 1;
        b[fwd[i]] = s->born[i];
    }
    free(s->kind);
    free(s->born);
    s->kind = k;
    s->born = b;
    s->cap = to_used > a->cap ? to_used : a->cap;
}

static inline void sstats_begin(void) {
    sstats_g = calloc(1, sizeof *sstats_g);
}

/*  The report, on stderr; the thunks still unforced count as never forced. */
static inline void sstats_report(void) {
    av_sstats *s = sstats_g;
    if (!s) return;
    uint64_t live = 0;
    for (uint32_t i = 0; i < s->cap; i++) live += s->kind[i] == 1;
    unsigned long long u = (unsigned long long)(s->dead + live);
    fprintf(stderr,
            "sstats: %llu instances, %llu cells: %llu spine, %llu argument values, "
            "%llu argument words, %llu argument thunks\n",
            (unsigned long long)s->instances, (unsigned long long)s->cells,
            (unsigned long long)s->spine, (unsigned long long)s->arg_value,
            (unsigned long long)s->arg_word, (unsigned long long)s->arg_thunk);
    fprintf(stderr,
            "sstats: thunks forced %llu, never forced %llu (%llu collected, %llu at the end)\n",
            (unsigned long long)s->forced, u, (unsigned long long)s->dead,
            (unsigned long long)live);
    fprintf(stderr,
            "sstats: forcing delay in steps: 0 %llu, 1 %llu, <=10 %llu, <=100 %llu, "
            "<=1e3 %llu, <=1e5 %llu, >1e5 %llu\n",
            (unsigned long long)s->hist[0], (unsigned long long)s->hist[1],
            (unsigned long long)s->hist[2], (unsigned long long)s->hist[3],
            (unsigned long long)s->hist[4], (unsigned long long)s->hist[5],
            (unsigned long long)s->hist[6]);
    fprintf(stderr,
            "sstats: speculable numeral operations %llu; body cases on a constructor %llu, "
            "on a numeral %llu; SUC made words %llu, cells %llu (%llu on a thunk)\n",
            (unsigned long long)s->prs, (unsigned long long)s->case_ctor,
            (unsigned long long)s->case_word, (unsigned long long)s->suc_word,
            (unsigned long long)s->suc_cell, (unsigned long long)s->suc_on_thunk);
    fprintf(stderr, "sstats: spine cells %llu: under a saturated head %llu (%.1f%%), "
            "a value or awaiting arguments %llu\n",
            (unsigned long long)s->spine, (unsigned long long)s->spine_saturated,
            s->spine ? 100.0 * (double)s->spine_saturated / (double)s->spine : 0.0,
            (unsigned long long)s->spine_open);
}

#define SSTATS_INSTANCE(a, T, args, now) sstats_instance((a), (T), (args), (now))
#define SSTATS_FORCE(a, t, now) sstats_force((a), (t), (now))

#else

#define SSTATS_INSTANCE(a, T, args, now) ((void)0)
#define SSTATS_FORCE(a, t, now) ((void)0)

#endif /* AV_STRICT_STATS */

#endif /* SSTATS_H */
