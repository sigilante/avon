/**  trace.c
 *
 *  Frame traces (docs/DESIGN.md §22): an observer of copy mode's head run
 *  for the pure S calculus with one opaque atom, the passenger X, as the
 *  hider census of the pure-S paper reads it (its fixed_points_hider.py).
 *
 *  The frame is the argument vector of the S head, fr = [u_1 .. u_L], u_1
 *  at the x-seat; in copy mode it is the argument slots stk[base..top),
 *  u_1 = stk[top-1].  pos(u_i) = L - i + 1, so position 1 is the last
 *  item, the bottom slot.  Before each S contraction the observer reports
 *  L, the positions of the X-headed items, and, with one of them (the
 *  passenger P), the stack depth d = pos(P) - 1 and the defect
 *  D = #{front u : sigma(u) >= 1} + #{stack u : sigma(u) >= 2}, sigma(u)
 *  the X-headed items among u's head's arguments; the event (o: P at the
 *  x-seat, y: the y-seat, z: the z-seat); and the arity of the front item.
 *
 *  Nothing here decides anything: the trace is an observation, and the
 *  census's verdicts and certificates stay with the paper's scripts.
 *
 *  Cost.  A trace run never collects, so copy mode's bump allocation makes
 *  every application's children older than it, and the per-node facts
 *  (X-headed, contains X, sigma capped at 2, arity) are filled in index
 *  order on demand: no walk over paths, which on these shared terms would
 *  be exponential.  Prefix counts over the slots are recomputed only for
 *  the slots a step rewrote -- a step leaves everything below its top
 *  three slots alone -- so a trace costs what the run costs.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "jets.h"

enum { F_DONE = 1, F_XH = 2, F_CX = 4 };

struct av_trace {
    uint32_t  pass;             /* the passenger's leaf node              */
    bool      steps_out;        /* print a line per step                  */
    FILE     *out;
    char     *buf;              /* buffered output                        */
    size_t    blen, bcap;
    /* per node */
    uint8_t  *fl, *sig;
    uint32_t *ar;
    uint32_t  ncap, done;       /* facts known for nodes < done           */
    bool      bad;              /* a node out of order, or not S/X        */
    /* per slot, inclusive prefix counts */
    uint32_t *cX, *c1, *c2;
    size_t    scap, valid;      /* prefixes known for slots < valid       */
    /* the run */
    uint32_t *len;              /* L at each step                         */
    uint32_t *minpos;           /* the lowest X-headed item's position; 0 none */
    uint8_t  *ym1;              /* an X-headed item at L-1, the y-seat    */
    size_t    nlen, lcap;
    int64_t   last_restart;     /* -1: none                               */
    /* dumps */
    uint64_t *dump;             /* sorted steps to dump                   */
    size_t    ndump;
    bool      dump_halt;        /* dump the final frame at a halt         */
    uint8_t  *printed;          /* per node: already in the table         */
    size_t    pcap;
    uint32_t *todo;
    size_t    tcap;
};

/*  ------------------------------------------------------------- output */

static void emit(av_trace *t, const char *s, size_t n) {
    if (!t->out) return;                    /* a silent pass */
    if (t->blen + n > t->bcap) {
        if (t->blen) fwrite(t->buf, 1, t->blen, t->out);
        t->blen = 0;
        if (n > t->bcap) { fwrite(s, 1, n, t->out); return; }
    }
    memcpy(t->buf + t->blen, s, n);
    t->blen += n;
}

static void emit_u64(av_trace *t, uint64_t v) {
    char tmp[24];
    int n = 0;
    char rev[24];
    do { rev[n++] = (char)('0' + v % 10); v /= 10; } while (v);
    for (int i = 0; i < n; i++) tmp[i] = rev[n - 1 - i];
    emit(t, tmp, (size_t)n);
}

void av_trace_flush(av_trace *t) {
    if (!t->out) return;
    if (t->blen) fwrite(t->buf, 1, t->blen, t->out);
    t->blen = 0;
    fflush(t->out);
}

/*  ---------------------------------------------------------- the facts */

static bool grow_nodes(av_trace *t, uint32_t need) {
    if (need <= t->ncap) return true;
    uint32_t cap = t->ncap ? t->ncap : 1024;
    while (cap < need) cap *= 2;
    uint8_t *fl = realloc(t->fl, cap), *sg = realloc(t->sig, cap);
    if (fl) t->fl = fl;
    if (sg) t->sig = sg;
    uint32_t *ar = realloc(t->ar, (size_t)cap * sizeof *ar);
    if (ar) t->ar = ar;
    if (!fl || !sg || !ar) return false;
    memset(t->fl + t->ncap, 0, cap - t->ncap);
    t->ncap = cap;
    return true;
}

/*  Facts for every node up to i, in index order. */
static bool facts_upto(av_trace *t, const av_arena *a, uint32_t i) {
    if (i < t->done) return true;
    if (!grow_nodes(t, i + 1)) { t->bad = true; return false; }
    for (uint32_t j = t->done; j <= i; j++) {
        uint32_t tag = av_tag(a, j);
        uint8_t f = F_DONE, s = 0;
        uint32_t ar = 0;
        if (tag == AV_APP) {
            uint32_t l = av_left(a, j), r = av_right(a, j);
            if (l >= j || r >= j || !(t->fl[l] & F_DONE) || !(t->fl[r] & F_DONE)) {
                t->bad = true;              /* children not older: not a trace run */
                return false;
            }
            if (t->fl[l] & F_XH) f |= F_XH;
            if ((t->fl[l] | t->fl[r]) & F_CX) f |= F_CX;
            unsigned sg = t->sig[l] + ((t->fl[r] & F_XH) ? 1u : 0u);
            s = (uint8_t)(sg > 2 ? 2 : sg);
            ar = t->ar[l] + 1;
        } else if (tag == AV_LEAF) {
            if (j == t->pass) f |= F_XH | F_CX;
            else if (j != AV_NODE_S) {
                /* K, I and other atoms are outside the calculus traced;
                 * they may exist unreached (leaves are interned at
                 * startup), so they are marked, not refused, here */
                f |= 8;
            }
        } else {
            t->bad = true;
            return false;
        }
        t->fl[j] = f;
        t->sig[j] = s;
        t->ar[j] = ar;
    }
    t->done = i + 1;
    return true;
}

/*  ----------------------------------------------------------- creation */

av_trace *av_trace_new(av_arena *a, const char *passenger, bool steps_out, FILE *out) {
    av_trace *t = calloc(1, sizeof *t);
    if (!t) return NULL;
    t->pass = av_leaf(a, passenger, strlen(passenger));
    t->steps_out = steps_out;
    t->out = out;
    t->bcap = 1 << 16;
    t->buf = malloc(t->bcap);
    t->last_restart = -1;
    if (t->pass == AV_NONE || !t->buf) { av_trace_free(t); return NULL; }
    return t;
}

void av_trace_free(av_trace *t) {
    if (!t) return;
    free(t->buf);
    free(t->fl); free(t->sig); free(t->ar);
    free(t->cX); free(t->c1); free(t->c2);
    free(t->len);
    free(t->minpos);
    free(t->ym1);
    free(t->dump);
    free(t->printed);
    free(t->todo);
    free(t);
}

static int cmp_u64(const void *x, const void *y) {
    uint64_t a = *(const uint64_t *)x, b = *(const uint64_t *)y;
    return (a > b) - (a < b);
}

void av_trace_dump_halt(av_trace *t, bool on) {
    t->dump_halt = on;
}

bool av_trace_dump_at(av_trace *t, const uint64_t *steps, size_t n) {
    uint64_t *d = realloc(t->dump, (n ? n : 1) * sizeof *d);
    if (!d) return false;
    memcpy(d, steps, n * sizeof *d);
    qsort(d, n, sizeof *d, cmp_u64);
    t->dump = d;
    t->ndump = n;
    return true;
}

static bool dumps(const av_trace *t, uint64_t step) {
    size_t lo = 0, hi = t->ndump;
    while (lo < hi) {
        size_t mid = (lo + hi) / 2;
        if (t->dump[mid] < step) lo = mid + 1; else hi = mid;
    }
    return lo < t->ndump && t->dump[lo] == step;
}

bool av_trace_check(av_trace *t, const av_arena *a, uint32_t root) {
    /* every node reachable is S, the passenger, or an application of them;
     * the facts are filled for the whole arena, then the term is walked */
    if (a->used == 0 || !facts_upto(t, a, a->used - 1)) return false;
    size_t cap = 64, top = 0;
    uint32_t *stk = malloc(cap * sizeof *stk);
    uint8_t *seen = calloc(a->used, 1);
    bool ok = stk && seen;
    if (ok) stk[top++] = root;
    while (ok && top) {
        uint32_t x = stk[--top];
        if (seen[x]) continue;
        seen[x] = 1;
        if (t->fl[x] & 8) { ok = false; break; }
        if (av_tag(a, x) == AV_APP) {
            if (top + 2 > cap) {
                uint32_t *q = realloc(stk, (cap *= 2) * sizeof *q);
                if (!q) { ok = false; break; }
                stk = q;
            }
            stk[top++] = av_left(a, x);
            stk[top++] = av_right(a, x);
        }
    }
    free(stk);
    free(seen);
    return ok;
}

/*  --------------------------------------------------------- the node table */

static bool grow_printed(av_trace *t, size_t need) {
    if (need <= t->pcap) return true;
    size_t cap = t->pcap ? t->pcap : 1024;
    while (cap < need) cap *= 2;
    uint8_t *p = realloc(t->printed, cap);
    if (!p) return false;
    memset(p + t->pcap, 0, cap - t->pcap);
    t->printed = p;
    t->pcap = cap;
    return true;
}

static int cmp_u32(const void *x, const void *y) {
    uint32_t a = *(const uint32_t *)x, b = *(const uint32_t *)y;
    return (a > b) - (a < b);
}

/*  Print every node below the items not yet printed, children first: the
 *  children of a node are older, so ascending index order is topological. */
static bool table(av_trace *t, const av_arena *a, const uint32_t *items, size_t n) {
    if (!grow_printed(t, a->used)) return false;
    size_t top = 0, got = 0;
    uint32_t *found = NULL;
    size_t fcap = 0;
    for (size_t i = 0; i < n; i++) {
        if (top + 1 > t->tcap) {
            size_t c = t->tcap ? 2 * t->tcap : 256;
            uint32_t *q = realloc(t->todo, c * sizeof *q);
            if (!q) { free(found); return false; }
            t->todo = q; t->tcap = c;
        }
        t->todo[top++] = items[i];
        while (top) {
            uint32_t x = t->todo[--top];
            if (t->printed[x]) continue;
            t->printed[x] = 1;
            if (got == fcap) {
                fcap = fcap ? 2 * fcap : 256;
                uint32_t *q = realloc(found, fcap * sizeof *q);
                if (!q) { free(found); return false; }
                found = q;
            }
            found[got++] = x;
            if (av_tag(a, x) == AV_APP) {
                if (top + 2 > t->tcap) {
                    size_t c = 2 * t->tcap + 2;
                    uint32_t *q = realloc(t->todo, c * sizeof *q);
                    if (!q) { free(found); return false; }
                    t->todo = q; t->tcap = c;
                }
                t->todo[top++] = av_left(a, x);
                t->todo[top++] = av_right(a, x);
            }
        }
    }
    qsort(found, got, sizeof *found, cmp_u32);
    for (size_t i = 0; i < got; i++) {
        uint32_t x = found[i];
        emit(t, "d ", 2);
        emit_u64(t, x);
        if (av_tag(a, x) == AV_APP) {
            emit(t, "=", 1);
            emit_u64(t, av_left(a, x));
            emit(t, ".", 1);
            emit_u64(t, av_right(a, x));
            emit(t, "\n", 1);
        } else {
            emit(t, x == t->pass ? "=X\n" : "=S\n", 3);
        }
    }
    free(found);
    return true;
}

/*  A frame dumped: its nodes' table, then `f <step>` and its items from the
 *  x-seat on. */
static bool frame_out(av_trace *t, const av_arena *a, uint64_t step,
                      const uint32_t *items, size_t n) {
    if (!table(t, a, items, n)) return false;
    emit(t, "f ", 2);
    emit_u64(t, step);
    for (size_t i = 0; i < n; i++) {
        emit(t, " ", 1);
        emit_u64(t, items[i]);
    }
    emit(t, "\n", 1);
    return true;
}

/*  ------------------------------------------------------------- a step */

static bool grow_slots(av_trace *t, size_t need) {
    if (need <= t->scap) return true;
    size_t cap = t->scap ? t->scap : 256;
    while (cap < need) cap *= 2;
    uint32_t *x = realloc(t->cX, cap * sizeof *x);
    if (x) t->cX = x;
    uint32_t *y = realloc(t->c1, cap * sizeof *y);
    if (y) t->c1 = y;
    uint32_t *z = realloc(t->c2, cap * sizeof *z);
    if (z) t->c2 = z;
    if (!x || !y || !z) return false;
    t->scap = cap;
    return true;
}

/*  The slot of the k-th X-headed item from the bottom (k >= 1). */
static size_t kth(const av_trace *t, size_t top, uint32_t k) {
    size_t lo = 0, hi = top - 1;
    while (lo < hi) {
        size_t mid = (lo + hi) / 2;
        if (t->cX[mid] >= k) hi = mid; else lo = mid + 1;
    }
    return lo;
}

bool trace_step(av_trace *t, const av_arena *a, const uint32_t *stk, size_t base,
                size_t top, uint64_t step) {
    if (t->bad || base != 0) { t->bad = true; return false; }
    uint32_t most = 0;
    for (size_t i = t->valid < top ? t->valid : top; i < top; i++)
        if (stk[i] > most) most = stk[i];
    if (!facts_upto(t, a, most) || !grow_slots(t, top)) { t->bad = true; return false; }
    for (size_t i = t->valid < top ? t->valid : top; i < top; i++) {
        uint32_t u = stk[i];
        uint32_t px = i ? t->cX[i - 1] : 0, p1 = i ? t->c1[i - 1] : 0, p2 = i ? t->c2[i - 1] : 0;
        t->cX[i] = px + ((t->fl[u] & F_XH) ? 1u : 0u);
        t->c1[i] = p1 + (t->sig[u] >= 1 ? 1u : 0u);
        t->c2[i] = p2 + (t->sig[u] >= 2 ? 1u : 0u);
    }
    /* the step to come pops the top three and pushes above them */
    t->valid = top >= 3 ? top - 3 : 0;

    size_t L = top - base;
    if (t->nlen == t->lcap) {
        size_t c = t->lcap ? 2 * t->lcap : 1024;
        uint32_t *q = realloc(t->len, c * sizeof *q);
        if (q) t->len = q;
        uint32_t *m = realloc(t->minpos, c * sizeof *m);
        if (m) t->minpos = m;
        uint8_t *y = realloc(t->ym1, c);
        if (y) t->ym1 = y;
        if (!q || !m || !y) { t->bad = true; return false; }
        t->lcap = c;
    }
    uint32_t np = t->cX[top - 1];
    t->len[t->nlen] = (uint32_t)L;
    t->minpos[t->nlen] = np ? (uint32_t)(kth(t, top, 1) - base + 1) : 0;
    t->ym1[t->nlen] = L >= 2 && (t->fl[stk[top - 2]] & F_XH);
    t->nlen++;
    if (np == 1) {
        size_t p = kth(t, top, 1);
        if (L == 3 && p == base) t->last_restart = (int64_t)step;
    }
    if (t->steps_out) {
        emit_u64(t, step);
        emit(t, " ", 1);
        emit_u64(t, L);
        emit(t, " ", 1);
        if (np == 0) emit(t, "-", 1);
        for (uint32_t k = np; k >= 1; k--) {        /* front first, as the oracle's indices */
            emit_u64(t, kth(t, top, k) - base + 1);
            if (k > 1) emit(t, ",", 1);
        }
        char ev = '-';
        if (np >= 1) {
            size_t pos = kth(t, top, np) - base + 1;   /* the front-most */
            ev = pos == L ? 'o' : pos == L - 1 ? 'y' : pos == L - 2 ? 'z' : '-';
        }
        if (np == 1) {
            size_t p = kth(t, top, 1);
            uint32_t D = (t->c1[top - 1] - t->c1[p]) + (p > base ? t->c2[p - 1] : 0);
            emit(t, " ", 1);
            emit_u64(t, p - base);                 /* d = pos - 1 */
            emit(t, " ", 1);
            emit_u64(t, D);
        } else {
            emit(t, " - -", 4);
        }
        char tail[4] = { ' ', ev, ' ', 0 };
        emit(t, tail, 3);
        emit_u64(t, t->ar[stk[top - 1]]);
        emit(t, "\n", 1);
    }
    if (t->ndump && dumps(t, step)) {
        uint32_t *items = malloc((L ? L : 1) * sizeof *items);
        if (!items) { t->bad = true; return false; }
        for (size_t i = 0; i < L; i++) items[i] = stk[top - 1 - i];
        bool ok = frame_out(t, a, step, items, L);
        free(items);
        if (!ok) { t->bad = true; return false; }
    }
    return true;
}

/*  ------------------------------------------------------------ the end */

/*  The final frame: the arguments of the result's head, x-seat first. */
static uint32_t *final_frame(const av_arena *a, uint32_t term, size_t *n, uint32_t *head) {
    size_t cap = 16, k = 0;
    uint32_t *v = malloc(cap * sizeof *v);
    if (!v) return NULL;
    uint32_t x = av_res(a, term);
    while (av_tag(a, x) == AV_APP) {
        if (k == cap) {
            uint32_t *q = realloc(v, (cap *= 2) * sizeof *q);
            if (!q) { free(v); return NULL; }
            v = q;
        }
        v[k++] = av_right(a, x);
        x = av_res(a, av_left(a, x));
    }
    for (size_t i = 0; i < k / 2; i++) {         /* x-seat first */
        uint32_t s = v[i]; v[i] = v[k - 1 - i]; v[k - 1 - i] = s;
    }
    *n = k;
    *head = x;
    return v;
}

bool av_trace_end(av_trace *t, const av_arena *a, av_status status, uint64_t steps,
                  uint32_t term, size_t conf, bool want_records, av_trace_summary *sum) {
    memset(sum, 0, sizeof *sum);
    sum->last_restart = t->last_restart;
    if (t->bad) return false;
    size_t n = 0;
    uint32_t head = AV_NONE;
    uint32_t *fr = term == AV_NONE ? NULL : final_frame(a, term, &n, &head);
    if (term != AV_NONE && !fr) return false;
    const char *kind = "-";
    if (status == AV_FUEL) {
        /* X at the head after the last step: step H-1 opened, and the
         * census reports OPEN there, though the horizon stopped the halt */
        kind = head == t->pass ? "OPEN" : "FUEL";
    } else if (status == AV_WHNF && head == t->pass) {
        kind = "OPEN";
    } else if (status == AV_WHNF && head == AV_NODE_S && n < 3) {
        uint32_t most = 0;
        for (size_t i = 0; i < n; i++) if (fr[i] > most) most = fr[i];
        if (!facts_upto(t, a, most)) { free(fr); return false; }
        bool xh = false;
        for (size_t i = 0; i < n; i++) xh |= (t->fl[fr[i]] & F_XH) != 0;
        kind = xh ? "HALT-X" : "HALT-B";
    }
    sum->kind = kind;
    emit(t, ". ", 2);
    emit(t, av_status_name(status), strlen(av_status_name(status)));
    emit(t, " ", 1);
    emit_u64(t, steps);
    emit(t, " ", 1);
    emit(t, kind, strlen(kind));
    emit(t, "\n", 1);
    /* the final frame: dumped when asked for by its step, or at a halt */
    bool halted = kind[0] == 'H';
    if (fr && ((t->ndump && dumps(t, steps)) || (t->dump_halt && halted)) &&
        !frame_out(t, a, steps, fr, n)) {
        free(fr);
        return false;
    }
    free(fr);
    if (want_records && kind[0] == 'F') {
        /* records: L_n < L_m for every later step m; confirmed: n + conf <= H */
        size_t H = t->nlen;
        uint8_t *rec = calloc(H ? H : 1, 1);
        if (!rec) return false;
        uint32_t minL = UINT32_MAX;
        for (size_t i = H; i-- > 0;)
            if (t->len[i] < minL) { rec[i] = 1; minL = t->len[i]; }
        emit(t, "R", 1);
        for (size_t i = 0; i < H; i++)
            if (rec[i]) { emit(t, " ", 1); emit_u64(t, i); }
        emit(t, "\nC", 2);
        for (size_t i = 0; i < H; i++)
            if (rec[i] && i + conf <= H) {
                emit(t, " ", 1);
                emit_u64(t, i);
                sum->nconf++;
            }
        emit(t, "\n", 1);
        /* each confirmed record's facts the census decides on: L, the
         * lowest X-headed position (- none), and an X-headed item at L-1 */
        for (size_t i = 0; i < H; i++)
            if (rec[i] && i + conf <= H) {
                emit(t, "K ", 2);
                emit_u64(t, i);
                emit(t, " ", 1);
                emit_u64(t, t->len[i]);
                emit(t, " ", 1);
                if (t->minpos[i]) emit_u64(t, t->minpos[i]); else emit(t, "-", 1);
                emit(t, t->ym1[i] ? " 1\n" : " 0\n", 3);
            }
        free(rec);
    }
    return true;
}

/*  The confirmed records' steps n and n+1, for a second pass's dumps. */
size_t av_trace_record_steps(const av_trace *t, size_t conf, uint64_t **out) {
    size_t H = t->nlen, k = 0;
    uint64_t *v = malloc((2 * H + 1) * sizeof *v);
    if (!v) { *out = NULL; return 0; }
    uint32_t minL = UINT32_MAX;
    uint8_t *rec = calloc(H ? H : 1, 1);
    if (!rec) { free(v); *out = NULL; return 0; }
    for (size_t i = H; i-- > 0;)
        if (t->len[i] < minL) { rec[i] = 1; minL = t->len[i]; }
    for (size_t i = 0; i < H; i++)
        if (rec[i] && i + conf <= H) { v[k++] = i; v[k++] = i + 1; }
    free(rec);
    *out = v;
    return k;
}

/*  The frames the census reads, in its order over the confirmed records
 *  (fixed_points_hider.run): at a record n with an X-headed item at or
 *  below L-3, frame n, and it stops; else with one at L-1, frame n+1, and
 *  it stops; else frame n+1, for the record's mint, and it goes on.  Which
 *  frames, not what they certify: that stays with the census. */
size_t av_trace_census_steps(const av_trace *t, size_t conf, uint64_t **out) {
    size_t H = t->nlen, k = 0;
    uint64_t *v = malloc((H + 1) * sizeof *v);
    uint8_t *rec = calloc(H ? H : 1, 1);
    if (!v || !rec) { free(v); free(rec); *out = NULL; return 0; }
    uint32_t minL = UINT32_MAX;
    for (size_t i = H; i-- > 0;)
        if (t->len[i] < minL) { rec[i] = 1; minL = t->len[i]; }
    for (size_t i = 0; i < H; i++) {
        if (!rec[i] || i + conf > H) continue;
        if (t->minpos[i] && t->minpos[i] + 3 <= t->len[i]) { v[k++] = i; break; }
        v[k++] = i + 1;
        if (t->ym1[i]) break;
    }
    free(rec);
    *out = v;
    return k;
}

uint64_t av_trace_steps_seen(const av_trace *t) {
    return t->nlen;
}
