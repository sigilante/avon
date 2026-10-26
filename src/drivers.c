/**  drivers.c
 *
 *  A kernel run as a program (DESIGN.md §9.2, SKIjack SPEC.md §4.1): the
 *  kernel emits cards [tag data], and the run performs them.  The walk is
 *  first in, first out, as skijack.drivers walks it: a poke's cards in list
 *  order, a write performed when the walk reaches it, a request answered
 *  with a reply poked then and there, the reply's own cards queued behind
 *  those not yet taken.  An exit card ends the run; a card of no driver's
 *  shape passes through.  The run keeps its log in memory, so it is
 *  av_run_kernel's caller that makes it durable or not.
 */

#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <sys/random.h>
#include <unistd.h>

#include "avon.h"
#include "jets.h"

enum { TAG_ENTROPY, TAG_WRITE, TAG_READ, TAG_ENV, TAG_STEPS, TAG_EXIT };

/*  A read's buffer at most; a larger max reads this much. */
#define READ_MAX (1u << 20)

/*  The queue of effect lists not yet walked, and the card being taken:
 *  roots, through the run's av_active, since every poke may collect. */
typedef struct {
    uint32_t *q;
    size_t    head, n, cap;
    uint32_t  card;
} walk;

static void walk_roots(av_gc *g, void *ctx) {
    walk *w = ctx;
    for (size_t i = w->head; i < w->n; i++) w->q[i] = av_gc_evac(g, w->q[i]);
    if (w->card != AV_NONE) w->card = av_gc_evac(g, w->card);
}

static bool walk_push(walk *w, uint32_t list) {
    if (w->n == w->cap) {
        if (w->head) {                          /* reuse the walked front */
            memmove(w->q, w->q + w->head, (w->n - w->head) * sizeof *w->q);
            w->n -= w->head;
            w->head = 0;
        }
        if (w->n == w->cap) {
            size_t c = w->cap ? 2 * w->cap : 64;
            uint32_t *v = realloc(w->q, c * sizeof *v);
            if (!v) return false;
            w->q = v;
            w->cap = c;
        }
    }
    w->q[w->n++] = list;
    return true;
}

/*  -------------------------------------------------------------- building
 *
 *  The encodings the pier builds: a cell λc. c x y, nil K, cons h t =
 *  K [h t], a numeral K or SUC n, a Boolean K or K I.  Building never
 *  collects. */

static uint32_t cell(av_arena *a, uint32_t x, uint32_t y) {
    uint32_t si = av_app(a, AV_NODE_S, AV_NODE_I);
    uint32_t kx = av_app(a, AV_NODE_K, x), ky = av_app(a, AV_NODE_K, y);
    uint32_t f = si == AV_NONE || kx == AV_NONE ? AV_NONE : av_app(a, si, kx);
    uint32_t g = f == AV_NONE ? AV_NONE : av_app(a, AV_NODE_S, f);
    return g == AV_NONE || ky == AV_NONE ? AV_NONE : av_app(a, g, ky);
}

static uint32_t cons(av_arena *a, uint32_t h, uint32_t t) {
    uint32_t c = h == AV_NONE || t == AV_NONE ? AV_NONE : cell(a, h, t);
    return c == AV_NONE ? AV_NONE : av_app(a, AV_NODE_K, c);
}

static uint32_t suc_term(av_arena *a) {
    uint32_t kk = av_app(a, AV_NODE_K, AV_NODE_K);
    uint32_t si = av_app(a, AV_NODE_S, AV_NODE_I);
    uint32_t ksi = si == AV_NONE ? AV_NONE : av_app(a, AV_NODE_K, si);
    uint32_t sksi = ksi == AV_NONE ? AV_NONE : av_app(a, AV_NODE_S, ksi);
    uint32_t r = sksi == AV_NONE ? AV_NONE : av_app(a, sksi, AV_NODE_K);
    uint32_t skk = kk == AV_NONE ? AV_NONE : av_app(a, AV_NODE_S, kk);
    return skk == AV_NONE || r == AV_NONE ? AV_NONE : av_app(a, skk, r);
}

/*  The numeral n: a word when words are on (share mode's --data), held as
 *  a number, and otherwise n successors over K. */
static uint32_t numeral(av_arena *a, uint64_t n) {
    uint32_t t = AV_NODE_K;
    if (a->word_suc && n < AV_WORD_MAX) {
        if (n > (UINT32_MAX - 2) / 2 || !av_reserve(a, (uint32_t)(2 * n + 2))) return AV_NONE;
        for (uint64_t i = 0; i < n && t != AV_NONE; i++) t = word_succ(a, t);
        return t;
    }
    uint32_t suc = suc_term(a);
    for (uint64_t i = 0; i < n && t != AV_NONE && suc != AV_NONE; i++) t = av_app(a, suc, t);
    return suc == AV_NONE ? AV_NONE : t;
}

static uint32_t byte_list(av_arena *a, const uint8_t *b, size_t n) {
    uint32_t t = AV_NODE_K;
    for (size_t i = n; i-- > 0 && t != AV_NONE;) t = cons(a, numeral(a, b[i]), t);
    return t;
}

/*  Bit 8i + j is bit j of byte i, least significant first. */
static uint32_t bits_list(av_arena *a, const uint8_t b[AV_ENY_BYTES]) {
    uint32_t ki = av_app(a, AV_NODE_K, AV_NODE_I), t = AV_NODE_K;
    for (int i = 8 * AV_ENY_BYTES - 1; i >= 0 && t != AV_NONE && ki != AV_NONE; i--)
        t = cons(a, b[i / 8] >> (i % 8) & 1u ? AV_NODE_K : ki, t);
    return t;
}

static uint32_t reply(av_arena *a, uint32_t id, uint32_t answer) {
    uint32_t inner = id == AV_NONE || answer == AV_NONE ? AV_NONE : cell(a, id, answer);
    return inner == AV_NONE ? AV_NONE : cell(a, AV_NODE_K, inner);
}

/*  --------------------------------------------------------------- probing
 *
 *  Copy mode, never collecting, a million contractions a probe: a card
 *  whose fields do not settle within that is no card. */

static av_opts probe_opts(const av_kernel *k) {
    av_opts po = k->o;
    po.strategy = AV_COPY;
    po.no_collect = true;
    po.whnf_only = true;
    po.max_steps = 1000000;
    return po;
}

static bool pair_of(av_arena *a, uint32_t t, const av_opts *po, uint32_t *x, uint32_t *y) {
    av_peeled p;
    if (!av_peel(a, t, 1, po, &p, NULL) || p.ctor != 0 || p.nfields != 2) return false;
    *x = p.field[0];
    *y = p.field[1];
    return true;
}

/*  A numeral's value, at most limit; false for anything else. */
static bool read_nat(av_arena *a, uint32_t t, const av_opts *po, uint64_t limit, uint64_t *v) {
    for (uint64_t n = 0;; n++) {
        if (n > limit) return false;
        uint32_t w;
        if (av_numeral(a, t, &w)) {             /* a word: its value at once */
            if (n + w > limit) return false;
            *v = n + w;
            return true;
        }
        av_peeled p;
        if (!av_peel(a, t, 2, po, &p, NULL)) return false;
        if (p.ctor == 0 && p.nfields == 0) { *v = n; return true; }
        if (p.ctor != 1 || p.nfields != 1) return false;
        t = p.field[0];
    }
}

/*  A list of numerals below 256, into a fresh buffer; false for anything
 *  else, or out of memory (*oom). */
static bool read_bytes(av_arena *a, uint32_t t, const av_opts *po, uint8_t **out, size_t *len,
                       bool *oom) {
    size_t n = 0, cap = 64;
    uint8_t *b = malloc(cap);
    if (!b) { *oom = true; return false; }
    for (;;) {
        av_peeled p;
        if (!av_peel(a, t, 2, po, &p, NULL)) break;
        if (p.ctor == 0 && p.nfields == 0) { *out = b; *len = n; return true; }
        if (p.ctor != 1 || p.nfields != 2) break;
        uint64_t v;
        if (!read_nat(a, p.field[0], po, 255, &v)) break;
        if (n == cap) {
            uint8_t *c = realloc(b, cap *= 2);
            if (!c) { *oom = true; break; }
            b = c;
        }
        b[n++] = (uint8_t)v;
        t = p.field[1];
    }
    free(b);
    return false;
}

/*  An id: its normal form, which the reply carries. */
static uint32_t read_id(av_arena *a, uint32_t t, const av_opts *po) {
    av_opts no = *po;
    no.whnf_only = false;
    av_result r = av_reduce(a, t, &no);
    a->probe_steps += r.steps;
    return r.status == AV_NORMAL ? r.term : AV_NONE;
}

/*  ------------------------------------------------------------- the world */

static bool write_all(int fd, const uint8_t *b, size_t n) {
    while (n) {
        ssize_t w = write(fd, b, n);
        if (w < 0 && errno == EINTR) continue;
        if (w <= 0) return false;
        b += w;
        n -= (size_t)w;
    }
    return true;
}

/*  At most max bytes, fewer only at the end of input: the reference host's
 *  read, which a pipe's short reads must not change. */
static ssize_t read_up_to(int fd, uint8_t *b, size_t max) {
    size_t n = 0;
    while (n < max) {
        ssize_t r = read(fd, b + n, max - n);
        if (r < 0 && errno == EINTR) continue;
        if (r < 0) return -1;
        if (r == 0) break;
        n += (size_t)r;
    }
    return (ssize_t)n;
}

static bool draw(av_run *d, uint8_t b[AV_ENY_BYTES], const char **err) {
    if (!d->entropy_file) {
        if (getentropy(b, AV_ENY_BYTES) != 0) { *err = "getentropy failed"; return false; }
    } else {
        FILE *f = fopen(d->entropy_file, "rb");
        if (!f) { *err = "cannot open the entropy file"; return false; }
        bool ok = fseeko(f, (off_t)(d->draws * AV_ENY_BYTES), SEEK_SET) == 0 &&
                  fread(b, 1, AV_ENY_BYTES, f) == AV_ENY_BYTES;
        fclose(f);
        if (!ok) { *err = "the entropy file has run out"; return false; }
    }
    d->draws++;
    return true;
}

/*  ---------------------------------------------------------------- the run */

static uint32_t boot_event(av_kernel *k, av_run *d, const char **err) {
    av_arena *a = k->a;
    uint32_t bits = AV_NODE_K;
    if (d->entropy) {
        uint8_t b[AV_ENY_BYTES];
        if (!draw(d, b, err)) return AV_NONE;
        bits = bits_list(a, b);
    }
    uint32_t args = AV_NODE_K;
    for (int i = d->argc; i-- > 0 && args != AV_NONE;)
        args = cons(a, byte_list(a, (const uint8_t *)d->argv[i], strlen(d->argv[i])), args);
    uint32_t ans = args == AV_NONE || bits == AV_NONE ? AV_NONE : cell(a, args, bits);
    uint32_t ev = reply(a, AV_NODE_K, ans);
    if (ev == AV_NONE) *err = "out of memory";
    return ev;
}

/*  The answer to a request card, or AV_NONE if it is no driver's (*err
 *  unset) or the world failed (*err set). */
static uint32_t answer(av_kernel *k, av_run *d, uint64_t tag, uint32_t data, const av_opts *po,
                       const char **err) {
    av_arena *a = k->a;
    uint32_t id = data, args = AV_NONE;
    if (tag == TAG_READ || tag == TAG_ENV) {
        if (!pair_of(a, data, po, &id, &args)) return AV_NONE;
    }
    if (tag == TAG_ENTROPY && !d->entropy) return AV_NONE;
    if ((id = read_id(a, id, po)) == AV_NONE) return AV_NONE;
    uint32_t ans = AV_NONE;
    if (tag == TAG_ENTROPY) {
        uint8_t b[AV_ENY_BYTES];
        if (!draw(d, b, err)) return AV_NONE;
        ans = bits_list(a, b);
    } else if (tag == TAG_READ) {
        uint32_t f, m;
        uint64_t fd, max;
        if (!pair_of(a, args, po, &f, &m) || !read_nat(a, f, po, 0, &fd) ||
            !read_nat(a, m, po, READ_MAX, &max) || max == 0)
            return AV_NONE;
        uint8_t *b = malloc(max);
        if (!b) { *err = "out of memory"; return AV_NONE; }
        ssize_t n = read_up_to(d->fd[0], b, max);
        if (n < 0) { free(b); *err = "cannot read standard input"; return AV_NONE; }
        ans = byte_list(a, b, (size_t)n);
        free(b);
    } else if (tag == TAG_ENV) {
        uint8_t *name;
        size_t len;
        bool oom = false;
        if (!read_bytes(a, args, po, &name, &len, &oom)) {
            if (oom) *err = "out of memory";
            return AV_NONE;
        }
        uint8_t *z = realloc(name, len + 1);
        if (!z) { free(name); *err = "out of memory"; return AV_NONE; }
        z[len] = 0;
        const char *v = memchr(z, 0, len) ? NULL : getenv((const char *)z);
        free(z);
        ans = v ? cons(a, byte_list(a, (const uint8_t *)v, strlen(v)), AV_NODE_K) : AV_NODE_K;
    } else {
        ans = numeral(a, d->steps);
    }
    uint32_t ev = reply(a, id, ans);
    if (ev == AV_NONE) *err = "out of memory";
    return ev;
}

av_status av_run_kernel(av_kernel *k, av_run *d, av_result *r, const char **err) {
    av_arena *a = k->a;
    d->status = 0;
    d->steps = d->pokes = d->passed = 0;
    walk w = { .card = AV_NONE };
    av_active me = { walk_roots, NULL, &w, a->active };
    a->active = &me;
    av_status st = AV_WHNF;
    *err = NULL;
    r->status = AV_WHNF;
    r->steps = 0;
    uint32_t ev = boot_event(k, d, err);
    while (ev != AV_NONE) {
        uint32_t eff;
        st = av_kernel_poke(k, ev, &eff, r);
        if (st != AV_WHNF) { *err = "a poke did not reach weak head normal form"; goto done; }
        d->steps += r->steps;
        d->pokes++;
        if (!walk_push(&w, eff)) { *err = "out of memory"; break; }
        ev = AV_NONE;
        av_opts po = probe_opts(k);
        while (ev == AV_NONE && w.head < w.n) {
            av_peeled l;
            if (!av_peel(a, w.q[w.head], 2, &po, &l, NULL) || l.ctor != 1 || l.nfields != 2) {
                w.head++;                       /* nil, or no list: no more cards there */
                continue;
            }
            w.card = l.field[0];
            w.q[w.head] = l.field[1];
            uint32_t tg, data;
            uint64_t tag = TAG_EXIT + 1;
            if (pair_of(a, w.card, &po, &tg, &data) && !read_nat(a, tg, &po, TAG_EXIT, &tag))
                tag = TAG_EXIT + 1;
            bool done = false;
            if (tag == TAG_EXIT) {
                uint64_t code;
                if (read_nat(a, data, &po, 255, &code)) {
                    d->status = (int)code;
                    goto done;
                }
            } else if (tag == TAG_WRITE) {
                uint32_t f, bs;
                uint64_t fd;
                uint8_t *b;
                size_t n;
                bool oom = false;
                if (pair_of(a, data, &po, &f, &bs) && read_nat(a, f, &po, 2, &fd) && fd >= 1 &&
                    read_bytes(a, bs, &po, &b, &n, &oom)) {
                    bool ok = write_all(d->fd[fd], b, n);
                    free(b);
                    if (!ok) { *err = fd == 1 ? "cannot write standard output" : "cannot write standard error"; break; }
                    done = true;
                } else if (oom) {
                    *err = "out of memory";
                    break;
                }
            } else if (tag <= TAG_STEPS) {
                ev = answer(k, d, tag, data, &po, err);
                if (*err) break;
                done = ev != AV_NONE;
            }
            if (!done) d->passed++;
            w.card = AV_NONE;
        }
        if (*err) break;
    }
    if (*err) { st = AV_SIZE; r->status = AV_SIZE; }
done:
    a->active = me.next;
    free(w.q);
    return st;
}
