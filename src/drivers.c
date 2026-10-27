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
    return true;
}

/*  ------------------------------------------------------------ the answers
 *
 *  A request is read from its card first, the same whether the log or the
 *  world answers it; the answer is a payload (avon.h), from which its
 *  reply is built. */

typedef struct {
    uint32_t id;                /* the id's normal form */
    uint64_t max;               /* a read's most bytes */
    uint8_t *name;              /* a variable's name, NUL-terminated */
    size_t   nlen;
} request;

/*  The request card tag holds in data, into *q: false if it is no
 *  driver's (*err unset) or memory ran out (*err set). */
static bool read_request(av_arena *a, av_run *d, uint64_t tag, uint32_t data, const av_opts *po,
                         request *q, const char **err) {
    uint32_t id = data, args = AV_NONE;
    q->name = NULL;
    if (tag == TAG_ENTROPY && !d->entropy) return false;
    if (tag == TAG_READ || tag == TAG_ENV) {
        if (!pair_of(a, data, po, &id, &args)) return false;
    }
    if ((q->id = read_id(a, id, po)) == AV_NONE) return false;
    if (tag == TAG_READ) {
        uint32_t f, m;
        uint64_t fd;
        return pair_of(a, args, po, &f, &m) && read_nat(a, f, po, 0, &fd) &&
               read_nat(a, m, po, READ_MAX, &q->max) && q->max != 0;
    }
    if (tag == TAG_ENV) {
        bool oom = false;
        if (!read_bytes(a, args, po, &q->name, &q->nlen, &oom)) {
            if (oom) *err = "out of memory";
            return false;
        }
        uint8_t *z = realloc(q->name, q->nlen + 1);
        if (!z) { free(q->name); q->name = NULL; *err = "out of memory"; return false; }
        z[q->nlen] = 0;
        q->name = z;
    }
    return true;
}

static bool put_le(uint8_t **pay, size_t *n, uint64_t v, unsigned bytes) {
    uint8_t *b = realloc(*pay, *n + bytes);
    if (!b) return false;
    for (unsigned i = 0; i < bytes; i++) b[*n + i] = (uint8_t)(v >> 8 * i);
    *pay = b;
    *n += bytes;
    return true;
}

static bool put_bytes(uint8_t **pay, size_t *n, const void *src, size_t len) {
    uint8_t *b = realloc(*pay, *n + len + 1);
    if (!b) return false;
    memcpy(b + *n, src, len);
    *pay = b;
    *n += len;
    return true;
}

static uint64_t get_le(const uint8_t *b, unsigned bytes) {
    uint64_t v = 0;
    for (unsigned i = 0; i < bytes; i++) v |= (uint64_t)b[i] << 8 * i;
    return v;
}

/*  What the world answers request q of tag: its payload, or false with
 *  *err when the world failed. */
static bool world_payload(av_run *d, unsigned tag, const request *q, uint8_t **pay, size_t *n,
                          const char **err) {
    *pay = NULL;
    *n = 0;
    bool ok = true;
    if (tag == AV_RUN_BOOT) {
        uint8_t b[AV_ENY_BYTES];
        ok = put_le(pay, n, d->entropy, 1);
        if (ok && d->entropy) {
            if (!draw(d, b, err)) { free(*pay); *pay = NULL; return false; }
            ok = put_bytes(pay, n, b, AV_ENY_BYTES);
        }
        for (int i = 0; ok && i < d->argc; i++) {
            size_t len = strlen(d->argv[i]);
            ok = len <= UINT32_MAX && put_le(pay, n, len, 4) && put_bytes(pay, n, d->argv[i], len);
        }
    } else if (tag == TAG_ENTROPY) {
        uint8_t b[AV_ENY_BYTES];
        if (!draw(d, b, err)) return false;
        ok = put_bytes(pay, n, b, AV_ENY_BYTES);
    } else if (tag == TAG_READ) {
        if (!(*pay = malloc(q->max))) ok = false;
        else {
            ssize_t r = read_up_to(d->fd[0], *pay, q->max);
            if (r < 0) { free(*pay); *pay = NULL; *err = "cannot read standard input"; return false; }
            *n = (size_t)r;
        }
    } else if (tag == TAG_ENV) {
        const char *v = memchr(q->name, 0, q->nlen) ? NULL : getenv((const char *)q->name);
        if (v) ok = put_le(pay, n, 1, 1) && put_bytes(pay, n, v, strlen(v));
    } else {
        ok = put_le(pay, n, d->steps, 8);
    }
    if (!ok) { free(*pay); *pay = NULL; *err = "out of memory"; }
    return ok;
}

/*  The reply event to request q of tag with payload pay: AV_NONE if the
 *  payload is not one of tag's (*err set) or memory ran out. */
static uint32_t reply_of(av_arena *a, unsigned tag, const request *q, const uint8_t *pay, size_t n,
                         const char **err) {
    uint32_t ans = AV_NONE;
    bool shaped = true;
    if (tag == AV_RUN_BOOT) {
        shaped = n >= 1 && pay[0] <= 1 && n >= 1u + (pay[0] ? AV_ENY_BYTES : 0);
        size_t at = shaped ? 1u + (pay[0] ? AV_ENY_BYTES : 0) : 0, argc = 0;
        for (size_t i = at; shaped && i < n; argc++) {
            uint64_t len = n - i >= 4 ? get_le(pay + i, 4) : UINT64_MAX;
            shaped = len <= n - i - 4;
            i += shaped ? 4 + len : 0;
        }
        if (shaped) {
            /* the arguments last first, as cons builds */
            size_t *starts = argc ? malloc(argc * sizeof *starts) : NULL;
            if (argc && !starts) return AV_NONE;
            size_t j = 0;
            for (size_t i = at; i < n; j++) { starts[j] = i; i += 4 + get_le(pay + i, 4); }
            uint32_t args = AV_NODE_K;
            for (size_t m = argc; m-- > 0 && args != AV_NONE;)
                args = cons(a, byte_list(a, pay + starts[m] + 4, get_le(pay + starts[m], 4)), args);
            free(starts);
            uint32_t bits = pay[0] ? bits_list(a, pay + 1) : AV_NODE_K;
            ans = args == AV_NONE || bits == AV_NONE ? AV_NONE : cell(a, args, bits);
        }
    } else if (tag == TAG_ENTROPY) {
        if ((shaped = n == AV_ENY_BYTES)) ans = bits_list(a, pay);
    } else if (tag == TAG_READ) {
        if ((shaped = n <= q->max)) ans = byte_list(a, pay, n);
    } else if (tag == TAG_ENV) {
        if ((shaped = n == 0 || pay[0] == 1))
            ans = n ? cons(a, byte_list(a, pay + 1, n - 1), AV_NODE_K) : AV_NODE_K;
    } else {
        if ((shaped = n == 8)) ans = numeral(a, get_le(pay, 8));
    }
    if (!shaped) { *err = "a logged answer is not of its request's shape"; return AV_NONE; }
    uint32_t ev = reply(a, q->id, ans);
    if (ev == AV_NONE) *err = "out of memory";
    return ev;
}

/*  ---------------------------------------------------------------- the run */

/*  Request q's reply: from the log while it answers, else from the world,
 *  kept first.  AV_NONE with *err, or with d->stopped. */
static uint32_t settle(av_kernel *k, av_run *d, unsigned tag, const request *q,
                       uint64_t live_fuel, const char **err) {
    av_arena *a = k->a;
    uint8_t *pay = NULL;
    size_t n = 0;
    bool logged = false;
    if (d->replaying) {
        logged = d->log->replay(d->log->ctx, a, tag, q->id, &pay, &n, err);
        if (*err) return AV_NONE;
        if (!logged) {                          /* live from here */
            d->replaying = false;
            k->o.max_steps = live_fuel;
        }
    }
    if (!logged) {
        if (d->max_pokes && d->pokes >= d->max_pokes) { d->stopped = true; return AV_NONE; }
        if (tag == AV_RUN_BOOT && d->boot_pay) {  /* kept when the pier was made */
            if (!(pay = malloc(d->boot_n + 1))) { *err = "out of memory"; return AV_NONE; }
            memcpy(pay, d->boot_pay, d->boot_n);
            n = d->boot_n;
        } else if (!world_payload(d, tag, q, &pay, &n, err)) {
            return AV_NONE;
        } else if (d->log && !d->log->keep(d->log->ctx, a, tag, q->id, pay, n, err)) {
            free(pay);
            return AV_NONE;
        }
    }
    if (tag == TAG_ENTROPY || (tag == AV_RUN_BOOT && n && pay[0])) d->draws++;
    uint32_t ev = reply_of(a, tag, q, pay, n, err);
    free(pay);
    return ev;
}

av_status av_run_kernel(av_kernel *k, av_run *d, av_result *r, const char **err) {
    av_arena *a = k->a;
    d->status = 0;
    d->steps = d->pokes = d->passed = d->draws = 0;
    d->stopped = false;
    d->replaying = d->log != NULL;
    uint64_t live_fuel = k->o.max_steps;
    if (d->replaying) k->o.max_steps = UINT64_MAX / 2;  /* every logged answer applied once */
    walk w = { .card = AV_NONE };
    av_active me = { walk_roots, NULL, &w, a->active };
    a->active = &me;
    av_status st = AV_WHNF;
    *err = NULL;
    r->status = AV_WHNF;
    r->steps = 0;
    request boot = { .id = AV_NODE_K };
    uint32_t ev = settle(k, d, AV_RUN_BOOT, &boot, live_fuel, err);
    /* the event's answer is the log's last, to cut if it does not apply;
     * a new pier's boot answer stays, with the arguments */
    bool kept = !d->replaying && d->log && !d->boot_pay;
    while (ev != AV_NONE) {
        uint32_t eff;
        st = av_kernel_poke(k, ev, &eff, r);
        if (st != AV_WHNF) {
            *err = d->replaying ? "a logged answer does not replay"
                                : "a poke did not reach weak head normal form";
            if (kept && !d->log->cut(d->log->ctx))
                *err = "a poke did not reach weak head normal form, and its answer could not "
                       "be removed from the log";
            goto done;
        }
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
                    bool ok = d->replaying || write_all(d->fd[fd], b, n);
                    free(b);
                    if (!ok) { *err = fd == 1 ? "cannot write standard output" : "cannot write standard error"; break; }
                    done = true;
                } else if (oom) {
                    *err = "out of memory";
                    break;
                }
            } else if (tag <= TAG_STEPS) {
                request q;
                if (read_request(a, d, tag, data, &po, &q, err)) {
                    av_root_push(a, &q.id);
                    ev = settle(k, d, (unsigned)tag, &q, live_fuel, err);
                    kept = !d->replaying && d->log && ev != AV_NONE;
                    av_root_pop(a);
                    done = ev != AV_NONE;
                }
                free(q.name);
                if (*err || d->stopped) break;
            }
            if (!done) d->passed++;
            w.card = AV_NONE;
        }
        if (*err || d->stopped) break;
    }
    if (*err) { st = AV_SIZE; r->status = AV_SIZE; }
done:
    k->o.max_steps = live_fuel;
    a->active = me.next;
    free(w.q);
    return st;
}

bool av_run_boot_payload(av_run *d, uint8_t **pay, size_t *n, const char **err) {
    request boot = { .id = AV_NODE_K };
    *err = NULL;
    return world_payload(d, AV_RUN_BOOT, &boot, pay, n, err);
}
