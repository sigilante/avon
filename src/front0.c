/**  front0.c
 *
 *  Running the SKIjack-0 front end.  The front end consists of one term,
 *  `front`, that takes a program as a list of 7-bit character codes and
 *  reduces to every name's closed term: ROk (OCons name tm ..) or RErr.
 *  The input is built in the arena, each code's datum once and shared,
 *  and the result is read by probing---a Scott datum applied to one marker
 *  per constructor returns its own marker applied to its fields---into
 *  lines of a name and its term's hash.  No term is rebuilt.
 *
 *  The front end's work happens inside the probes, lazily, so unlike
 *  av_peel's these collect.  Every node the reader holds sits on one stack
 *  that a registered reduction record evacuates, and the memo of hashed
 *  nodes follows each collection.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "jets.h"

/*  The reader's stack entry: a node to read, or a node whose two fields'
 *  digests are on the digest stack and are to be joined into its own. */
enum { READ, JOIN };

typedef struct {
    av_arena *a;
    uint32_t *node;             /* rooted: the collector moves these      */
    uint8_t  *kind;
    size_t    n, cap;
    uint64_t *dig;              /* digests of the terms read so far       */
    size_t    nd, dcap;
    nmap      memo;             /* node -> digest, remapped on collection */
    ski_leaf  mark[5];          /* the markers' leaf ids                  */
    uint32_t  marknode[5];      /* rooted too: a collection moves leaves */
    uint64_t  steps, tmpl_calls, dispatches, fused, word_ops, fix_calls, joins;
    bool      lost;             /* a remap ran out of memory              */
} reader;

static void roots(av_gc *g, void *ctx) {
    reader *r = ctx;
    for (size_t i = 0; i < r->n; i++) r->node[i] = av_gc_evac(g, r->node[i]);
    for (unsigned i = 0; i < 5; i++) r->marknode[i] = av_gc_evac(g, r->marknode[i]);
}

static void after(av_gc *g, void *ctx) {
    reader *r = ctx;
    nmap old = r->memo, fresh = { 0 };
    for (size_t i = 0; i < old.cap; i++) {
        if (old.key[i] == AV_NONE) continue;
        uint32_t j = av_gc_forwarded(g, old.key[i]);
        if (j != AV_NONE && !nmap_put(&fresh, j, old.val[i])) r->lost = true;
    }
    nmap_free(&old);
    r->memo = fresh;
}

static bool push(reader *r, uint32_t node, uint8_t kind) {
    if (r->n == r->cap) {
        size_t cap = r->cap ? 2 * r->cap : 1024;
        uint32_t *nd = realloc(r->node, cap * sizeof *nd);
        if (!nd) return false;
        r->node = nd;
        uint8_t *kd = realloc(r->kind, cap * sizeof *kd);
        if (!kd) return false;
        r->kind = kd;
        r->cap = cap;
    }
    r->node[r->n] = node;
    r->kind[r->n++] = kind;
    return true;
}

static bool push_digest(reader *r, uint64_t d) {
    if (r->nd == r->dcap) {
        size_t cap = r->dcap ? 2 * r->dcap : 1024;
        uint64_t *q = realloc(r->dig, cap * sizeof *q);
        if (!q) return false;
        r->dig = q;
        r->dcap = cap;
    }
    r->dig[r->nd++] = d;
    return true;
}

/*  Probe the node on top of the stack, which is popped, as a datum of a
 *  type whose constructor i has fields[i] fields; they are pushed, the last
 *  first, so the first is on top.  Returns the constructor, or -1. */
static int probe(reader *r, unsigned nctors, const unsigned *fields, const av_opts *o,
                 const char **err) {
    av_arena *a = r->a;
    uint32_t t = r->node[--r->n];
    for (unsigned i = 0; i < nctors; i++) {
        t = av_app(a, t, r->marknode[i]);
        if (t == AV_NONE) { *err = "out of memory"; return -1; }
    }
    av_opts po = *o;
    po.whnf_only = true;
    /* the probes share the run's fuel: --fuel bounds the read, not each
     * probe of it */
    if (o->max_steps != UINT64_MAX)
        po.max_steps = r->steps < o->max_steps ? o->max_steps - r->steps : 0;
    av_result res = av_reduce(a, t, &po);
    r->steps += res.steps;
    r->tmpl_calls += res.tmpl_calls;
    r->dispatches += res.dispatches;
    r->fused += res.fused;
    r->word_ops += res.word_ops;
    r->fix_calls += res.fix_calls;
    r->joins += res.joins;
    if (res.status != AV_WHNF && res.status != AV_NORMAL) {
        *err = av_status_name(res.status);
        return -1;
    }
    uint32_t spine[8];
    unsigned k = 0;
    uint32_t h = av_view(a, res.term);
    while (av_tag(a, h) == AV_APP) {
        if (k == 8) { *err = "a constructor carried too many fields"; return -1; }
        spine[k++] = av_right(a, h);
        h = av_view(a, av_left(a, h));
    }
    ski_leaf id = av_tag(a, h) == AV_LEAF ? av_right(a, h) : AV_NONE;
    unsigned w = 0;
    while (w < nctors && r->mark[w] != id) w++;
    if (w == nctors) { *err = "the head is not a marker: not a value of this type"; return -1; }
    if (k != fields[w]) { *err = "a constructor with the wrong number of fields"; return -1; }
    for (unsigned i = 0; i < k; i++)            /* spine[0] is the last field */
        if (!push(r, spine[i], READ)) { *err = "out of memory"; return -1; }
    return (int)w;
}

static const unsigned F_RESULT[2] = { 1, 0 };           /* ROk outs | RErr        */
static const unsigned F_OUTS[2]   = { 0, 3 };           /* ONil | OCons name tm . */
static const unsigned F_NAME[2]   = { 0, 2 };           /* NNil | NCons code name */
static const unsigned F_CODE[1]   = { 7 };              /* Code b6 .. b0          */
static const unsigned F_BIT[2]    = { 0, 0 };           /* Lo | Hi                */
static const unsigned F_TM[5]     = { 0, 0, 0, 1, 1 };  /* TS TK TI TV nat, TA ap */
static const unsigned F_AP[1]     = { 2 };              /* Ap tm tm               */

/*  The name on top of the stack, into buf (NUL-terminated): at most
 *  NAME_MAX_LEN characters, none of them a control character or a space, as
 *  the output is a line per name and a tab before its hash. */
#define NAME_MAX_LEN 65536
static bool read_name(reader *r, const av_opts *o, char **buf, size_t *cap,
                      const char **err) {
    size_t len = 0;
    for (;;) {
        int c = probe(r, 2, F_NAME, o, err);
        if (c < 0) return false;
        if (len + 1 >= *cap) {
            size_t ncap = *cap ? 2 * *cap : 64;
            char *q = realloc(*buf, ncap);
            if (!q) { *err = "out of memory"; return false; }
            *buf = q;
            *cap = ncap;
        }
        if (c == 0) { (*buf)[len] = '\0'; return true; }
        if (len == NAME_MAX_LEN) { *err = "a name longer than 65536 characters"; return false; }
        if (probe(r, 1, F_CODE, o, err) < 0) return false;  /* its bits; the rest below */
        unsigned ch = 0;
        for (int i = 0; i < 7; i++) {
            int b = probe(r, 2, F_BIT, o, err);
            if (b < 0) return false;
            ch = ch << 1 | (unsigned)b;
        }
        if (ch <= ' ' || ch == 0x7f) { *err = "a name holding a control character or a space"; return false; }
        (*buf)[len++] = (char)ch;
    }
}

/*  The term on top of the stack to its digest, each node read once:
 *  a node is replaced by a JOIN of itself, then read; an atom's digest is
 *  its name's, an application's joins its two fields' digests. */
static bool read_term(reader *r, const av_opts *o, uint64_t *digest, const char **err) {
    av_arena *a = r->a;
    const uint64_t atom[3] = { digest_leaf("S"), digest_leaf("K"), digest_leaf("I") };
    size_t base = r->n - 1, dbase = r->nd;
    while (r->n > base) {
        size_t top = r->n - 1;
        uint32_t node = av_res(a, r->node[top]);
        uint64_t d;
        if (r->kind[top] == JOIN) {
            r->n--;
            uint64_t x = r->dig[--r->nd], f = r->dig[--r->nd];
            d = digest_app(f, x);
        } else if (nmap_get(&r->memo, node, &d)) {
            r->n--;
            if (!push_digest(r, d)) { *err = "out of memory"; return false; }
            continue;
        } else {
            r->node[top] = node;
            r->kind[top] = JOIN;
            if (!push(r, node, READ)) { *err = "out of memory"; return false; }
            int c = probe(r, 5, F_TM, o, err);
            if (c < 0) return false;
            if (c == 3) { *err = "a variable in a closed term"; return false; }
            if (c == 4) {                       /* TA ap: read Ap e f's two */
                if (probe(r, 1, F_AP, o, err) < 0) return false;
                continue;
            }
            node = av_res(a, r->node[--r->n]);  /* an atom: its JOIN is done */
            d = atom[c];
        }
        if (!nmap_put(&r->memo, node, d) || !push_digest(r, d)) {
            *err = "out of memory";
            return false;
        }
    }
    if (r->nd != dbase + 1) { *err = "the reader lost its place"; return false; }
    *digest = r->dig[--r->nd];
    return true;
}

uint32_t av_front0_input(av_arena *a, const av_front0 *f, const char *src, size_t len) {
    uint32_t codes[128] = { 0 };
    for (int i = 0; i < 128; i++) codes[i] = AV_NONE;
    uint32_t list = f->snil;
    for (size_t i = len; i-- > 0;) {
        unsigned ch = (unsigned char)src[i];
        if (ch > 127) return AV_NONE;
        if (codes[ch] == AV_NONE) {
            uint32_t c = f->code;
            for (int b = 6; b >= 0 && c != AV_NONE; b--)
                c = av_app(a, c, (ch >> b & 1) ? f->hi : f->lo);
            codes[ch] = c;
        }
        list = codes[ch] == AV_NONE ? AV_NONE : av_app(a, av_app(a, f->scons, codes[ch]), list);
        if (list == AV_NONE) return AV_NONE;
    }
    return av_app(a, f->front, list);
}

int av_front0_read(av_arena *a, uint32_t t, const av_opts *o, FILE *out,
                   uint64_t *steps, av_result *tally, const char **err) {
    reader r = { .a = a };
    av_active me = { roots, after, &r, a->active };
    int rc = -1;
    char *name = NULL;
    size_t ncap = 0;
    for (unsigned i = 0; i < 5; i++) {
        char nm[8];
        int n = snprintf(nm, sizeof nm, "@%u", i);
        r.marknode[i] = av_leaf(a, nm, (size_t)n);
        if (r.marknode[i] == AV_NONE) { *err = "out of memory"; return -1; }
        r.mark[i] = av_right(a, r.marknode[i]);
    }
    a->active = &me;
    if (!push(&r, t, READ)) { *err = "out of memory"; goto done; }
    int c = probe(&r, 2, F_RESULT, o, err);
    if (c < 0) goto done;
    if (c == 1) { fputs("RErr\n", out); rc = 1; goto done; }
    for (;;) {
        c = probe(&r, 2, F_OUTS, o, err);
        if (c < 0) goto done;
        if (c == 0) break;
        if (!read_name(&r, o, &name, &ncap, err)) goto done;   /* the tm, rest below */
        uint64_t d;
        if (!read_term(&r, o, &d, err)) goto done;          /* the rest below */
        fprintf(out, "%s\t" AV_HASH_VERSION ":%016llx\n", name, (unsigned long long)d);
    }
    rc = r.lost ? -1 : 0;
    if (r.lost) *err = "out of memory remapping the reader's memo";
done:
    a->active = me.next;
    *steps = r.steps;
    if (tally) {
        tally->steps = r.steps;
        tally->tmpl_calls = r.tmpl_calls;
        tally->dispatches = r.dispatches;
        tally->fused = r.fused;
        tally->word_ops = r.word_ops;
        tally->fix_calls = r.fix_calls;
        tally->joins = r.joins;
    }
    free(r.node);
    free(r.kind);
    free(r.dig);
    nmap_free(&r.memo);
    free(name);
    return rc;
}
