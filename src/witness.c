/**  witness.c
 *
 *  The witness strategy (docs/DESIGN.md §17): lean-ski's write-once heap
 *  machine, Air.stepG, executed literally, and its trace written as the
 *  table Ski/AirCheck.lean reads and bench/plonky3 proves.
 *
 *  Nothing here shares the arena's representation.  A witness heap holds
 *  the circuit's cells -- S, K, I, A f x, N, C x r -- each written once at
 *  the counter, which is the heap's length; nothing is overwritten,
 *  collected or hash-consed (§19).  So a contraction here is a contraction
 *  of the term, and the count equals copy mode's (Mach.machine_count).
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "avon.h"

void av_witness_free(av_witness *w) {
    free(w->mem);
    free(w->rows);
    memset(w, 0, sizeof *w);
}

static bool put_cell(av_witness *w, uint32_t tag, uint32_t x, uint32_t y) {
    if (w->nmem == w->memcap) {
        size_t cap = w->memcap ? w->memcap * 2 : 1024;
        av_cell *m = realloc(w->mem, cap * sizeof *m);
        if (!m) return false;
        w->mem = m;
        w->memcap = cap;
    }
    w->mem[w->nmem++] = (av_cell){ tag, x, y };
    return true;
}

static bool put_row(av_witness *w, uint32_t hd, uint32_t stk, uint32_t ctr) {
    if (w->nrows == w->rowcap) {
        size_t cap = w->rowcap ? w->rowcap * 2 : 1024;
        av_row *r = realloc(w->rows, cap * sizeof *r);
        if (!r) return false;
        w->rows = r;
        w->rowcap = cap;
    }
    w->rows[w->nrows++] = (av_row){ hd, stk, ctr };
    return true;
}

/*  Mach.build: children first, the function before the argument, a fresh
 *  cell for every leaf.  The arena term is unfolded as a tree. */
static const char *build(const av_arena *a, uint32_t t, av_witness *w,
                         size_t max_cells, uint32_t *root) {
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 256, top = 0, nout = 0, ocap = 256;
    item *todo = malloc(cap * sizeof *todo);
    uint32_t *out = malloc(ocap * sizeof *out);
    const char *msg = NULL;
    if (!todo || !out) { msg = "out of memory"; goto done; }
    todo[top++] = (item){ t, false };
    while (top) {
        item it = todo[--top];
        uint32_t n = av_res(a, it.node);
        if (w->nmem >= max_cells) { msg = "the loaded heap exceeds the cell budget"; goto done; }
        if (nout + 1 > ocap) {
            uint32_t *o = realloc(out, (ocap *= 2) * sizeof *o);
            if (!o) { msg = "out of memory"; goto done; }
            out = o;
        }
        if (it.done) {
            uint32_t x = out[--nout], f = out[--nout];
            if (!put_cell(w, AV_CELL_APP, f, x)) { msg = "out of memory"; goto done; }
            out[nout++] = (uint32_t)(w->nmem - 1);
            continue;
        }
        if (av_tag(a, n) == AV_APP) {
            if (top + 3 > cap) {
                item *q = realloc(todo, (cap *= 2) * sizeof *q);
                if (!q) { msg = "out of memory"; goto done; }
                todo = q;
            }
            todo[top++] = (item){ n, true };
            todo[top++] = (item){ av_right(a, n), false };
            todo[top++] = (item){ av_left(a, n), false };
            continue;
        }
        if (av_tag(a, n) != AV_LEAF) { msg = "a jet node in a witnessed term"; goto done; }
        ski_leaf id = av_right(a, n);
        if (!ski_is_comb(id)) {
            msg = "a witness of a term with atoms is not supported yet (§17.3)";
            goto done;
        }
        uint32_t tag = id == SKI_S ? AV_CELL_S : id == SKI_K ? AV_CELL_K : AV_CELL_I;
        if (!put_cell(w, tag, 0, 0)) { msg = "out of memory"; goto done; }
        out[nout++] = (uint32_t)(w->nmem - 1);
    }
    *root = out[0];
done:
    free(todo);
    free(out);
    return msg;
}

/*  A cell at an address, or none: reads beyond the counter are not cells. */
static const av_cell *get(const av_witness *w, uint32_t addr) {
    return addr < w->nmem ? &w->mem[addr] : NULL;
}

static const av_cell *cons_at(const av_witness *w, uint32_t addr) {
    const av_cell *c = get(w, addr);
    return c && c->tag == AV_CELL_CONS ? c : NULL;
}

av_status av_witness_run(const av_arena *a, uint32_t t, size_t max_rows,
                         size_t max_cells, av_witness *w, const char **err) {
    memset(w, 0, sizeof *w);
    if (max_cells > AV_MAX_NODES) max_cells = AV_MAX_NODES;  /* 32-bit cells */
    uint32_t hd;
    const char *msg = build(a, t, w, max_cells, &hd);
    if (msg) { if (err) *err = msg; return AV_SIZE; }
    uint32_t stk = (uint32_t)w->nmem;
    if (!put_cell(w, AV_CELL_NIL, 0, 0)) { if (err) *err = "out of memory"; return AV_SIZE; }
    w->loaded = w->nmem;
    w->hd0 = hd;
    w->stk0 = stk;

    for (;;) {
        if (w->nrows >= max_rows) {
            if (err) *err = "the run exceeds the row budget";
            return AV_SIZE;
        }
        if (w->nmem > UINT32_MAX - 3) { if (err) *err = "address space"; return AV_SIZE; }
        uint32_t c = (uint32_t)w->nmem;
        if (!put_row(w, hd, stk, c)) { if (err) *err = "out of memory"; return AV_SIZE; }

        /* Air.stepG over the heap, counter c */
        const av_cell *h = get(w, hd);
        const av_cell *s1, *s2, *s3;
        uint32_t nhd, nstk;
        size_t writes = 0;
        av_cell ws[3];
        if (!h) break;
        switch (h->tag) {
        case AV_CELL_APP:
            nhd = h->a;
            nstk = c;
            ws[writes++] = (av_cell){ AV_CELL_CONS, h->b, stk };
            break;
        case AV_CELL_I:
            if (!(s1 = cons_at(w, stk))) goto halted;
            nhd = s1->a;
            nstk = s1->b;
            break;
        case AV_CELL_K:
            if (!(s1 = cons_at(w, stk)) || !(s2 = cons_at(w, s1->b))) goto halted;
            nhd = s1->a;
            nstk = s2->b;
            break;
        case AV_CELL_S: {
            if (!(s1 = cons_at(w, stk)) || !(s2 = cons_at(w, s1->b)) ||
                !(s3 = cons_at(w, s2->b)))
                goto halted;
            uint32_t x = s1->a, y = s2->a, z = s3->a, rest = s3->b;
            nhd = x;
            nstk = c + 2;
            ws[writes++] = (av_cell){ AV_CELL_APP, y, z };
            ws[writes++] = (av_cell){ AV_CELL_CONS, c, rest };
            ws[writes++] = (av_cell){ AV_CELL_CONS, z, c + 1 };
            break;
        }
        default:
            goto halted;
        }
        if (w->nmem + writes > max_cells) {
            if (err) *err = "the run exceeds the cell budget";
            return AV_SIZE;
        }
        if (h->tag != AV_CELL_APP) w->contractions++;
        for (size_t i = 0; i < writes; i++)
            if (!put_cell(w, ws[i].tag, ws[i].a, ws[i].b)) {
                if (err) *err = "out of memory";
                return AV_SIZE;
            }
        hd = nhd;
        stk = nstk;
    }
halted:
    return AV_WHNF;
}

/*  --------------------------------------------------------------- tables */

static size_t pow2_at_least(size_t n, unsigned min_log) {
    size_t p = (size_t)1 << min_log;
    while (p < n) p *= 2;
    return p;
}

static bool out_str(av_buf *b, const char *s, size_t n) {
    if (b->len + n + 1 > b->cap) {
        size_t cap = b->cap ? b->cap : 4096;
        while (b->len + n + 1 > cap) cap *= 2;
        char *p = realloc(b->s, cap);
        if (!p) return false;
        b->s = p;
        b->cap = cap;
    }
    memcpy(b->s + b->len, s, n);
    b->len += n;
    b->s[b->len] = '\0';
    return true;
}

bool av_prefix(const av_arena *a, uint32_t t, size_t budget, av_buf *out) {
    size_t cap = 256, top = 0, visited = 0;
    uint32_t *stk = malloc(cap * sizeof *stk);
    bool ok = stk != NULL;
    if (ok) stk[top++] = t;
    while (ok && top) {
        uint32_t n = av_res(a, stk[--top]);
        if (++visited > budget) { ok = false; break; }
        if (av_tag(a, n) == AV_APP) {
            if (top + 2 > cap) {
                uint32_t *q = realloc(stk, (cap *= 2) * sizeof *q);
                if (!q) { ok = false; break; }
                stk = q;
            }
            ok = out_str(out, "`", 1);
            stk[top++] = av_right(a, n);
            stk[top++] = av_left(a, n);
            continue;
        }
        ski_leaf id = av_right(a, n);
        if (av_tag(a, n) != AV_LEAF || !ski_is_comb(id)) { ok = false; break; }
        ok = out_str(out, id == SKI_S ? "S" : id == SKI_K ? "K" : "I", 1);
    }
    free(stk);
    return ok;
}

bool av_witness_table(const av_arena *a, uint32_t t, const av_witness *w,
                      unsigned min_log, av_buf *out) {
    char line[64];
    if (w->nrows == 0 || w->loaded == 0) return false;   /* no run to show */
    if (!av_prefix(a, t, w->loaded, out) || !out_str(out, "\n", 1)) return false;

    size_t msize = pow2_at_least(w->nmem, min_log);
    int n = snprintf(line, sizeof line, "%zu\n", msize);
    if (!out_str(out, line, (size_t)n)) return false;
    for (size_t i = 0; i < msize; i++) {
        const av_cell *c = i < w->nmem ? &w->mem[i] : NULL;
        uint32_t tag = c ? c->tag : AV_CELL_NIL;
        switch (tag) {
        case AV_CELL_S:    n = snprintf(line, sizeof line, "S\n"); break;
        case AV_CELL_K:    n = snprintf(line, sizeof line, "K\n"); break;
        case AV_CELL_I:    n = snprintf(line, sizeof line, "I\n"); break;
        case AV_CELL_APP:  n = snprintf(line, sizeof line, "A %u %u\n", c->a, c->b); break;
        case AV_CELL_NIL:  n = snprintf(line, sizeof line, "N\n"); break;
        case AV_CELL_CONS: n = snprintf(line, sizeof line, "C %u %u\n", c->a, c->b); break;
        default:           return false;
        }
        if (!out_str(out, line, (size_t)n)) return false;
    }

    size_t k = pow2_at_least(w->nrows, min_log);
    n = snprintf(line, sizeof line, "%zu\n", k);
    if (!out_str(out, line, (size_t)n)) return false;
    for (size_t i = 0; i < k; i++) {
        const av_row *r = &w->rows[i < w->nrows ? i : w->nrows - 1];
        n = snprintf(line, sizeof line, "%u %u %u\n", r->hd, r->stk, r->ctr);
        if (!out_str(out, line, (size_t)n)) return false;
    }
    return true;
}

uint32_t av_parse_prefix(av_arena *a, const char *src, size_t len,
                         const char **err) {
    size_t i = 0, j = len;
    while (i < j && (src[i] == ' ' || src[i] == '\n' || src[i] == '\r' || src[i] == '\t')) i++;
    while (j > i && (src[j - 1] == ' ' || src[j - 1] == '\n' || src[j - 1] == '\r' || src[j - 1] == '\t')) j--;
    /* a stack of applications waiting on a child, as cue keeps */
    size_t cap = 64, top = 0;
    uint32_t *stk = malloc(cap * sizeof *stk);
    const char *msg = NULL;
    uint32_t root = AV_NONE;
    if (!stk) { msg = "out of memory"; goto done; }
    for (; i < j; i++) {
        char c = src[i];
        if (c == '`') {
            if (top == cap) {
                uint32_t *q = realloc(stk, (cap *= 2) * sizeof *q);
                if (!q) { msg = "out of memory"; goto done; }
                stk = q;
            }
            stk[top++] = AV_NONE;
            continue;
        }
        uint32_t t = c == 'S' ? AV_NODE_S : c == 'K' ? AV_NODE_K : c == 'I' ? AV_NODE_I : AV_NONE;
        if (t == AV_NONE) { msg = "not a prefix term"; goto done; }
        for (;;) {
            if (top == 0) { root = t; break; }
            if (stk[top - 1] == AV_NONE) { stk[top - 1] = t; break; }
            t = av_app(a, stk[--top], t);
            if (t == AV_NONE) { msg = "out of memory"; goto done; }
        }
        if (root != AV_NONE) { i++; break; }
    }
    if (!msg && (root == AV_NONE || i != j)) msg = root == AV_NONE ? "truncated prefix term" : "text after the term";
done:
    free(stk);
    if (msg && err) *err = msg;
    return msg ? AV_NONE : root;
}
