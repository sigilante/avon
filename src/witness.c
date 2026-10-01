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
        uint32_t n = av_view(a, it.node);
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

/*  --------------------------------------------------------- the jet table */

void av_jettable_free(av_jettable *jt) {
    for (size_t i = 0; i < jt->njets; i++) free(jt->jets[i].cells);
    free(jt->jets);
    free(jt->root_addr);
    free(jt->root_jet);
    memset(jt, 0, sizeof *jt);
}

/*  A cursor over the file: whitespace-separated words. */
typedef struct { const char *s; size_t len, pos; } cursor;

static bool word(cursor *c, const char **w, size_t *n) {
    while (c->pos < c->len && (c->s[c->pos] == ' ' || c->s[c->pos] == '\n' ||
                               c->s[c->pos] == '\r' || c->s[c->pos] == '\t'))
        c->pos++;
    size_t start = c->pos;
    while (c->pos < c->len && c->s[c->pos] != ' ' && c->s[c->pos] != '\n' &&
           c->s[c->pos] != '\r' && c->s[c->pos] != '\t')
        c->pos++;
    *w = c->s + start;
    *n = c->pos - start;
    return *n > 0;
}

static bool nat32(cursor *c, uint32_t *out) {
    const char *w;
    size_t n;
    if (!word(c, &w, &n) || n > 10) return false;
    uint64_t v = 0;
    for (size_t i = 0; i < n; i++) {
        if (w[i] < '0' || w[i] > '9') return false;
        v = v * 10 + (uint64_t)(w[i] - '0');
    }
    if (v > UINT32_MAX) return false;
    *out = (uint32_t)v;
    return true;
}

static bool keyword(cursor *c, const char *k) {
    const char *w;
    size_t n;
    return word(c, &w, &n) && n == strlen(k) && memcmp(w, k, n) == 0;
}

static bool operand(cursor *c, av_jop *op) {
    const char *w;
    size_t n;
    if (!word(c, &w, &n) || n != 1) return false;
    op->kind = w[0] == 'L' ? AV_JOP_LOCAL : w[0] == 'A' ? AV_JOP_ARG :
               w[0] == 'G' ? AV_JOP_GLOBAL : 99u;
    return op->kind != 99u && nat32(c, &op->val);
}

bool av_jettable_read(const char *src, size_t len, av_jettable *jt, const char **err) {
    memset(jt, 0, sizeof *jt);
    cursor c = { src, len, 0 };
    uint32_t r, g;
    const char *msg = "malformed jet file";
    if (!keyword(&c, "roots") || !nat32(&c, &r)) goto fail;
    jt->root_addr = calloc(r ? r : 1, sizeof *jt->root_addr);
    jt->root_jet = calloc(r ? r : 1, sizeof *jt->root_jet);
    if (!jt->root_addr || !jt->root_jet) { msg = "out of memory"; goto fail; }
    for (uint32_t i = 0; i < r; i++) {
        if (!nat32(&c, &jt->root_addr[i]) || !nat32(&c, &jt->root_jet[i])) goto fail;
        jt->nroots++;
    }
    if (!keyword(&c, "jets") || !nat32(&c, &g)) goto fail;
    jt->jets = calloc(g ? g : 1, sizeof *jt->jets);
    if (!jt->jets) { msg = "out of memory"; goto fail; }
    for (uint32_t j = 0; j < g; j++) {
        av_tjet *J = &jt->jets[j];
        uint32_t n;
        if (!nat32(&c, &J->k) || !nat32(&c, &n) || !operand(&c, &J->root)) goto fail;
        jt->njets++;
        J->cells = calloc(n ? n : 1, sizeof *J->cells);
        if (!J->cells) { msg = "out of memory"; goto fail; }
        for (uint32_t i = 0; i < n; i++) {
            av_jcell *x = &J->cells[i];
            if (!nat32(&c, &x->tag) || x->tag > 3) goto fail;
            if (x->tag == 3 && (!operand(&c, &x->a) || !operand(&c, &x->b))) goto fail;
            J->ncells++;
        }
    }
    const char *w;
    size_t n;
    if (word(&c, &w, &n)) { msg = "text after the jet file"; goto fail; }
    /* every root names a jet; every local operand an earlier cell; every
       argument operand an argument */
    for (size_t i = 0; i < jt->nroots; i++)
        if (jt->root_jet[i] >= jt->njets) { msg = "a root names no jet"; goto fail; }
    for (size_t j = 0; j < jt->njets; j++) {
        const av_tjet *J = &jt->jets[j];
        for (size_t i = 0; i < J->ncells; i++) {
            const av_jcell *x = &J->cells[i];
            if (x->tag != 3) continue;
            const av_jop ops[2] = { x->a, x->b };
            for (int q = 0; q < 2; q++) {
                if (ops[q].kind == AV_JOP_LOCAL && ops[q].val >= i) { msg = "a local operand names a later cell"; goto fail; }
                if (ops[q].kind == AV_JOP_ARG && ops[q].val >= J->k) { msg = "an argument operand past the arity"; goto fail; }
            }
        }
        if (J->root.kind == AV_JOP_LOCAL && J->root.val >= J->ncells) { msg = "a root operand past the cells"; goto fail; }
        if (J->root.kind == AV_JOP_ARG && J->root.val >= J->k) { msg = "a root operand past the arity"; goto fail; }
    }
    return true;
fail:
    if (err) *err = msg;
    av_jettable_free(jt);
    return false;
}

av_status av_witness_run(const av_arena *a, uint32_t t, size_t max_rows,
                         size_t max_cells, av_witness *w, const char **err) {
    return av_witness_run_jets(a, t, NULL, max_rows, max_cells, w, NULL, err);
}

static uint32_t resolve(av_jop op, uint32_t c, const uint32_t *ps) {
    return op.kind == AV_JOP_LOCAL ? c + op.val : op.kind == AV_JOP_ARG ? ps[op.val] : op.val;
}

/*  The jetted machine from (*hd, *stk) to a halt, one row per state: at a
 *  licensed root with enough arguments an instantiation, else Air.stepG.
 *  The halted state's row is the last.  False, with *msg, on a budget. */
static bool run_to_halt(av_witness *w, const av_jettable *jt, const uint32_t *root_of,
                        uint32_t *ps, uint32_t *hdp, uint32_t *stkp, size_t max_rows,
                        size_t max_cells, uint64_t *insts, const char **msg) {
    uint32_t hd = *hdp, stk = *stkp;
    for (;;) {
        if (w->nrows >= max_rows) { *msg = "the run exceeds the row budget"; return false; }
        if (w->nmem > UINT32_MAX - 3) { *msg = "address space"; return false; }
        uint32_t c = (uint32_t)w->nmem;
        if (!put_row(w, hd, stk, c)) { *msg = "out of memory"; return false; }

        /* An instantiation, at a licensed root with enough arguments. */
        if (root_of && hd < w->loaded && root_of[hd]) {
            const av_tjet *J = &jt->jets[root_of[hd] - 1];
            uint32_t s = stk;
            uint32_t i = 0;
            for (; i < J->k; i++) {
                const av_cell *cc = cons_at(w, s);
                if (!cc) break;
                ps[i] = cc->a;
                s = cc->b;
            }
            if (i == J->k) {
                if (w->nmem + J->ncells > max_cells) { *msg = "the run exceeds the cell budget"; return false; }
                for (size_t q = 0; q < J->ncells; q++) {
                    const av_jcell *x = &J->cells[q];
                    bool ok = x->tag == 3
                        ? put_cell(w, AV_CELL_APP, resolve(x->a, c, ps), resolve(x->b, c, ps))
                        : put_cell(w, x->tag, 0, 0);   /* S, K, I share the mem bus's tags */
                    if (!ok) { *msg = "out of memory"; return false; }
                }
                hd = resolve(J->root, c, ps);
                stk = s;
                if (insts) (*insts)++;
                w->pops += J->k;
                w->wcells += J->ncells;
                continue;
            }
        }

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
        default:                                /* an atom, a nil, a cons */
            goto halted;
        }
        if (w->nmem + writes > max_cells) { *msg = "the run exceeds the cell budget"; return false; }
        if (h->tag != AV_CELL_APP) w->contractions++;
        for (size_t i = 0; i < writes; i++)
            if (!put_cell(w, ws[i].tag, ws[i].a, ws[i].b)) { *msg = "out of memory"; return false; }
        hd = nhd;
        stk = nstk;
    }
halted:
    *hdp = hd;
    *stkp = stk;
    return true;
}

/*  Mach.load, and the jet table's roots over the loaded heap. */
static const char *load_jetted(const av_arena *a, uint32_t t, const av_jettable *jt,
                               size_t max_cells, av_witness *w, uint32_t **root_of,
                               uint32_t **ps) {
    uint32_t hd;
    const char *msg = build(a, t, w, max_cells, &hd);
    if (msg) return msg;
    uint32_t stk = (uint32_t)w->nmem;
    if (!put_cell(w, AV_CELL_NIL, 0, 0)) return "out of memory";
    w->loaded = w->nmem;
    w->hd0 = hd;
    w->stk0 = stk;
    if (!jt) return NULL;
    uint32_t maxk = 1;
    for (size_t j = 0; j < jt->njets; j++)
        if (jt->jets[j].k > maxk) maxk = jt->jets[j].k;
    *root_of = calloc(w->loaded, sizeof **root_of);
    *ps = calloc(maxk, sizeof **ps);
    if (!*root_of || !*ps) return "out of memory";
    for (size_t i = 0; i < jt->nroots; i++) {
        if (jt->root_addr[i] >= w->loaded) return "a root outside the loaded heap";
        (*root_of)[jt->root_addr[i]] = jt->root_jet[i] + 1;
    }
    return NULL;
}

av_status av_witness_run_jets(const av_arena *a, uint32_t t, const av_jettable *jt,
                              size_t max_rows, size_t max_cells, av_witness *w,
                              uint64_t *insts, const char **err) {
    memset(w, 0, sizeof *w);
    if (insts) *insts = 0;
    if (max_cells > AV_MAX_NODES) max_cells = AV_MAX_NODES;  /* 32-bit cells */
    uint32_t *root_of = NULL;   /* jet + 1 at each root of the loaded heap */
    uint32_t *ps = NULL;        /* the argument pointers an instantiation pops */
    av_status st = AV_SIZE;
    const char *msg = load_jetted(a, t, jt, max_cells, w, &root_of, &ps);
    uint32_t hd = w->hd0, stk = w->stk0;
    if (!msg && run_to_halt(w, jt, root_of, ps, &hd, &stk, max_rows, max_cells, insts, &msg))
        st = AV_WHNF;
    free(root_of);
    free(ps);
    if (msg && err) *err = msg;
    return st;
}

/*  --------------------------------------------------------- probe segments */

static size_t pow2_at_least(size_t n, unsigned min_log);
static bool out_str(av_buf *b, const char *s, size_t n);

void av_plan_free(av_plan *p) {
    free(p->segs);
    memset(p, 0, sizeof *p);
}

bool av_plan_read(const char *src, size_t len, av_plan *p, const char **err) {
    cursor c = { src, len, 0 };
    uint32_t n;
    memset(p, 0, sizeof *p);
    if (!keyword(&c, "plan") || !nat32(&c, &n) || n == 0) { *err = "expected `plan N`, N > 0"; return false; }
    if (n > (1u << 16)) { *err = "a plan past 65,536 segments"; return false; }
    p->segs = calloc(n, sizeof *p->segs);
    if (!p->segs) { *err = "out of memory"; return false; }
    for (uint32_t j = 0; j < n; j++) {
        av_seg *g = &p->segs[j];
        if (!nat32(&c, &g->base) || !nat32(&c, &g->k) || !nat32(&c, &g->ctor) ||
            !nat32(&c, &g->arity) || !nat32(&c, &g->parent) || !nat32(&c, &g->field)) {
            av_plan_free(p);
            *err = "a malformed segment line";
            return false;
        }
    }
    const char *rest;
    size_t rn;
    if (word(&c, &rest, &rn)) { av_plan_free(p); *err = "text after the plan"; return false; }
    /* The shape Air.planOf gives: consecutive marker ranges, a constructor
     * among its type's, and each field of each segment probed by exactly
     * one later segment, depth first, the last a leaf. */
    uint64_t base = 0, fields = 0;
    uint8_t *probed = NULL;
    for (uint32_t j = 0; j < n; j++) {
        const av_seg *g = &p->segs[j];
        const char *why = NULL;
        if (g->base != base) why = "a segment's markers do not follow the last's";
        else if (g->ctor >= g->k) why = "a constructor past its type's count";
        else if (base + g->k > UINT32_MAX) why = "markers past 2^32";
        else if (j == 0 ? g->parent != 0 || g->field != 0 : g->parent >= j)
            why = "a segment's parent is not before it";
        else if (j > 0 && g->field >= p->segs[g->parent].arity)
            why = "a segment reads a field its parent does not have";
        if (why) { av_plan_free(p); *err = why; return false; }
        base += g->k;
        fields += g->arity;
    }
    if (fields != (uint64_t)n - 1 || p->segs[n - 1].arity != 0) {
        av_plan_free(p);
        *err = "the fields are not each probed once";
        return false;
    }
    /* each (parent, field) once: offsets of each segment's fields */
    size_t *off = calloc(n + 1, sizeof *off);
    probed = calloc(fields ? fields : 1, 1);
    if (!off || !probed) { free(off); free(probed); av_plan_free(p); *err = "out of memory"; return false; }
    for (uint32_t j = 0; j < n; j++) off[j + 1] = off[j] + p->segs[j].arity;
    for (uint32_t j = 1; j < n; j++) {
        size_t at = off[p->segs[j].parent] + p->segs[j].field;
        if (probed[at]++) {
            free(off);
            free(probed);
            av_plan_free(p);
            *err = "a field probed twice";
            return false;
        }
    }
    free(off);
    free(probed);
    p->n = n;
    return true;
}

void av_probe_free(av_probe *pr) {
    free(pr->starts);
    free(pr->fields);
    free(pr->field_off);
    memset(pr, 0, sizeof *pr);
}

av_status av_witness_run_probe(const av_arena *a, uint32_t t, const av_jettable *jt,
                               const av_plan *plan, size_t max_rows, size_t max_cells,
                               av_witness *w, av_probe *pr, uint64_t *insts,
                               const char **err) {
    memset(w, 0, sizeof *w);
    memset(pr, 0, sizeof *pr);
    if (insts) *insts = 0;
    if (max_cells > AV_MAX_NODES) max_cells = AV_MAX_NODES;
    uint32_t *root_of = NULL, *ps = NULL;
    for (size_t j = 0; j < plan->n; j++)    /* fields past the cells: no run */
        if (plan->segs[j].arity > max_cells) {
            if (err) *err = "a segment with more fields than the cell budget";
            return AV_SIZE;
        }
    av_status st = AV_SIZE;
    char *why = pr->why;                    /* the caller's: valid until av_probe_free */
    const size_t whyn = sizeof pr->why;
    const char *msg = NULL;
    size_t nfields = 0;
    for (size_t j = 0; j < plan->n; j++) nfields += plan->segs[j].arity;
    pr->starts = calloc(plan->n ? plan->n : 1, sizeof *pr->starts);
    pr->fields = calloc(nfields ? nfields : 1, sizeof *pr->fields);
    pr->field_off = calloc(plan->n + 1, sizeof *pr->field_off);
    if (!pr->starts || !pr->fields || !pr->field_off) { msg = "out of memory"; goto out; }
    pr->n = plan->n;
    msg = load_jetted(a, t, jt, max_cells, w, &root_of, &ps);
    if (msg) goto out;
    uint32_t hd = w->hd0, stk = w->stk0;
    for (size_t j = 0; j < plan->n; j++) {
        const av_seg *g = &plan->segs[j];
        uint32_t f = hd;                        /* segment 0 probes the head */
        if (j > 0) {
            /* av_plan_read refuses these; a plan built by hand may not */
            if (g->parent >= j || g->field >= plan->segs[g->parent].arity) {
                snprintf(why, whyn, "a malformed plan: segment %zu reads no earlier field", j);
                msg = why;
                goto out;
            }
            f = pr->fields[pr->field_off[g->parent] + g->field];
        }
        /* the probe row, then the markers: atoms, a stack of them, a nil */
        if (w->nrows >= max_rows) { msg = "the run exceeds the row budget"; goto out; }
        uint64_t c = w->nmem;
        if (c + 2ull * g->k + 1 > max_cells || c + 2ull * g->k + 1 > UINT32_MAX - 3) {
            msg = "the run exceeds the cell budget";
            goto out;
        }
        pr->starts[j] = (uint32_t)w->nrows;
        if (!put_row(w, hd, stk, (uint32_t)c)) { msg = "out of memory"; goto out; }
        for (uint32_t i = 0; i < g->k; i++)
            if (!put_cell(w, AV_CELL_ATOM, g->base + i, 0)) { msg = "out of memory"; goto out; }
        for (uint32_t i = 0; i < g->k; i++)
            if (!put_cell(w, AV_CELL_CONS, (uint32_t)c + i, (uint32_t)c + g->k + i + 1)) {
                msg = "out of memory";
                goto out;
            }
        if (!put_cell(w, AV_CELL_NIL, 0, 0)) { msg = "out of memory"; goto out; }
        hd = f;
        stk = (uint32_t)c + g->k;
        if (!run_to_halt(w, jt, root_of, ps, &hd, &stk, max_rows, max_cells, insts, &msg))
            goto out;
        w->nrows--;                             /* the halted row is not pushed */
        /* the end: the segment's marker at the head, exactly its fields */
        const av_cell *h = get(w, hd);
        if (!h || h->tag != AV_CELL_ATOM || h->a != g->ctor + g->base) {
            if (h && h->tag == AV_CELL_ATOM)
                snprintf(why, whyn, "segment %zu ends at marker %u, not its marker %u",
                         j, h->a, g->ctor + g->base);
            else
                snprintf(why, whyn, "segment %zu ends at %s, not its marker %u", j,
                         !h ? "no cell" : h->tag == AV_CELL_APP ? "an application"
                         : "a combinator short of arguments", g->ctor + g->base);
            msg = why;
            st = AV_INTERRUPTED;
            goto out;
        }
        pr->field_off[j + 1] = pr->field_off[j] + g->arity;
        uint32_t s = stk;
        for (uint32_t i = 0; i < g->arity; i++) {
            const av_cell *cc = cons_at(w, s);
            if (!cc) {
                snprintf(why, whyn, "segment %zu has too few fields", j);
                msg = why;
                st = AV_INTERRUPTED;
                goto out;
            }
            pr->fields[pr->field_off[j] + i] = cc->a;
            s = cc->b;
        }
        const av_cell *nil = get(w, s);
        if (!nil || nil->tag != AV_CELL_NIL) {
            snprintf(why, whyn, "segment %zu has too many fields", j);
            msg = why;
            st = AV_INTERRUPTED;
            goto out;
        }
    }
    if (w->nrows >= max_rows) { msg = "the run exceeds the row budget"; goto out; }
    if (!put_row(w, hd, stk, (uint32_t)w->nmem)) { msg = "out of memory"; goto out; }
    st = AV_WHNF;
out:
    free(root_of);
    free(ps);
    if (msg && err) *err = msg;
    return st;
}

bool av_probe_table(const av_witness *w, const av_probe *pr, unsigned min_log,
                    av_buf *out) {
    char line[64];
    size_t k = pow2_at_least(w->nrows, min_log);
    int n = snprintf(line, sizeof line, "starts %zu\n", pr->n + 1);
    if (!out_str(out, line, (size_t)n)) return false;
    for (size_t j = 0; j < pr->n; j++) {
        n = snprintf(line, sizeof line, "%u\n", pr->starts[j]);
        if (!out_str(out, line, (size_t)n)) return false;
    }
    n = snprintf(line, sizeof line, "%zu\n", k - 1);   /* the padded last row */
    if (!out_str(out, line, (size_t)n)) return false;
    n = snprintf(line, sizeof line, "fields %zu\n", pr->n);
    if (!out_str(out, line, (size_t)n)) return false;
    for (size_t j = 0; j < pr->n; j++) {
        n = snprintf(line, sizeof line, "%zu", pr->field_off[j + 1] - pr->field_off[j]);
        if (!out_str(out, line, (size_t)n)) return false;
        for (size_t i = pr->field_off[j]; i < pr->field_off[j + 1]; i++) {
            n = snprintf(line, sizeof line, " %u", pr->fields[i]);
            if (!out_str(out, line, (size_t)n)) return false;
        }
        if (!out_str(out, "\n", 1)) return false;
    }
    return true;
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
        uint32_t n = av_view(a, stk[--top]);
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
        case AV_CELL_ATOM: n = snprintf(line, sizeof line, "X %u\n", c->a); break;
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

/*  ------------------------------------------- composed statements, jetted */

/*  A line cursor: lines as Rust's str::lines splits them (at \n, a \r
 *  before it dropped), and space-separated numbers within one. */
typedef struct { const char *s; size_t len, pos; } lines;

static bool next_line(lines *L, const char **l, size_t *n) {
    if (L->pos >= L->len) return false;
    size_t start = L->pos, end = start;
    while (end < L->len && L->s[end] != '\n') end++;
    bool nl = end < L->len;
    L->pos = nl ? end + 1 : end;
    if (nl && end > start && L->s[end - 1] == '\r') end--;
    *l = L->s + start;
    *n = end - start;
    return true;
}

/*  `key n0 n1 …`, each number a u32: up to max numbers into out, *k of
 *  them.  False unless the line is exactly that. */
static bool nums_line(const char *l, size_t n, const char *key, uint32_t *out, size_t max,
                      size_t *k) {
    size_t kl = strlen(key);
    if (n < kl + 2 || memcmp(l, key, kl) != 0 || l[kl] != ' ') return false;
    size_t i = kl + 1;
    *k = 0;
    for (;;) {
        size_t start = i;
        uint64_t v = 0;
        while (i < n && l[i] >= '0' && l[i] <= '9') {
            v = v * 10 + (uint64_t)(l[i] - '0');
            if (v > UINT32_MAX) return false;
            i++;
        }
        if (i == start || *k == max) return false;
        out[(*k)++] = (uint32_t)v;
        if (i == n) return true;
        if (l[i] != ' ') return false;
        i++;
    }
}

/*  A cell's text, `S`, `K`, `I`, `N`, `A f x`, `C x r` or `X n`, as
 *  bench/plonky3's parse_cell reads it. */
static bool cell_text(const char *l, size_t n, av_cell *c) {
    if (n == 1) {
        switch (l[0]) {
        case 'S': *c = (av_cell){ AV_CELL_S, 0, 0 }; return true;
        case 'K': *c = (av_cell){ AV_CELL_K, 0, 0 }; return true;
        case 'I': *c = (av_cell){ AV_CELL_I, 0, 0 }; return true;
        case 'N': *c = (av_cell){ AV_CELL_NIL, 0, 0 }; return true;
        default:  return false;
        }
    }
    uint32_t v[2];
    size_t k;
    if (nums_line(l, n, "A", v, 2, &k) && k == 2) { *c = (av_cell){ AV_CELL_APP, v[0], v[1] }; return true; }
    if (nums_line(l, n, "C", v, 2, &k) && k == 2) { *c = (av_cell){ AV_CELL_CONS, v[0], v[1] }; return true; }
    if (nums_line(l, n, "X", v, 1, &k) && k == 1) { *c = (av_cell){ AV_CELL_ATOM, v[0], 0 }; return true; }
    return false;
}

void av_cstmt_free(av_cstmt *s) {
    free(s->header);
    free(s->roots);
    free(s->cells);
    memset(s, 0, sizeof *s);
}

static bool log_ok(uint32_t x) { return x >= 8 && x <= 20; }

bool av_cstmt_read(const char *src, size_t len, av_cstmt *s, const char **err) {
    memset(s, 0, sizeof *s);
    lines L = { src, len, 0 };
    const char *l;
    size_t n, k;
    uint32_t v[4];
    const char *msg = "a truncated statement";
    if (!next_line(&L, &l, &n)) goto fail;
    if (!((n >= 8 && memcmp(l, "formula ", 8) == 0) || (n >= 10 && memcmp(l, "predicate ", 10) == 0))) {
        msg = "expected `formula …` or `predicate …`";
        goto fail;
    }
    if (memchr(l, '\0', n)) { msg = "a NUL in the header"; goto fail; }
    s->header = malloc(n + 1);
    if (!s->header) { msg = "out of memory"; goto fail; }
    memcpy(s->header, l, n);
    s->header[n] = '\0';
    msg = "a malformed header";
    if (!next_line(&L, &l, &n) || !nums_line(l, n, "W", v, 1, &k) || k != 1) goto fail;
    s->w = v[0];
    if (!next_line(&L, &l, &n)) goto fail;
    s->log_rows = 11;
    s->log_mem = 11;
    if (n >= 4 && memcmp(l, "log ", 4) == 0) {
        if (!nums_line(l, n, "log", v, 4, &k)) { msg = "a bad `log` line"; goto fail; }
        if (k == 2 && log_ok(v[0]) && log_ok(v[1]) && !(v[0] == 11 && v[1] == 11)) {
            s->log_rows = v[0];
            s->log_mem = v[1];
        } else if (k == 4 && log_ok(v[0]) && log_ok(v[1]) && log_ok(v[2]) && log_ok(v[3])) {
            s->log_rows = v[0];
            s->log_mem = v[1];
            s->log_pop = v[2];
            s->log_instw = v[3];
        } else {
            msg = "a bad `log` line";
            goto fail;
        }
        if (!next_line(&L, &l, &n)) goto fail;
    }
    if (!nums_line(l, n, "bits", v, 1, &k) || k != 1) goto fail;
    s->nbits = v[0];
    if (!next_line(&L, &l, &n) || n < 7 || memcmp(l, "roots ", 6) != 0) goto fail;
    size_t nr = 1;
    for (size_t i = 6; i < n; i++) nr += l[i] == ' ';
    s->roots = malloc(nr * sizeof *s->roots);
    if (!s->roots) { msg = "out of memory"; goto fail; }
    if (!nums_line(l, n, "roots", s->roots, nr, &s->nroots) || s->nroots == 0) goto fail;
    if (!next_line(&L, &l, &n) || !nums_line(l, n, "nil", v, 1, &k) || k != 1) goto fail;
    s->nil = v[0];
    /* the registers: `hd stk ctr` */
    if (!next_line(&L, &l, &n) || n + 2 > 64) goto fail;
    char regs[64] = "r ";
    memcpy(regs + 2, l, n);
    if (!nums_line(regs, n + 2, "r", v, 3, &k) || k != 3) goto fail;
    s->hd0 = v[0];
    s->stk0 = v[1];
    s->ctr0 = v[2];
    if (s->ctr0 > AV_MAX_NODES) { msg = "a heap past the cell budget"; goto fail; }
    s->cells = calloc(s->ctr0 ? s->ctr0 : 1, sizeof *s->cells);
    if (!s->cells) { msg = "out of memory"; goto fail; }
    uint64_t lo = 3, hi = 3 + (uint64_t)s->nbits + s->w;
    msg = "a truncated statement";
    for (uint32_t i = 0; i < s->ctr0; i++) {
        if (!next_line(&L, &l, &n)) goto fail;
        bool blank = n == 1 && l[0] == 'W';
        if (blank != (i >= lo && i < hi)) {
            msg = "the bits and the region are not exactly the blank cells";
            goto fail;
        }
        if (blank) s->cells[i] = (av_cell){ AV_CELL_NIL, 0, 0 };
        else if (!cell_text(l, n, &s->cells[i])) { msg = "a bad cell"; goto fail; }
    }
    if (hi > s->ctr0) {
        msg = "the bits and the region are not exactly the blank cells";
        goto fail;
    }
    if ((uint64_t)s->nbits + s->w > 256) { msg = "too many private cells"; goto fail; }
    return true;
fail:
    if (err) *err = msg;
    av_cstmt_free(s);
    return false;
}

bool av_cwitness_read(const char *src, size_t len, const av_cstmt *s, av_cell *priv,
                      const char **err) {
    lines L = { src, len, 0 };
    const char *l;
    size_t n, i = 0, want = (size_t)s->nbits + s->w;
    while (next_line(&L, &l, &n)) {
        if (n == 0) continue;
        if (i == want) { if (err) *err = "a witness with too many lines"; return false; }
        if (i < s->nbits && n == 1 && l[0] == '1') priv[i] = (av_cell){ AV_CELL_K, 0, 0 };
        else if (i < s->nbits && n == 1 && l[0] == '0') priv[i] = (av_cell){ AV_CELL_APP, 0, 1 };
        else if (!cell_text(l, n, &priv[i])) { if (err) *err = "a bad witness cell"; return false; }
        i++;
    }
    if (i != want) { if (err) *err = "a witness with too few lines"; return false; }
    return true;
}

av_status av_witness_run_composed(const av_cstmt *s, const av_cell *priv, const av_jettable *jt,
                                  av_witness *w, size_t **ends, uint64_t *insts,
                                  const char **err) {
    memset(w, 0, sizeof *w);
    *ends = NULL;
    if (insts) *insts = 0;
    const char *msg = NULL;
    av_status st = AV_SIZE;
    uint32_t *root_of = NULL, *ps = NULL;
    if (s->log_pop == 0) { msg = "the statement fixes no budgets"; goto out; }
    size_t max_rows = (size_t)1 << s->log_rows, max_cells = (size_t)1 << s->log_mem;
    /* the statement's heap, its private cells the witness's */
    for (uint32_t i = 0; i < s->ctr0; i++) {
        bool p = i >= 3 && i < 3 + (uint64_t)s->nbits + s->w;
        if (!put_cell(w, p ? priv[i - 3].tag : s->cells[i].tag, p ? priv[i - 3].a : s->cells[i].a,
                      p ? priv[i - 3].b : s->cells[i].b)) { msg = "out of memory"; goto out; }
    }
    w->loaded = w->nmem;
    w->hd0 = s->hd0;
    w->stk0 = s->stk0;
    if (w->nmem > max_cells) { msg = "the run exceeds the statement's memory"; goto out; }
    uint32_t maxk = 1;
    for (size_t j = 0; j < jt->njets; j++)
        if (jt->jets[j].k > maxk) maxk = jt->jets[j].k;
    root_of = calloc(w->loaded ? w->loaded : 1, sizeof *root_of);
    ps = calloc(maxk, sizeof *ps);
    *ends = calloc(s->nroots, sizeof **ends);
    if (!root_of || !ps || !*ends) { msg = "out of memory"; goto out; }
    for (size_t i = 0; i < jt->nroots; i++) {
        if (jt->root_addr[i] >= w->loaded) { msg = "a root outside the statement's heap"; goto out; }
        root_of[jt->root_addr[i]] = jt->root_jet[i] + 1;
    }
    for (size_t j = 0; j < s->nroots; j++) {
        uint32_t hd = s->roots[j], stk = s->nil;
        if (!run_to_halt(w, jt, root_of, ps, &hd, &stk, max_rows, max_cells, insts, &msg)) goto out;
        (*ends)[j] = w->nrows - 1;
        const av_cell *h = get(w, hd), *t = get(w, stk);
        if (!h || h->tag != AV_CELL_K || !t || t->tag != AV_CELL_NIL) {
            msg = "a segment does not end at K over a nil: the witness does not satisfy the statement";
            st = AV_INTERRUPTED;
            goto out;
        }
    }
    if (w->pops > ((uint64_t)1 << s->log_pop)) { msg = "the run's pops exceed POP's budget"; goto out; }
    if (w->wcells > ((uint64_t)1 << s->log_instw)) { msg = "the run's written cells exceed INSTW's budget"; goto out; }
    st = AV_WHNF;
out:
    free(root_of);
    free(ps);
    if (st != AV_WHNF) {
        free(*ends);
        *ends = NULL;
        if (err) *err = msg;
    }
    return st;
}

static bool out_cell(av_buf *out, const av_cell *c) {
    char line[64];
    int n;
    switch (c->tag) {
    case AV_CELL_S:    n = snprintf(line, sizeof line, "S\n"); break;
    case AV_CELL_K:    n = snprintf(line, sizeof line, "K\n"); break;
    case AV_CELL_I:    n = snprintf(line, sizeof line, "I\n"); break;
    case AV_CELL_APP:  n = snprintf(line, sizeof line, "A %u %u\n", c->a, c->b); break;
    case AV_CELL_NIL:  n = snprintf(line, sizeof line, "N\n"); break;
    case AV_CELL_CONS: n = snprintf(line, sizeof line, "C %u %u\n", c->a, c->b); break;
    case AV_CELL_ATOM: n = snprintf(line, sizeof line, "X %u\n", c->a); break;
    default:           return false;
    }
    return out_str(out, line, (size_t)n);
}

bool av_composed_table(const av_cstmt *s, const av_witness *w, const size_t *ends,
                       av_buf *out) {
    char line[64];
    size_t msize = (size_t)1 << s->log_mem, k = (size_t)1 << s->log_rows;
    if (w->nrows == 0 || w->nrows > k || w->nmem > msize) return false;
    if (!out_str(out, s->header, strlen(s->header))) return false;
    int n = snprintf(line, sizeof line, "\nW %u\n%zu\n", s->w, msize);
    if (!out_str(out, line, (size_t)n)) return false;
    const av_cell nil = { AV_CELL_NIL, 0, 0 };
    for (size_t i = 0; i < msize; i++)
        if (!out_cell(out, i < w->nmem ? &w->mem[i] : &nil)) return false;
    n = snprintf(line, sizeof line, "ends %zu\n", s->nroots);
    if (!out_str(out, line, (size_t)n)) return false;
    for (size_t j = 0; j < s->nroots; j++) {
        n = snprintf(line, sizeof line, "%zu\n", j + 1 < s->nroots ? ends[j] : k - 1);
        if (!out_str(out, line, (size_t)n)) return false;
    }
    n = snprintf(line, sizeof line, "%zu\n", k);
    if (!out_str(out, line, (size_t)n)) return false;
    for (size_t i = 0; i < k; i++) {
        const av_row *r = &w->rows[i < w->nrows ? i : w->nrows - 1];
        n = snprintf(line, sizeof line, "%u %u %u\n", r->hd, r->stk, r->ctr);
        if (!out_str(out, line, (size_t)n)) return false;
    }
    return true;
}
