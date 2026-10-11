/**  wire.c
 *
 *  Terms at rest: the container, Tromp's bitstring with a third leaf, and
 *  the atom-name hygiene check.  Neither jam nor cue recurses.
 */

#include <stdlib.h>
#include <string.h>

#include "avon.h"

/*  ---------------------------------------------------------------- birds */

/*  aviary_kernel 0.1.0's live combinators other than S, K, I: every name
 *  in birds.BY_NAME and BUILTIN_ALIAS_KEYS for which Environment.lookup
 *  answers.  Regenerate on an oracle upgrade.
 */
static const char *const birds[] = {
    "B", "B1", "B2", "B3", "C", "C*", "C**", "D", "D1", "D2", "E", "E^",
    "F", "F*", "F**", "G", "H", "I*", "I**", "J", "KM", "KM'", "Ki", "L",
    "M", "M2", "O", "Phi", "Psi", "Q", "Q1", "Q2", "Q3", "Q4", "R", "R*",
    "R**", "T", "Theta", "U", "V", "V*", "V**", "W", "W'", "W*", "W**",
    "Y", "\xc3\x8a" /* Ê */, "\xce\x98" /* Θ */, "\xce\xa6" /* Φ */,
    "\xce\xa8" /* Ψ */,
};

bool av_is_bird(const char *name, size_t len) {
    for (size_t i = 0; i < sizeof birds / sizeof birds[0]; i++)
        if (strlen(birds[i]) == len && memcmp(birds[i], name, len) == 0)
            return true;
    return false;
}

/*  ------------------------------------------------------------------ bits */

typedef struct { av_buf *b; size_t start; uint64_t nbits; bool ok; } writer;

static void put_bytes(writer *w, const void *p, size_t n) {
    av_buf *b = w->b;
    if (!w->ok) return;
    if (b->len + n + 1 > b->cap) {
        size_t cap = b->cap ? b->cap : 256;
        while (b->len + n + 1 > cap) cap *= 2;
        char *s = realloc(b->s, cap);
        if (!s) { w->ok = false; return; }
        b->s = s;
        b->cap = cap;
    }
    memcpy(b->s + b->len, p, n);
    b->len += n;
    b->s[b->len] = '\0';
}

static void put_le(writer *w, uint64_t v, int bytes) {
    uint8_t x[8];
    for (int i = 0; i < bytes; i++) x[i] = (uint8_t)(v >> (8 * i));
    put_bytes(w, x, (size_t)bytes);
}

static void put_bit(writer *w, unsigned bit) {
    if (w->nbits % 8 == 0) {
        uint8_t zero = 0;
        put_bytes(w, &zero, 1);
    }
    if (w->ok && bit)
        w->b->s[w->start + w->nbits / 8] |= (char)(1u << (w->nbits % 8));
    w->nbits++;
}

static unsigned bit_width(uint32_t n) {
    unsigned w = 0;
    while (n) { w++; n >>= 1; }
    return w;
}

/*  ------------------------------------------------------------------- jam */

bool av_jam(const av_arena *a, uint32_t t, size_t budget, av_buf *out,
            const char **err) {
    /* pass 1: the atoms in first-met order, under the budget */
    uint32_t *order = calloc(a->n_leaves, sizeof *order);  /* id -> k, 0 none */
    uint32_t *seq = malloc(a->n_leaves * sizeof *seq);     /* k-1 -> id       */
    size_t cap = 256, top = 0, visited = 0;
    uint32_t *stk = malloc(cap * sizeof *stk);
    uint32_t natoms = 0;
    const char *msg = NULL;
    if (!order || !seq || !stk) { msg = "out of memory"; goto done; }

    stk[top++] = t;
    while (top) {
        uint32_t n = av_view(a, stk[--top]);
        if (++visited > budget) { msg = "node budget exceeded"; goto done; }
        if (av_tag(a, n) == AV_LEAF) {
            ski_leaf id = av_right(a, n);
            if (!ski_is_comb(id) && !order[id]) {
                order[id] = ++natoms;
                seq[natoms - 1] = id;
            }
            continue;
        }
        if (av_tag(a, n) != AV_APP) { msg = "jet node in term"; goto done; }
        if (top + 2 > cap) {
            uint32_t *p = realloc(stk, (cap *= 2) * sizeof *p);
            if (!p) { msg = "out of memory"; goto done; }
            stk = p;
        }
        stk[top++] = av_right(a, n);          /* function first: push it last */
        stk[top++] = av_left(a, n);
    }

    /* header and atom table */
    writer w = { out, 0, 0, true };
    put_bytes(&w, "SKIT\x01\0\0\0", 8);
    put_le(&w, natoms, 4);
    for (uint32_t k = 0; k < natoms; k++) {
        const char *nm = av_leaf_name(a, seq[k]);
        size_t len = strlen(nm);
        put_le(&w, len, 4);
        put_bytes(&w, nm, len);
    }
    size_t nbits_at = out->len;
    put_le(&w, 0, 8);                       /* bit count, patched below */
    w.start = out->len;

    /* pass 2: the bits, pre-order */
    unsigned width = bit_width(natoms);
    top = 0;
    stk[top++] = t;
    while (top && w.ok) {
        uint32_t n = av_view(a, stk[--top]);
        if (av_tag(a, n) == AV_APP) {
            put_bit(&w, 1);
            put_bit(&w, 1);
            stk[top++] = av_right(a, n);      /* capacity reached in pass 1 */
            stk[top++] = av_left(a, n);
            continue;
        }
        ski_leaf id = av_right(a, n);
        if (id == SKI_S)      { put_bit(&w, 0); put_bit(&w, 0); continue; }
        if (id == SKI_K)      { put_bit(&w, 0); put_bit(&w, 1); continue; }
        put_bit(&w, 1);
        put_bit(&w, 0);
        uint32_t k = id == SKI_I ? 0 : order[id];
        for (unsigned i = 0; i < width; i++) put_bit(&w, k >> i & 1u);
    }
    if (!w.ok) { msg = "out of memory"; goto done; }
    for (int i = 0; i < 8; i++)
        out->s[nbits_at + (size_t)i] = (char)(w.nbits >> (8 * i));

done:
    free(order);
    free(seq);
    free(stk);
    if (msg && err) *err = msg;
    return msg == NULL;
}

/*  ------------------------------------------------------------------- cue */

typedef struct { const uint8_t *p; size_t n, pos; } reader;

static bool get_le(reader *r, int bytes, uint64_t *v) {
    if (r->n - r->pos < (size_t)bytes) return false;
    *v = 0;
    for (int i = 0; i < bytes; i++) *v |= (uint64_t)r->p[r->pos + (size_t)i] << (8 * i);
    r->pos += (size_t)bytes;
    return true;
}

static int cmp_u32(const void *x, const void *y) {
    uint32_t a = *(const uint32_t *)x, b = *(const uint32_t *)y;
    return (a > b) - (a < b);
}

static bool valid_name(const uint8_t *s, size_t len) {
    if (len == 0) return false;
    for (size_t i = 0; i < len; i++) {
        uint8_t c = s[i];
        if (c == 0 || c == ' ' || c == '\t' || c == '\n' || c == '\r' ||
            c == '(' || c == ')' || c == '`')
            return false;           /* it must print and parse back */
    }
    if (s[0] == '@') return false;  /* reserved for probe markers */
    return !(len == 1 && (s[0] == 'S' || s[0] == 'K' || s[0] == 'I'));
}

uint32_t av_cue(av_arena *a, const uint8_t *p, size_t n, const char **err) {
    reader r = { p, n, 0 };
    const char *msg = NULL;
    uint32_t *atoms = NULL, *stk = NULL, root = AV_NONE;
    uint64_t v, natoms, nbits;

    if (n < 8 || memcmp(p, "SKIT", 4) != 0) { msg = "not a SKIT container"; goto done; }
    if (p[4] != 1) { msg = "unknown container version"; goto done; }
    if (p[5] || p[6] || p[7]) { msg = "reserved bytes not zero"; goto done; }
    r.pos = 8;
    if (!get_le(&r, 4, &natoms)) { msg = "truncated atom count"; goto done; }
    if (natoms > (n - r.pos) / 5) { msg = "atom count exceeds input"; goto done; }

    atoms = malloc((natoms + 1) * sizeof *atoms);
    if (!atoms) { msg = "out of memory"; goto done; }
    atoms[0] = AV_NODE_I;
    /* the whole table checked before any name is interned, so a refused
     * container leaves the arena's atoms as they were */
    size_t names_at = r.pos;
    for (uint64_t k = 1; k <= natoms; k++) {
        if (!get_le(&r, 4, &v) || v > n - r.pos) { msg = "truncated atom name"; goto done; }
        const uint8_t *nm = p + r.pos;
        size_t len = (size_t)v;
        r.pos += len;
        if (!valid_name(nm, len)) { msg = "invalid atom name"; goto done; }
        if (!a->allow_bird_atoms && av_is_bird((const char *)nm, len)) {
            msg = "atom named like a live aviary combinator (§4.3)";
            goto done;
        }
    }
    r.pos = names_at;
    for (uint64_t k = 1; k <= natoms; k++) {
        get_le(&r, 4, &v);
        uint32_t leaf = av_leaf(a, (const char *)p + r.pos, (size_t)v);
        r.pos += (size_t)v;
        if (leaf == AV_NONE) { msg = "out of memory"; goto done; }
        atoms[k] = leaf;
    }
    if (natoms > 1) {                           /* each name once: sorted, no neighbours alike */
        uint32_t *sorted = malloc(natoms * sizeof *sorted);
        if (!sorted) { msg = "out of memory"; goto done; }
        memcpy(sorted, atoms + 1, natoms * sizeof *sorted);
        qsort(sorted, natoms, sizeof *sorted, cmp_u32);
        bool dup = false;
        for (uint64_t k = 1; k < natoms && !dup; k++) dup = sorted[k] == sorted[k - 1];
        free(sorted);
        if (dup) { msg = "duplicate atom name"; goto done; }
    }
    if (!get_le(&r, 8, &nbits)) { msg = "truncated bit count"; goto done; }
    if (nbits == 0 || nbits > (uint64_t)(n - r.pos) * 8 ||
        (nbits + 7) / 8 != n - r.pos) {
        msg = "bit count does not match the input";
        goto done;
    }

    const uint8_t *bits = p + r.pos;
    uint64_t at = 0, seen = 0;  /* atoms met so far: they must come in order */
    unsigned width = bit_width((uint32_t)natoms);
#define BIT() (bits[at / 8] >> (at % 8) & 1u)

    /* A stack of applications waiting on a child: the entry holds the
     * function once it is done, AV_NONE before. */
    size_t cap = 64, top = 0;
    stk = malloc(cap * sizeof *stk);
    if (!stk) { msg = "out of memory"; goto done; }
    for (;;) {
        if (nbits - at < 2) { msg = "truncated bitstring"; goto done; }
        unsigned b0 = BIT(); at++;
        unsigned b1 = BIT(); at++;
        uint32_t t;
        if (b0 && b1) {                          /* 11: application */
            if (top == cap) {
                uint32_t *q = realloc(stk, (cap *= 2) * sizeof *q);
                if (!q) { msg = "out of memory"; goto done; }
                stk = q;
            }
            stk[top++] = AV_NONE;
            continue;
        }
        if (!b0) {
            t = b1 ? AV_NODE_K : AV_NODE_S;
        } else {                                 /* 10: I or an atom */
            if (nbits - at < width) { msg = "truncated atom index"; goto done; }
            uint64_t k = 0;
            for (unsigned i = 0; i < width; i++, at++) k |= (uint64_t)BIT() << i;
            if (k > natoms) { msg = "atom index out of range"; goto done; }
            if (k > seen) {
                if (k != seen + 1) { msg = "atom table not in first-met order"; goto done; }
                seen = k;
            }
            t = atoms[k];
        }
        /* t is complete: feed it to the waiting applications */
        for (;;) {
            if (top == 0) { root = t; goto finished; }
            if (stk[top - 1] == AV_NONE) {       /* it was the function */
                stk[top - 1] = t;
                break;
            }
            uint32_t app = av_app(a, stk[--top], t);
            if (app == AV_NONE) { msg = "out of memory"; goto done; }
            t = app;
        }
    }
finished:
    if (at != nbits) { msg = "bits after the end of the term"; goto done; }
    if (seen != natoms) { msg = "atom table names an unused atom"; goto done; }
    for (uint64_t i = at; i < (nbits + 7) / 8 * 8; i++)
        if (bits[i / 8] >> (i % 8) & 1u) { msg = "padding not zero"; goto done; }
#undef BIT

done:
    free(atoms);
    free(stk);
    if (msg) {
        if (err) *err = msg;
        return AV_NONE;
    }
    return root;
}
