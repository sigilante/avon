/**  print.c
 *
 *  The printed form, written without recursion and under a node budget:
 *  a work stack of nodes still to print and the punctuation between them.
 *  And the DAG form, which prints each node once, so sharing survives.
 */

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "avon.h"

void av_buf_free(av_buf *b) {
    free(b->s);
    *b = (av_buf){ 0 };
}

static bool put(av_buf *b, const char *s, size_t n) {
    if (b->len + n + 1 > b->cap) {
        size_t cap = b->cap ? b->cap : 256;
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

/* A work item: a node to print, or one of these punctuation marks. */
#define W_SPACE (AV_NONE - 0)
#define W_OPEN  (AV_NONE - 1)
#define W_CLOSE (AV_NONE - 2)

bool av_print(const av_arena *a, uint32_t t, size_t budget, av_buf *b) {
    size_t cap = 64, top = 0, visited = 0;
    uint32_t *work = malloc(cap * sizeof *work);
    bool ok = work != NULL;
    if (ok) work[top++] = t;

    while (ok && top) {
        uint32_t w = work[--top];
        if (w == W_SPACE) { ok = put(b, " ", 1); continue; }
        if (w == W_OPEN)  { ok = put(b, "(", 1); continue; }
        if (w == W_CLOSE) { ok = put(b, ")", 1); continue; }
        if (++visited > budget) { ok = false; break; }

        w = av_view(a, w);
        if (av_tag(a, w) == AV_LEAF) {
            const char *nm = av_leaf_name(a, av_right(a, w));
            ok = put(b, nm, strlen(nm));
            continue;
        }
        if (top + 5 > cap) {
            cap *= 2;
            uint32_t *p = realloc(work, cap * sizeof *p);
            if (!p) { ok = false; break; }
            work = p;
        }
        /* fn, then " ", then arg, parenthesized if it is an application */
        uint32_t arg = av_view(a, av_right(a, w));
        bool paren = av_tag(a, arg) == AV_APP;
        if (paren) work[top++] = W_CLOSE;
        work[top++] = arg;
        if (paren) work[top++] = W_OPEN;
        work[top++] = W_SPACE;
        work[top++] = av_left(a, w);
    }
    free(work);
    return ok;
}

/*  ---------------------------------------------------------- the DAG form */

/*  Node -> id, open addressing; ids are assigned 1, 2, ... so 0 marks a
 *  node seen but not yet numbered, and a missing key is UINT32_MAX. */
typedef struct { uint32_t *key; uint64_t *id; size_t cap, used; } nmap;

static size_t nmap_slot(const nmap *m, uint32_t k) {
    size_t i = (size_t)((uint64_t)k * 0x9e3779b97f4a7c15u >> 32) & (m->cap - 1);
    while (m->key[i] != UINT32_MAX && m->key[i] != k) i = (i + 1) & (m->cap - 1);
    return i;
}

static bool nmap_grow(nmap *m) {
    size_t ncap = m->cap ? 2 * m->cap : 1024;
    uint32_t *nk = malloc(ncap * sizeof *nk);
    uint64_t *ni = malloc(ncap * sizeof *ni);
    if (!nk || !ni) { free(nk); free(ni); return false; }
    memset(nk, 0xff, ncap * sizeof *nk);
    nmap old = *m;
    m->key = nk; m->id = ni; m->cap = ncap;
    for (size_t i = 0; i < old.cap; i++)
        if (old.key[i] != UINT32_MAX) {
            size_t j = nmap_slot(m, old.key[i]);
            m->key[j] = old.key[i];
            m->id[j] = old.id[i];
        }
    free(old.key);
    free(old.id);
    return true;
}

bool av_print_dag(const av_arena *a, uint32_t t, size_t budget, av_buf *b) {
    nmap m = { 0 };
    size_t cap = 64, top = 0;
    uint32_t *work = malloc(cap * sizeof *work);  /* a node, its bit 31 set once its children are out */
    bool ok = work != NULL && nmap_grow(&m) && put(b, "dag", 3);
    uint64_t next = 0;
    char num[64];
    t = av_view(a, t);
    if (ok) work[top++] = t;
    /* post-order: a node is printed after both its children, each once */
    while (ok && top) {
        uint32_t w = work[--top];
        bool expanded = (w & 0x80000000u) != 0;
        w &= 0x7fffffffu;
        size_t s = nmap_slot(&m, w);
        if (m.key[s] == w && m.id[s]) continue;     /* already printed */
        if (av_tag(a, w) == AV_LEAF) {
            const char *nm = av_leaf_name(a, av_right(a, w));
            int n = snprintf(num, sizeof num, " %" PRIu64 "=", next);
            ok = put(b, num, (size_t)n) && put(b, nm, strlen(nm));
        } else if (!expanded) {
            if (m.key[s] != w) {                     /* first sight: count it */
                if (++m.used > budget) { ok = false; break; }
                if (2 * m.used > m.cap) {
                    if (!nmap_grow(&m)) { ok = false; break; }
                    s = nmap_slot(&m, w);
                }
                m.key[s] = w;
                m.id[s] = 0;
            }
            if (top + 3 > cap) {
                uint32_t *p = realloc(work, (cap *= 2) * sizeof *p);
                if (!p) { ok = false; break; }
                work = p;
            }
            work[top++] = w | 0x80000000u;
            work[top++] = av_view(a, av_right(a, w));
            work[top++] = av_view(a, av_left(a, w));
            continue;
        } else {
            size_t sl = nmap_slot(&m, av_view(a, av_left(a, w)));
            size_t sr = nmap_slot(&m, av_view(a, av_right(a, w)));
            int n = snprintf(num, sizeof num, " %" PRIu64 "=%" PRIu64 ".%" PRIu64, next,
                             m.id[sl] - 1, m.id[sr] - 1);
            ok = put(b, num, (size_t)n);
        }
        if (!ok) break;
        /* number the node just printed: a leaf may be new to the map */
        if (m.key[s] != w) {
            if (++m.used > budget) { ok = false; break; }
            if (2 * m.used > m.cap) {
                if (!nmap_grow(&m)) { ok = false; break; }
                s = nmap_slot(&m, w);
            }
            m.key[s] = w;
        }
        m.id[s] = ++next;
    }
    if (ok) {
        size_t s = nmap_slot(&m, t);
        int n = snprintf(num, sizeof num, " @%" PRIu64, m.id[s] - 1);
        ok = put(b, num, (size_t)n);
    }
    free(work);
    free(m.key);
    free(m.id);
    return ok;
}
