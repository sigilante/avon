/**  print.c
 *
 *  The printed form, written without recursion and under a node budget
 *  (docs/DESIGN.md §4.1): a work stack of nodes still to print and the
 *  punctuation between them.
 */

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

        w = av_res(a, w);
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
        uint32_t arg = av_res(a, av_right(a, w));
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
