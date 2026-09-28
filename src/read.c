/**  read.c
 *
 *  The printed form, parsed without recursion: a stack of partial
 *  applications, one per open parenthesis (docs/DESIGN.md §4.1).
 */

#include <stdlib.h>

#include "avon.h"

static bool is_space(char c) {
    return c == ' ' || c == '\t' || c == '\n' || c == '\r';
}

static bool is_name(char c) {
    return !is_space(c) && c != '(' && c != ')' && c != '\0';
}

typedef struct { uint32_t *acc; size_t *open; size_t depth, cap; } levels;

static bool push_level(levels *lv, size_t pos) {
    if (lv->depth == lv->cap) {
        size_t cap = lv->cap ? lv->cap * 2 : 64;
        uint32_t *acc = realloc(lv->acc, cap * sizeof *acc);
        if (!acc) return false;
        lv->acc = acc;
        size_t *open = realloc(lv->open, cap * sizeof *open);
        if (!open) return false;
        lv->open = open;
        lv->cap = cap;
    }
    lv->acc[lv->depth] = AV_NONE;
    lv->open[lv->depth] = pos;
    lv->depth++;
    return true;
}

/* Apply the innermost level's accumulated term to t, or start it with t. */
static bool juxtapose(av_arena *a, levels *lv, uint32_t t) {
    uint32_t *acc = &lv->acc[lv->depth - 1];
    if (*acc == AV_NONE) {
        *acc = t;
        return true;
    }
    uint32_t app = av_app(a, *acc, t);
    if (app == AV_NONE) return false;
    *acc = app;
    return true;
}

uint32_t av_parse(av_arena *a, const char *src, size_t len,
                  av_parse_error *err) {
    levels lv = { 0 };
    uint32_t out = AV_NONE;
    const char *msg = NULL;
    size_t i = 0;

    if (!push_level(&lv, 0)) { msg = "out of memory"; goto done; }
    while (i < len) {
        char c = src[i];
        if (c == '\0') {
            msg = "NUL byte in input";      /* names are C strings */
            goto done;
        } else if (is_space(c)) {
            i++;
        } else if (c == '(') {
            if (!push_level(&lv, i)) { msg = "out of memory"; goto done; }
            i++;
        } else if (c == ')') {
            if (lv.depth == 1) { msg = "unmatched ')'"; goto done; }
            uint32_t t = lv.acc[--lv.depth];
            if (t == AV_NONE) { msg = "empty parentheses"; goto done; }
            if (!juxtapose(a, &lv, t)) { msg = "out of memory"; goto done; }
            i++;
        } else {
            size_t start = i;
            while (i < len && is_name(src[i])) i++;
            if (!a->allow_bird_atoms && av_is_bird(src + start, i - start)) {
                i = start;
                msg = "atom named like a live aviary combinator (§4.3)";
                goto done;
            }
            uint32_t leaf = av_leaf(a, src + start, i - start);
            if (leaf == AV_NONE || !juxtapose(a, &lv, leaf)) {
                msg = "out of memory";
                goto done;
            }
        }
    }
    if (lv.depth > 1) {
        i = lv.open[lv.depth - 1];
        msg = "unmatched '('";
    } else if (lv.acc[0] == AV_NONE) {
        msg = "empty term";
    } else {
        out = lv.acc[0];
    }

done:
    if (msg && err) {
        err->pos = i;
        err->msg = msg;
    }
    free(lv.acc);
    free(lv.open);
    return msg ? AV_NONE : out;
}
