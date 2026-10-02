/**  read.c
 *
 *  The printed form, parsed without recursion: a stack of partial
 *  applications, one per open parenthesis (docs/DESIGN.md §4.1).
 */

#include <stdlib.h>
#include <string.h>

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
            if (src[start] == '@') {
                i = start;
                msg = "atom names beginning with @ are reserved for probe markers";
                goto done;
            }
            if (memchr(src + start, '`', i - start)) {
                i = start;
                msg = "` belongs to the prefix form, not to atom names";
                goto done;
            }
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

/*  ------------------------------------------------------------- the DAG form */

/*  `dag <id>=<rhs> ... @<root>`: a shared graph on one line, the form frame
 *  dumps print (docs/RUNTIME.md, "Frame traces").  <rhs> is a leaf name (S,
 *  K, I or an atom) or <l>.<r>, two ids defined before it; ids are numbers
 *  below 2^64-1, local to the term, each defined once.  The root comes
 *  last: only blanks may follow it.  The graph is rebuilt node for node, so a
 *  term the tree printer would unfold exponentially is read in its size. */
/*  A dag id at src[*i]: digits, below 2^64 - 1 (the table keys id + 1). */
static bool dag_id(const char *src, size_t len, size_t *i, uint64_t *id) {
    size_t s = *i;
    uint64_t v = 0;
    while (*i < len && src[*i] >= '0' && src[*i] <= '9') {
        uint64_t d = (uint64_t)(src[(*i)++] - '0');
        if (v > (UINT64_MAX - 1 - d) / 10) return false;
        v = v * 10 + d;
    }
    *id = v;
    return *i > s;
}

uint32_t av_parse_dag(av_arena *a, const char *src, size_t len, const char **msg) {
    size_t i = 0;
    while (i < len && (src[i] == ' ' || src[i] == '\t')) i++;
    if (len - i < 4 || memcmp(src + i, "dag ", 4) != 0) { *msg = "not the dag form"; return AV_NONE; }
    i += 4;
    size_t cap = 1024;                      /* open addressing: id -> node */
    uint64_t *key = calloc(cap, sizeof *key);
    uint32_t *val = malloc(cap * sizeof *val);
    size_t used = 0;
    uint32_t root = AV_NONE;
    *msg = NULL;
    if (!key || !val) { *msg = "out of memory"; goto out; }
#define FIND(id, slot)                                                         \
    do {                                                                       \
        slot = (size_t)(((id) + 1) * 0x9e3779b97f4a7c15u >> 20) & (cap - 1);   \
        while (key[slot] && key[slot] != (id) + 1) slot = (slot + 1) & (cap - 1); \
    } while (0)
    for (;;) {
        while (i < len && (src[i] == ' ' || src[i] == '\t')) i++;
        if (i >= len || src[i] == '\n' || src[i] == '\r') break;
        if (src[i] == '@') {
            i++;
            uint64_t id;
            if (!dag_id(src, len, &i, &id)) { *msg = "a root id expected after '@'"; goto out; }
            size_t slot;
            FIND(id, slot);
            if (!key[slot]) { *msg = "the root is not defined"; goto out; }
            root = val[slot];
            /* the root ends the term: nothing but blanks may follow */
            while (i < len && (src[i] == ' ' || src[i] == '\t' || src[i] == '\n' || src[i] == '\r')) i++;
            if (i < len) { *msg = "text after the root"; goto out; }
            break;
        }
        uint64_t id;
        if (!dag_id(src, len, &i, &id) || i >= len || src[i] != '=') {
            *msg = "<id>= expected, the id below 2^64-1";
            goto out;
        }
        i++;
        uint32_t node;
        if (i < len && src[i] >= '0' && src[i] <= '9') {
            uint64_t l, r;
            if (!dag_id(src, len, &i, &l) || i >= len || src[i] != '.') {
                *msg = "<l>.<r> expected";
                goto out;
            }
            i++;
            if (!dag_id(src, len, &i, &r)) { *msg = "<l>.<r> expected"; goto out; }
            size_t sl, sr;
            FIND(l, sl);
            FIND(r, sr);
            if (!key[sl] || !key[sr]) { *msg = "an id used before it is defined"; goto out; }
            node = av_app(a, val[sl], val[sr]);
        } else {
            size_t s2 = i;
            while (i < len && src[i] != ' ' && src[i] != '\t' && src[i] != '\n' && src[i] != '\r') i++;
            if (i == s2) { *msg = "a leaf name expected"; goto out; }
            if (src[s2] == '@' || src[s2] == '`') { *msg = "a reserved leaf name"; goto out; }
            if (!(i - s2 == 1 && (src[s2] == 'S' || src[s2] == 'K' || src[s2] == 'I')) &&
                !a->allow_bird_atoms && av_is_bird(src + s2, i - s2)) {
                *msg = "atom named like a live aviary combinator (§4.3)";
                goto out;
            }
            node = av_leaf(a, src + s2, i - s2);
        }
        if (node == AV_NONE) { *msg = "out of memory"; goto out; }
        if (2 * (used + 1) > cap) {             /* grow the table */
            size_t ncap = cap * 2;
            uint64_t *nk = calloc(ncap, sizeof *nk);
            uint32_t *nv = malloc(ncap * sizeof *nv);
            if (!nk || !nv) { free(nk); free(nv); *msg = "out of memory"; goto out; }
            for (size_t k = 0; k < cap; k++) {
                if (!key[k]) continue;
                size_t sl = (size_t)(key[k] * 0x9e3779b97f4a7c15u >> 20) & (ncap - 1);
                while (nk[sl]) sl = (sl + 1) & (ncap - 1);
                nk[sl] = key[k];
                nv[sl] = val[k];
            }
            free(key); free(val);
            key = nk; val = nv; cap = ncap;
        }
        size_t slot;
        FIND(id, slot);
        if (key[slot]) { *msg = "an id defined twice"; goto out; }
        key[slot] = id + 1;
        val[slot] = node;
        used++;
    }
#undef FIND
    if (root == AV_NONE && !*msg) *msg = "no root: '@<id>' expected";
out:
    free(key);
    free(val);
    return *msg ? AV_NONE : root;
}
