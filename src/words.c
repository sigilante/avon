/**  words.c
 *
 *  Words (docs/DESIGN.md §6.10): Scott numerals held as numbers.  W n, for
 *  n >= 1, is a jet node flagged AV_JET_WORD whose id field holds n and
 *  whose term is SUC (W (n-1)), W 0 being K.  A reader sees the numeral
 *  through av_view, node for node, and the predecessor is the term's right
 *  child.  SUC is skijack's successor, \n z s. s n, the constructor term
 *  every `Zero | Suc t` type compiles to, so a numeral is recognized by its
 *  term, whatever the program calls its type.
 *
 *  Words come from three places, and none forces anything: closed
 *  numerals in the loaded program (av_words_scan), a template instance
 *  applying SUC to a numeral already held (tmpl_instance, the operations
 *  av_words_mark finds), and the numeral operations, which fire only on
 *  words (reduce.c).  An operation is skijack's term for it, found by its
 *  hash; word_admit runs that term on small numerals before the native
 *  code may stand in for it.
 */

#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "jets.h"

static const char SUC_TEXT[] = "S (K K) (S (K (S I)) K)";

void av_fix_on(av_arena *a) {
    a->fix_on = true;
}

bool av_words_on(av_arena *a) {
    if (a->word_suc) return true;
    av_parse_error pe;
    uint32_t t = av_parse(a, SUC_TEXT, sizeof SUC_TEXT - 1, &pe);
    if (t == AV_NONE) return false;
    a->word_suc = t;
    return true;
}

uint32_t word_succ(av_arena *a, uint32_t pred) {
    uint32_t n;
    pred = av_res(a, pred);
    if (!a->word_suc || !av_numeral(a, pred, &n) || n >= AV_WORD_MAX) return AV_NONE;
    uint32_t t = arena_app_reserved(a, a->word_suc, pred);
    uint32_t w = arena_app_reserved(a, t, t);
    arena_set(a, w, (av_node){ (AV_JET << AV_TAG_SHIFT) | AV_JET_WORD | (n + 1), t });
    return w;
}

/*  Whether x denotes SUC: compared as trees, x seen through its wrappers. */
static bool is_suc(const av_arena *a, uint32_t x, nmap *memo) {
    uint32_t v = av_view(a, x);
    uint64_t got;
    if (nmap_get(memo, v, &got)) return got != 0;
    bool yes = av_tag(a, v) == AV_APP && av_equal(a, v, a->word_suc, 64) == 1;
    nmap_put(memo, v, yes);
    return yes;
}

/*  ------------------------------------------------------------ the scan */

/*  Every closed numeral below t, children first: an application of SUC to
 *  K or to a word becomes a word, in place, so each parent keeps it. */
static bool scan(av_arena *a, uint32_t t, nmap *seen, nmap *memo, long *made) {
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 256, top = 0;
    item *todo = malloc(cap * sizeof *todo);
    if (!todo) return false;
    todo[top++] = (item){ t, false };
    bool ok = true;
    while (ok && top) {
        item it = todo[--top];
        uint32_t x = av_res(a, it.node);
        uint64_t v;
        if (av_tag(a, x) != AV_APP) continue;          /* leaves, jets, words */
        if (!it.done) {
            if (nmap_get(seen, x, &v)) continue;
            if (!(ok = nmap_put(seen, x, 1))) break;
            if (top + 3 > cap) {
                item *q = realloc(todo, (cap *= 2) * sizeof *q);
                if (!q) { ok = false; break; }
                todo = q;
            }
            todo[top++] = (item){ x, true };
            todo[top++] = (item){ av_right(a, x), false };
            todo[top++] = (item){ av_left(a, x), false };
            continue;
        }
        uint32_t pred = av_res(a, av_right(a, x)), n;
        if (!av_numeral(a, pred, &n) || n >= AV_WORD_MAX || !is_suc(a, av_left(a, x), memo))
            continue;
        uint32_t st = av_app(a, a->word_suc, pred);
        if (st == AV_NONE) { ok = false; break; }
        arena_set(a, x, (av_node){ (AV_JET << AV_TAG_SHIFT) | AV_JET_WORD | (n + 1), st });
        (*made)++;
    }
    free(todo);
    return ok;
}

long av_words_scan(av_arena *a, uint32_t t) {
    if (!a->word_suc) return 0;
    nmap seen = { 0 }, memo = { 0 };
    long made = 0;
    bool ok = scan(a, t, &seen, &memo, &made);
    for (uint32_t g = 0; ok && g < a->nglobals; g++)
        ok = scan(a, a->tmpl_globals[g], &seen, &memo, &made);
    nmap_free(&seen);
    nmap_free(&memo);
    return ok ? made : -1;
}

/*  Each template instruction applying a constant SUC: an instance builds a
 *  word there when the argument is a numeral already. */
bool av_words_mark(av_arena *a) {
    if (!a->word_suc) return true;
    nmap memo = { 0 };
    bool ok = true;
    for (uint32_t ti = 0; ok && ti < a->ntmpls; ti++) {
        av_tmpl *T = &a->tmpls[ti];
        free(T->sucop);
        T->sucop = NULL;
        T->nsuc = 0;
        for (uint32_t i = 0; i < T->nops; i++) {
            uint32_t l = T->ops[2 * i];
            if (l >> 30 != TMPL_CONST ||
                !is_suc(a, a->tmpl_globals[T->consts[l & AV_PAYLOAD]], &memo))
                continue;
            if (!T->sucop && !(T->sucop = calloc(T->nops, 1))) { ok = false; break; }
            T->sucop[i] = 1;
            T->nsuc++;
        }
    }
    nmap_free(&memo);
    return ok;
}

/*  ----------------------------------------------------------- admission */

/*  A fresh copy of t's tree, sharing leaves: what a share-mode run may
 *  write without touching t. */
static uint32_t copy_tree(av_arena *a, uint32_t t) {
    nmap m = { 0 };
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 64, top = 0;
    item *todo = malloc(cap * sizeof *todo);
    uint32_t result = AV_NONE;
    if (!todo) return AV_NONE;
    todo[top++] = (item){ t, false };
    while (top) {
        item it = todo[--top];
        uint32_t x = av_view(a, it.node);
        uint64_t v;
        if (!it.done && nmap_get(&m, x, &v)) continue;
        uint32_t built;
        if (av_tag(a, x) == AV_LEAF) {
            built = x;
        } else if (!it.done) {
            if (top + 3 > cap) {
                item *q = realloc(todo, (cap *= 2) * sizeof *q);
                if (!q) goto done;
                todo = q;
            }
            todo[top++] = (item){ x, true };
            todo[top++] = (item){ av_right(a, x), false };
            todo[top++] = (item){ av_left(a, x), false };
            continue;
        } else {
            uint64_t l, r;
            nmap_get(&m, av_view(a, av_left(a, x)), &l);
            nmap_get(&m, av_view(a, av_right(a, x)), &r);
            built = av_app(a, (uint32_t)l, (uint32_t)r);
        }
        if (built == AV_NONE || !nmap_put(&m, x, built)) goto done;
        if (x == av_view(a, t)) result = built;
    }
done:
    free(todo);
    nmap_free(&m);
    return result;
}

/*  The numeral n as a plain term over a fresh SUC. */
static uint32_t plain_numeral(av_arena *a, uint32_t n) {
    uint32_t suc = copy_tree(a, a->word_suc), t = AV_NODE_K;
    for (uint32_t i = 0; suc != AV_NONE && t != AV_NONE && i < n; i++) t = av_app(a, suc, t);
    return suc == AV_NONE ? AV_NONE : t;
}

/*  The numeral operations' terms, skijack's (expand.py's natAdd .. natIfLe,
 *  over its prelude's suc and zero), pinned: a words.tsv row is admitted
 *  only if its term is this one, node for node, so a row cannot bring an
 *  operation of its own; word_admit's test on small numerals runs as well.
 *  Index AV_WOP_ADD .. AV_WOP_IFLE. */
static const char *const PINNED[] = {
    NULL,
    /* add */
        "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (S (K S) (S (K (S"
        " I)) K)))) (S (K (S (K K))) (S (K (S (K (S (K K) (S (K (S I)) K)))))"
        ")))",
    /* sub */
        "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (S (K S) (S (K (S"
        " I)) K)))) (S (K (S (K K))) (S (S (K S) K) (K (S (S I (K K)) (K I)))"
        ")))",
    /* mul */
        "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (K (S (S I (K K))"
        ")))) (S (K (S (K K))) (S (S (K S) (S (K K) (S (K (S I I)) (S (S (K S"
        ") K) (K (S I I))) (S (K (S (S (K S) (S (K (S I)) K)))) (S (K (S (K K"
        "))) (S (K (S (K (S (K K) (S (K (S I)) K))))))))))))))",
    /* ifeq */
        "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (S (K S) (S (K (S"
        " (K S))) (S (K (S (K (S (K S))))) (S (S (K S) (S (K K) (S (K S) (S ("
        "K K) (S (K S) K))))) (K (S (S (K S) (S (K (S (K S))) (S (K K)))) (K "
        "(K K)))))))))) (S (K K) (S (K (S (S (K S) (S (K K) (S (K S) (S (K (S"
        " (K S))) (S (K K)))))))) (S (K K) (S (S (K S) (S (K (S (K S))) (S (K"
        " (S (K K))) (S (K (S (K S))) (S (K (S (K (S (K S))))) (S (S (K S) (S"
        " (K K) (S (K S) (S (K S))))) (K (S (K K) K)))))))) (K (K (S (K K) K)"
        ")))))))",
    /* ifle */
        "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (S (K S) (S (K K)"
        " (S (K S) (S (K (S (K S))) (S (K K)))))))) (S (K K) (S (K (S (S (K S"
        ") (S (K K) (S (K S) (S (K (S (K S))) (S (K K)))))))) (S (K K) (S (S "
        "(K S) (S (K (S (K S))) (S (K (S (K K))) (S (K (S (K S))) (S (K (S (K"
        " (S (K S))))) (S (S (K S) (S (K K) (S (K S) (S (K S))))) (K (S (K K)"
        " K)))))))) (K (K (S (K K) K))))))))",
};

const char *av_word_pinned(unsigned op) {
    return op >= 1 && op < sizeof PINNED / sizeof *PINNED ? PINNED[op] : NULL;
}

#define ADMIT_MAX 5u        /* operands 0 .. ADMIT_MAX, each against each */

bool word_admit(av_arena *a, uint32_t term, unsigned op) {
    if (!a->word_suc || !jet_marks(a)) return false;
    av_opts o = av_opts_default();
    o.no_collect = true;                    /* the caller's indices hold */
    o.jets = false;
    o.max_steps = 10000000;
    for (uint32_t x = 0; x <= ADMIT_MAX; x++) {
        for (uint32_t y = 0; y <= ADMIT_MAX; y++) {
            uint32_t f = copy_tree(a, term), mx = plain_numeral(a, x), my = plain_numeral(a, y);
            if (f == AV_NONE || mx == AV_NONE || my == AV_NONE) return false;
            uint32_t t = av_app(a, f, mx);
            t = t == AV_NONE ? t : av_app(a, t, my);
            if (t == AV_NONE) return false;
            if (op == AV_WOP_IFEQ || op == AV_WOP_IFLE) {
                bool yes = op == AV_WOP_IFEQ ? x == y : x <= y;
                t = av_app(a, t, a->jet_mark[0]);
                t = t == AV_NONE ? t : av_app(a, t, a->jet_mark[1]);
                if (t == AV_NONE) return false;
                o.whnf_only = true;
                av_result r = av_reduce(a, t, &o);
                if (r.status != AV_WHNF ||
                    av_res(a, r.term) != a->jet_mark[yes ? 0 : 1])
                    return false;
                continue;
            }
            uint32_t want = op == AV_WOP_ADD ? x + y
                          : op == AV_WOP_SUB ? (x > y ? x - y : 0)
                          : op == AV_WOP_MUL ? x * y : UINT32_MAX;
            if (want == UINT32_MAX) return false;
            uint32_t e = plain_numeral(a, want);
            if (e == AV_NONE) return false;
            o.whnf_only = false;
            av_result r = av_reduce(a, t, &o);
            av_result re = av_reduce(a, e, &o);
            if (r.status != AV_NORMAL || re.status != AV_NORMAL ||
                av_equal(a, r.term, re.term, 1000000) != 1)
                return false;
        }
    }
    return true;
}
