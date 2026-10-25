/**  words.c
 *
 *  Words: Scott numerals held as numbers.  W n, for n >= 1, is a jet node
 *  flagged AV_JET_WORD whose id field holds n and whose term is
 *  SUC (W (n-1)), W 0 being K.  A reader sees the numeral through av_view,
 *  node for node, and the predecessor is the term's right child.  SUC is
 *  skijack's successor, \n z s. s n, the constructor term every
 *  `Zero | Suc t` type compiles to, so a numeral is recognized by its
 *  term, whatever the program calls its type.
 *
 *  Words come from three places, and none forces anything: closed
 *  numerals in the loaded program (av_words_scan), a template instance
 *  applying SUC to a numeral already held (tmpl_instance, the operations
 *  av_words_mark finds), and the numeral operations, which fire only on
 *  words (reduce.c).  An operation is skijack's term for it, found by its
 *  hash; word_admit runs that term on small numerals before the native
 *  code may stand in for it.
 *
 *  List words are the same for Scott lists.  L n, for n >= 1, is a word
 *  flagged AV_JET_LIST too, whose id field holds n and whose term is
 *  CONS x (L (n-1)), L 0 being K.  CONS is skijack's cons, \h t n c. c h
 *  t, the constructor term of every list type's second constructor, so a
 *  list is recognized by its term.  They come from closed lists in the
 *  loaded program (av_words_scan) and from the list operations, which fire
 *  only on lists held (reduce.c); a list a run builds cell by cell is its
 *  term.
 */

#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "jets.h"

static const char SUC_TEXT[] = "S (K K) (S (K (S I)) K)";
static const char CONS_TEXT[] = "S (K (S (K K))) (S (S (K S) (S (K K) (S (K S) (S (K (S I)) K)))) (K K))";

void av_fix_on(av_arena *a) {
    a->fix_on = true;
}

bool av_words_on(av_arena *a) {
    if (a->word_suc) return true;
    av_parse_error pe;
    uint32_t t = av_parse(a, SUC_TEXT, sizeof SUC_TEXT - 1, &pe);
    if (t == AV_NONE) return false;
    uint32_t c = av_parse(a, CONS_TEXT, sizeof CONS_TEXT - 1, &pe);
    if (c == AV_NONE) return false;
    a->word_suc = t;
    a->word_cons = c;
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

uint32_t list_cell(av_arena *a, uint32_t x, uint32_t rest) {
    uint32_t n;
    rest = av_res(a, rest);
    if (!a->word_cons || !av_list(a, rest, &n) || n >= AV_WORD_MAX) return AV_NONE;
    uint32_t t = arena_app_reserved(a, arena_app_reserved(a, a->word_cons, x), rest);
    uint32_t w = arena_app_reserved(a, t, t);
    arena_set(a, w, (av_node){ (AV_JET << AV_TAG_SHIFT) | AV_JET_WORD | AV_JET_LIST | (n + 1), t });
    return w;
}

/*  Whether x denotes the term c (SUC or CONS): compared as trees, x seen
 *  through its wrappers.  A memo serves one c. */
static bool is_term(const av_arena *a, uint32_t x, uint32_t c, nmap *memo) {
    uint32_t v = av_view(a, x);
    uint64_t got;
    if (nmap_get(memo, v, &got)) return got != 0;
    bool yes = av_tag(a, v) == AV_APP && av_equal(a, v, c, 64) == 1;
    nmap_put(memo, v, yes);
    return yes;
}
static bool is_suc(const av_arena *a, uint32_t x, nmap *memo) {
    return is_term(a, x, a->word_suc, memo);
}

/*  ------------------------------------------------------------ the scan */

/*  Every closed numeral and list below t, children first: an application
 *  of SUC to K or to a word becomes a word, and of CONS to an element and
 *  then to K or a list word a list word, in place, so each parent keeps
 *  it. */
static bool scan(av_arena *a, uint32_t t, nmap *seen, nmap *memo, nmap *cmemo, long *made,
                 long *lists) {
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
        if (av_numeral(a, pred, &n) && n < AV_WORD_MAX && is_suc(a, av_left(a, x), memo)) {
            uint32_t st = av_app(a, a->word_suc, pred);
            if (st == AV_NONE) { ok = false; break; }
            arena_set(a, x, (av_node){ (AV_JET << AV_TAG_SHIFT) | AV_JET_WORD | (n + 1), st });
            (*made)++;
            continue;
        }
        uint32_t ch = av_res(a, av_left(a, x));
        if (!av_list(a, pred, &n) || n >= AV_WORD_MAX || av_tag(a, ch) != AV_APP ||
            !is_term(a, av_left(a, ch), a->word_cons, cmemo))
            continue;
        uint32_t c1 = av_app(a, a->word_cons, av_right(a, ch));
        uint32_t st = c1 == AV_NONE ? AV_NONE : av_app(a, c1, pred);
        if (st == AV_NONE) { ok = false; break; }
        arena_set(a, x, (av_node){ (AV_JET << AV_TAG_SHIFT) | AV_JET_WORD | AV_JET_LIST | (n + 1), st });
        (*made)++;
        (*lists)++;
    }
    free(todo);
    return ok;
}

long av_words_scan(av_arena *a, uint32_t t, long *lists) {
    long nl = 0;
    if (lists) *lists = 0;
    if (!a->word_suc) return 0;
    nmap seen = { 0 }, memo = { 0 }, cmemo = { 0 };
    long made = 0;
    bool ok = scan(a, t, &seen, &memo, &cmemo, &made, &nl);
    for (uint32_t g = 0; ok && g < a->nglobals; g++)
        ok = scan(a, a->tmpl_globals[g], &seen, &memo, &cmemo, &made, &nl);
    if (lists) *lists = nl;
    nmap_free(&seen);
    nmap_free(&memo);
    nmap_free(&cmemo);
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
 *  natDiv and natRem, over its prelude's suc and zero), pinned: a words.tsv
 *  row is admitted only if its term is this one, node for node, so a row
 *  cannot bring an operation of its own; word_admit's test on small
 *  numerals runs as well.  Then the list operations, skijack's listLength
 *  .. listDrop (expand.py, over its prelude's nil and cons), on small
 *  lists.  Index AV_WOP_ADD .. AV_WOP_DROP. */
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
    /* div */
        "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (K (S (S I (K K))"
        ")))) (S (K (S (K (S (K K))))) (S (S (K S) (S (K (S (K S))) (S (K (S "
        "(S (K S) (S (K (S (S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K ("
        "S (S (K S) (S (K K) (S (K S) (S (K (S (K S))) (S (K K)))))))) (S (K "
        "K) (S (K (S (S (K S) (S (K K) (S (K S) (S (K (S (K S))) (S (K K)))))"
        "))) (S (K K) (S (S (K S) (S (K (S (K S))) (S (K (S (K K))) (S (K (S "
        "(K S))) (S (K (S (K (S (K S))))) (S (S (K S) (S (K K) (S (K S) (S (K"
        " S))))) (K (S (K K) K)))))))) (K (K (S (K K) K))))))))))) K)))) (S ("
        "K (S (K (S (K (S (K K) (S (K (S I)) K))))))) (S (S (K S) (S (K (S (K"
        " S))) (S (S (K S) (S (K K) (S (K S) K))) (K (S (K (S I I)) (S (S (K "
        "S) K) (K (S I I))) (S (K (S (S (K S) (S (K (S I)) K)))) (S (K (S (K "
        "K))) (S (S (K S) K) (K (S (S I (K K)) (K I))))))))))) (K (K I)))))))"
        " (K (K (K K))))))",
    /* rem */
        "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (S (K S) (S (K (S"
        " I)) K)))) (S (K (S (K (S (K K))))) (S (S (K S) (S (K (S (K S))) (S "
        "(K (S (S (K S) (S (K (S (S (K (S I I)) (S (S (K S) K) (K (S I I))) ("
        "S (K (S (S (K S) (S (K K) (S (K S) (S (K (S (K S))) (S (K K)))))))) "
        "(S (K K) (S (K (S (S (K S) (S (K K) (S (K S) (S (K (S (K S))) (S (K "
        "K)))))))) (S (K K) (S (S (K S) (S (K (S (K S))) (S (K (S (K K))) (S "
        "(K (S (K S))) (S (K (S (K (S (K S))))) (S (S (K S) (S (K K) (S (K S)"
        " (S (K S))))) (K (S (K K) K)))))))) (K (K (S (K K) K))))))))))) K)))"
        ") (S (S (K S) (S (K (S (K S))) (S (S (K S) (S (K K) (S (K S) K))) (K"
        " (S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (S (K S) (S (K "
        "(S I)) K)))) (S (K (S (K K))) (S (S (K S) K) (K (S (S I (K K)) (K I)"
        ")))))))))) (K (K I)))))) (K K))))",
    /* len */
        "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (S I (K K)))) (S (K"
        " K) (S (K K) (S (K (S (K K) (S (K (S I)) K)))))))",
    /* at */
        "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (S (K S) (S (K K) S"
        ")))) (S (K K) (S (K (S (S (K S) (S (K K) (S (K S) (S (K (S (K S))) (S "
        "(K K)))))))) (S (K K) (S (K (S (K K))) (S (S (K S) (S (K K) (S (K S) ("
        "S (S (K S) (S (K (S (K S))) (S (K (S (K K))) (S (K S))))) (K (K K)))))"
        ") (K K)))))))",
    /* app */
        "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S S)) (S (K K) (S (K "
        "(S (K (S (S (K S) (S (K K) (S (K (S (K K))) (S (S (K S) (S (K K) (S (K"
        " S) (S (K (S I)) K)))) (K K))))))))) (S (K (S (K K))) (S (S (K S) (S ("
        "K K) S)) (K K))))))",
    /* take */
        "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (K (S (S I (K K))))"
        ")) (S (K (S (K K))) (S (K (S (S (K S) (S (K K) (S I (K K)))))) (S (K K"
        ") (S (K (S (K (S (S (K S) (S (K K) (S (K (S (K K))) (S (S (K S) (S (K "
        "K) (S (K S) (S (K (S I)) K)))) (K K))))))))) (S (K (S (K K))) (S (S (K"
        " S) (S (K K) S)) (K K))))))))",
    /* drop */
        "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (S (K S) (S (K (S I"
        ")) K)))) (S (K (S (K K))) (S (K (S (S (K S) (S (K K) (S I (K K)))))) ("
        "S (K K) (S (K (S (K K))) (S (S (K S) (S (K K) S)) (K K)))))))",
};

const char *av_word_pinned(unsigned op) {
    return op >= 1 && op < sizeof PINNED / sizeof *PINNED ? PINNED[op] : NULL;
}

#define ADMIT_MAX 5u        /* operands 0 .. ADMIT_MAX, each against each */

/*  The list of the numerals xs[0 .. n-1] as a plain term over a fresh CONS. */
static uint32_t plain_list(av_arena *a, const uint32_t *xs, unsigned n) {
    uint32_t cons = copy_tree(a, a->word_cons), t = AV_NODE_K;
    for (unsigned i = n; cons != AV_NONE && t != AV_NONE && i-- > 0;) {
        uint32_t x = plain_numeral(a, xs[i]);
        uint32_t c = x == AV_NONE ? AV_NONE : av_app(a, cons, x);
        t = c == AV_NONE ? AV_NONE : av_app(a, c, t);
    }
    return cons == AV_NONE ? AV_NONE : t;
}

/*  Whether t and the plain want have one normal form. */
static bool same_normal(av_arena *a, uint32_t t, uint32_t want, const av_opts *o) {
    if (t == AV_NONE || want == AV_NONE) return false;
    av_result r = av_reduce(a, t, o), re = av_reduce(a, want, o);
    return r.status == AV_NORMAL && re.status == AV_NORMAL &&
           av_equal(a, r.term, re.term, 1000000) == 1;
}

/*  The small lists a list operation's term is run on, and the index past
 *  every one's end, and at's default. */
static const uint32_t ADMIT_LISTS[4][3] = { { 0 }, { 1 }, { 2, 0 }, { 0, 3, 1 } };
static const unsigned ADMIT_LENS[4] = { 0, 1, 2, 3 };
#define ADMIT_INDEX 4u
#define ADMIT_DEFAULT 7u

static bool list_admit(av_arena *a, uint32_t term, unsigned op) {
    av_opts o = av_opts_default();
    o.no_collect = true;
    o.jets = false;
    o.max_steps = 10000000;
    for (unsigned i = 0; i < 4; i++) {
        const uint32_t *xs = ADMIT_LISTS[i];
        unsigned n = ADMIT_LENS[i];
        for (unsigned j = 0; j < (op == AV_WOP_APP ? 4u : op == AV_WOP_LEN ? 1u : ADMIT_INDEX + 1); j++) {
            uint32_t f = copy_tree(a, term), l = plain_list(a, xs, n);
            if (f == AV_NONE || l == AV_NONE) return false;
            uint32_t t = av_app(a, f, l), want = AV_NONE;
            if (t == AV_NONE) return false;
            if (op == AV_WOP_LEN) {
                want = plain_numeral(a, n);
            } else if (op == AV_WOP_APP) {
                uint32_t both[6];
                for (unsigned q = 0; q < n; q++) both[q] = xs[q];
                for (unsigned q = 0; q < ADMIT_LENS[j]; q++) both[n + q] = ADMIT_LISTS[j][q];
                t = av_app(a, t, plain_list(a, ADMIT_LISTS[j], ADMIT_LENS[j]));
                want = plain_list(a, both, n + ADMIT_LENS[j]);
            } else {
                unsigned k = j, m = k < n ? k : n;
                uint32_t kn = plain_numeral(a, k);
                t = t == AV_NONE || kn == AV_NONE ? AV_NONE : av_app(a, t, kn);
                if (op == AV_WOP_AT) {
                    uint32_t d = plain_numeral(a, ADMIT_DEFAULT);
                    t = t == AV_NONE || d == AV_NONE ? AV_NONE : av_app(a, t, d);
                    want = plain_numeral(a, k < n ? xs[k] : ADMIT_DEFAULT);
                } else if (op == AV_WOP_TAKE) {
                    want = plain_list(a, xs, m);
                } else if (op == AV_WOP_DROP) {
                    want = plain_list(a, xs + m, n - m);
                } else {
                    return false;
                }
            }
            if (!same_normal(a, t, want, &o)) return false;
        }
    }
    return true;
}

bool word_admit(av_arena *a, uint32_t term, unsigned op) {
    if (av_wop_list(op)) return a->word_cons && jet_marks(a) && list_admit(a, term, op);
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
                          : op == AV_WOP_MUL ? x * y
                          : op == AV_WOP_DIV ? (y ? x / y : 0)
                          : op == AV_WOP_REM ? (y ? x % y : x) : UINT32_MAX;
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
