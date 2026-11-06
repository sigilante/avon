/**  pin.c
 *
 *  Pinned jets: a jet whose term is fixed by its full digest, so that a
 *  native rewrite stands for exactly the term a proof licenses.  Poseidon2's
 *  P (p2.c) and the transported Nock decrement (nockdec.c) are two.  Here
 *  is what they share: the digest, the registration, the bind that keeps a
 *  jet node only where its term is the pinned one, node for node, and the
 *  comparison a fire repeats; and the pairs both encodings are made of.
 */

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "jets.h"

/*  The full digest: the structural hash with every digest kept whole, 32
 *  bytes, over S, K and I only: an atom's, SHA-256 of its name; an
 *  application's, of "(" + hex(f) + " " + hex(x) + ")".  False on any other
 *  leaf, or out of memory. */
static bool merkle256(const av_arena *a, uint32_t t, uint8_t out[32]) {
    static const char hx[] = "0123456789abcdef";
    nmap at = { 0 };                        /* viewed node -> 1 + its slot */
    uint8_t (*d)[32] = NULL;
    size_t nd = 0, dcap = 0, cap = 256, top = 0;
    typedef struct { uint32_t node; bool done; } item;
    item *todo = malloc(cap * sizeof *todo);
    bool ok = todo != NULL;
    if (ok) todo[top++] = (item){ av_view(a, t), false };
    while (ok && top) {
        item it = todo[--top];
        uint64_t v;
        if (nmap_get(&at, it.node, &v)) continue;
        uint8_t h[32];
        if (av_tag(a, it.node) == AV_LEAF) {
            static const char *const name[3] = { "S", "K", "I" };
            if (it.node > AV_NODE_I) { ok = false; break; }
            av_sha256(name[it.node], 1, h);
        } else {
            uint32_t f = av_view(a, av_left(a, it.node)), x = av_view(a, av_right(a, it.node));
            uint64_t df, dx;
            if (!it.done) {
                if (top + 3 > cap) {
                    item *q = realloc(todo, (cap *= 2) * sizeof *q);
                    if (!q) { ok = false; break; }
                    todo = q;
                }
                todo[top++] = (item){ it.node, true };
                todo[top++] = (item){ x, false };
                todo[top++] = (item){ f, false };
                continue;
            }
            nmap_get(&at, f, &df);
            nmap_get(&at, x, &dx);
            char text[131];
            text[0] = '(';
            text[65] = ' ';
            text[130] = ')';
            for (int k = 0; k < 32; k++) {
                text[1 + 2 * k] = hx[d[df - 1][k] >> 4];
                text[2 + 2 * k] = hx[d[df - 1][k] & 15];
                text[66 + 2 * k] = hx[d[dx - 1][k] >> 4];
                text[67 + 2 * k] = hx[d[dx - 1][k] & 15];
            }
            av_sha256(text, sizeof text, h);
        }
        if (nd == dcap) {
            size_t c = dcap ? 2 * dcap : 1024;
            uint8_t (*q)[32] = realloc(d, c * sizeof *q);
            if (!q) { ok = false; break; }
            d = q;
            dcap = c;
        }
        memcpy(d[nd++], h, 32);
        if (!nmap_put(&at, it.node, nd)) { ok = false; break; }
    }
    uint64_t r;
    if (ok && nmap_get(&at, av_view(a, t), &r)) memcpy(out, d[r - 1], 32);
    else ok = false;
    free(todo);
    free(d);
    nmap_free(&at);
    return ok;
}

bool av_pin_digest(const av_arena *a, uint32_t t, char out[65]) {
    static const char hx[] = "0123456789abcdef";
    uint8_t h[32];
    if (!merkle256(a, t, h)) return false;
    for (int k = 0; k < 32; k++) {
        out[2 * k] = hx[h[k] >> 4];
        out[2 * k + 1] = hx[h[k] & 15];
    }
    out[64] = '\0';
    return true;
}

/*  A term's distinct nodes, through views: the bound on a comparison with it. */
static uint32_t view_nodes(const av_arena *a, uint32_t t) {
    nmap seen = { 0 };
    size_t cap = 256, top = 0;
    uint32_t *todo = malloc(cap * sizeof *todo), n = 0;
    bool ok = todo != NULL;
    if (ok) todo[top++] = t;
    while (ok && top) {
        uint32_t x = av_view(a, todo[--top]);
        uint64_t v;
        if (nmap_get(&seen, x, &v)) continue;
        if (!(ok = nmap_put(&seen, x, 1))) break;
        n++;
        if (av_tag(a, x) != AV_APP) continue;
        if (top + 2 > cap) {
            uint32_t *q = realloc(todo, (cap *= 2) * sizeof *q);
            if (!(ok = q != NULL)) break;
            todo = q;
        }
        todo[top++] = av_left(a, x);
        todo[top++] = av_right(a, x);
    }
    free(todo);
    nmap_free(&seen);
    return ok ? n : 0;
}

/*  A term's application nodes as a tree, through views, past PIN_TREE_MAX
 *  saturated: a comparison of a tree with it visits at most that many
 *  distinct pairs, as each node of the tree meets one of the term's.
 *  0 out of memory. */
static uint32_t tree_apps(const av_arena *a, uint32_t t) {
    nmap at = { 0 };                        /* viewed node -> 1 + its size */
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 256, top = 0;
    item *todo = malloc(cap * sizeof *todo);
    bool ok = todo != NULL;
    if (ok) todo[top++] = (item){ av_view(a, t), false };
    while (ok && top) {
        item it = todo[--top];
        uint64_t v, dl, dr;
        if (nmap_get(&at, it.node, &v)) continue;
        if (av_tag(a, it.node) != AV_APP) {
            ok = nmap_put(&at, it.node, 1);
            continue;
        }
        uint32_t f = av_view(a, av_left(a, it.node)), x = av_view(a, av_right(a, it.node));
        if (!it.done) {
            if (top + 3 > cap) {
                item *q = realloc(todo, (cap *= 2) * sizeof *q);
                if (!(ok = q != NULL)) break;
                todo = q;
            }
            todo[top++] = (item){ it.node, true };
            todo[top++] = (item){ x, false };
            todo[top++] = (item){ f, false };
            continue;
        }
        nmap_get(&at, f, &dl);
        nmap_get(&at, x, &dr);
        uint64_t n = (dl - 1) + (dr - 1) + 1;
        if (n > PIN_TREE_MAX) n = PIN_TREE_MAX;
        ok = nmap_put(&at, it.node, n + 1);
    }
    uint64_t r = 0;
    if (ok && !nmap_get(&at, av_view(a, t), &r)) ok = false;
    free(todo);
    nmap_free(&at);
    return ok ? (uint32_t)(r - 1 ? r - 1 : 1) : 0;
}

/*  The pairs a comparison with jet id's term may visit: eight a distinct
 *  node of it, as before, or the term's size as a tree, whichever is more,
 *  so that a term loaded as a tree, never hash-consed (a backtick-prefix
 *  input), compares whole. */
static size_t pin_budget(const av_jet *j) {
    size_t b = 8 * (size_t)j->pin_nodes + 4096;
    return j->pin_tree > b ? j->pin_tree : b;
}

bool pin_same(const av_arena *a, uint32_t x, uint32_t id) {
    return av_equal(a, x, a->jets[id].fallback, pin_budget(&a->jets[id]) + 1) == 1;
}

uint32_t pin_register(av_arena *a, uint32_t p, const char *sha256, const char *sha256b,
                      const char *refusal, const char **err) {
    char h[AV_HASH_LEN + 1];
    av_digest d;
    if (!av_structural_hash(a, p, h) || !av_hash_parse(h, &d)) {
        *err = "cannot hash the term";
        return AV_NONE;
    }
    char full[65];
    if (sha256 && (!av_pin_digest(a, p, full) ||
                   (strcmp(full, sha256) != 0 && (!sha256b || strcmp(full, sha256b) != 0)))) {
        *err = refusal;
        return AV_NONE;
    }
    uint32_t nodes = view_nodes(a, p), tree = tree_apps(a, p);
    if (!nodes || !tree) {
        *err = "out of memory";
        return AV_NONE;
    }
    uint32_t before = a->njets;
    uint32_t id = jet_entry_for(a, d, p, err);
    if (id == AV_NONE) return AV_NONE;
    av_jet *j = &a->jets[id];
    if (j->tmpl || j->word_op || j->fix || j->interp >= 0) {
        *err = "the term's digest is already another kind of jet";
        return AV_NONE;
    }
    av_jet probe = { .pin_nodes = nodes, .pin_tree = tree };
    if (id < before && av_equal(a, j->fallback, p, pin_budget(&probe) + 1) != 1) {
        /* an entry under the same digest from elsewhere (a --jets
         * dictionary): its term must be the pinned one, since the fires
         * check against it */
        *err = "another term already holds the term's digest";
        return AV_NONE;
    }
    j->pin_nodes = nodes;
    j->pin_tree = tree;
    return id;
}

long av_pin_bind(av_arena *a, uint32_t t, uint32_t id) {
    nmap seen = { 0 };
    size_t cap = 256, top = 0;
    uint32_t *todo = malloc(cap * sizeof *todo);
    long kept = 0;
    if (!todo) return -1;
    todo[top++] = t;
    while (top) {
        uint32_t x = av_res(a, todo[--top]);
        uint64_t v;
        if (nmap_get(&seen, x, &v)) continue;
        if (!nmap_put(&seen, x, 1)) { kept = -1; break; }
        if (av_tag(a, x) == AV_JET && !(av_left(a, x) & AV_JET_WORD)) {
            uint32_t inner = av_right(a, x);
            if (AV_JET_ID(av_left(a, x)) == id) {
                if (pin_same(a, inner, id)) kept++;
                else arena_set(a, x, (av_node){ (AV_IND << AV_TAG_SHIFT) | inner, 0 });
            }
            x = inner;
        }
        if (av_tag(a, x) != AV_APP) continue;
        if (top + 2 > cap) {
            uint32_t *q = realloc(todo, (cap *= 2) * sizeof *q);
            if (!q) { kept = -1; break; }
            todo = q;
        }
        todo[top++] = av_left(a, x);
        todo[top++] = av_right(a, x);
    }
    free(todo);
    nmap_free(&seen);
    return kept;
}

/*  pairT x y = S (S I (K x)) (K y), seen through indirections and jet
 *  nodes. */
bool pin_pair_read(const av_arena *a, uint32_t t, uint32_t *x, uint32_t *y) {
    t = av_view(a, t);
    if (av_tag(a, t) != AV_APP) return false;
    uint32_t f = av_view(a, av_left(a, t)), ky = av_view(a, av_right(a, t));
    if (av_tag(a, f) != AV_APP || av_tag(a, ky) != AV_APP ||
        av_view(a, av_left(a, f)) != AV_NODE_S || av_view(a, av_left(a, ky)) != AV_NODE_K)
        return false;
    uint32_t g = av_view(a, av_right(a, f));            /* S I (K x) */
    if (av_tag(a, g) != AV_APP) return false;
    uint32_t si = av_view(a, av_left(a, g)), kx = av_view(a, av_right(a, g));
    if (av_tag(a, si) != AV_APP || av_tag(a, kx) != AV_APP ||
        av_view(a, av_left(a, si)) != AV_NODE_S || av_view(a, av_right(a, si)) != AV_NODE_I ||
        av_view(a, av_left(a, kx)) != AV_NODE_K)
        return false;
    *x = av_right(a, kx);
    *y = av_right(a, ky);
    return true;
}

uint32_t pin_pair_build(av_arena *a, uint32_t si, uint32_t x, uint32_t y) {
    uint32_t f = arena_app_reserved(a, AV_NODE_S, arena_app_reserved(a, si,
                                    arena_app_reserved(a, AV_NODE_K, x)));
    return arena_app_reserved(a, f, arena_app_reserved(a, AV_NODE_K, y));
}
