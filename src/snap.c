/**  snap.c
 *
 *  Arena snapshots (docs/DESIGN.md §4.2, §19).  The image keeps sharing
 *  and indirections, which the bitstring cannot.  Its layout:
 *
 *      "AVIM"  u8 version = 1  u8[3] zero
 *      u32 node count  u32 leaf count
 *      for each atom leaf (ids 3 ..): u32 length and its bytes
 *      node count x (u32 l, u32 r)
 *
 *  and the sidecar PATH.sum, written last:
 *
 *      "AVSM"  u8 version = 1  u8[3] zero
 *      u32 root  u32 node count  32-byte SHA-256 of (image, root, count)
 *
 *  Integers are little-endian.  A snapshot is not a proof witness (§17.1).
 */

#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "avon.h"
#include "durable.h"
#include "jets.h"

/*  -------------------------------------------------------------- writing */

typedef struct { av_buf b; bool ok; } out;

static void put(out *o, const void *p, size_t n) {
    if (!o->ok) return;
    av_buf *b = &o->b;
    if (b->len + n > b->cap) {
        size_t cap = b->cap ? b->cap : 4096;
        while (b->len + n > cap) cap *= 2;
        char *s = realloc(b->s, cap);
        if (!s) { o->ok = false; return; }
        b->s = s;
        b->cap = cap;
    }
    memcpy(b->s + b->len, p, n);
    b->len += n;
}

static void put32(out *o, uint32_t v) {
    uint8_t x[4] = { (uint8_t)v, (uint8_t)(v >> 8), (uint8_t)(v >> 16),
                     (uint8_t)(v >> 24) };
    put(o, x, 4);
}

/* Write a whole file durably: a temporary, synced, renamed over path, and
 * the directory synced, which must succeed (av_sync_fd, durable.h). */
static bool write_durably(const char *path, const void *p, size_t n) {
    size_t len = strlen(path);
    char *tmp = malloc(len + 5);
    if (!tmp) return false;
    memcpy(tmp, path, len);
    memcpy(tmp + len, ".tmp", 5);
    int fd = open(tmp, O_WRONLY | O_CREAT | O_TRUNC, 0600);
    bool ok = fd >= 0;
    const char *c = p;
    while (ok && n) {
        ssize_t w = write(fd, c, n);
        if (w < 0 && errno == EINTR) continue;
        if (w <= 0) ok = false;
        else { c += w; n -= (size_t)w; }
    }
    if (fd >= 0) {
        if (ok && !av_sync_fd(fd)) ok = false;
        if (close(fd) != 0) ok = false;
    }
    if (ok && rename(tmp, path) != 0) ok = false;
    if (!ok) unlink(tmp);
    free(tmp);

    /* the rename itself must reach the disk before the sidecar does */
    return ok && av_sync_parent(path);
}

static void checksum(const av_buf *image, uint32_t root, uint32_t used,
                     uint8_t sum[32]) {
    av_sha256_ctx s;
    uint8_t tail[8] = { (uint8_t)root, (uint8_t)(root >> 8),
                        (uint8_t)(root >> 16), (uint8_t)(root >> 24),
                        (uint8_t)used, (uint8_t)(used >> 8),
                        (uint8_t)(used >> 16), (uint8_t)(used >> 24) };
    av_sha256_init(&s);
    av_sha256_update(&s, image->s, image->len);
    av_sha256_update(&s, tail, 8);
    av_sha256_final(&s, sum);
}

static char *sum_path(const char *path) {
    size_t len = strlen(path);
    char *s = malloc(len + 5);
    if (s) {
        memcpy(s, path, len);
        memcpy(s + len, ".sum", 5);
    }
    return s;
}

/*  Copy the graph below root into a fresh arena: sharing kept, indirections
 *  resolved, jet nodes seen through, and nothing else -- not the caller's
 *  other terms, not the dashboard (§19: never persisted).  A marker leaf
 *  in the graph is refused. */
static av_arena *copy_out(const av_arena *a, uint32_t root, uint32_t *broot,
                          const char **msg) {
    av_arena *b = av_arena_new(64);
    nmap m = { 0 };
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 256, top = 0;
    item *todo = malloc(cap * sizeof *todo);
    *msg = NULL;
    if (!b || !todo) { *msg = "out of memory"; goto done; }
    b->allow_bird_atoms = true;             /* names already in an arena */
    todo[top++] = (item){ av_view(a, root), false };
    while (top) {
        item it = todo[--top];
        uint64_t v;
        if (!it.done && nmap_get(&m, it.node, &v)) continue;
        uint32_t built;
        if (av_tag(a, it.node) == AV_LEAF) {
            const char *nm = av_leaf_name(a, av_right(a, it.node));
            if (nm[0] == '@') { *msg = "the term carries a probe marker"; goto done; }
            built = av_leaf(b, nm, strlen(nm));
        } else if (!it.done) {
            if (top + 3 > cap) {
                item *q = realloc(todo, (cap *= 2) * sizeof *q);
                if (!q) { *msg = "out of memory"; goto done; }
                todo = q;
            }
            todo[top++] = (item){ it.node, true };
            todo[top++] = (item){ av_view(a, av_right(a, it.node)), false };
            todo[top++] = (item){ av_view(a, av_left(a, it.node)), false };
            continue;
        } else {
            uint64_t l, r;
            nmap_get(&m, av_view(a, av_left(a, it.node)), &l);
            nmap_get(&m, av_view(a, av_right(a, it.node)), &r);
            built = av_app(b, (uint32_t)l, (uint32_t)r);
        }
        if (built == AV_NONE || !nmap_put(&m, it.node, built)) {
            *msg = "out of memory";
            goto done;
        }
    }
    {
        uint64_t r;
        if (!nmap_get(&m, av_view(a, root), &r)) *msg = "out of memory";
        else *broot = (uint32_t)r;
    }
done:
    free(todo);
    nmap_free(&m);
    if (*msg) { av_arena_free(b); return NULL; }
    return b;
}

bool av_snapshot_save(const av_arena *live, uint32_t root, const char *path,
                      const char **err) {
    const char *why = NULL;
    uint32_t r0;
    av_arena *a = copy_out(live, root, &r0, &why);
    if (!a) { if (err) *err = why; return false; }
    uint32_t *broot = &r0;

    out img = { { 0 }, true };
    put(&img, "AVIM\x01\0\0\0", 8);
    put32(&img, a->used);
    put32(&img, a->n_leaves);
    for (uint32_t id = SKI_ATOM_FIRST; id < a->n_leaves; id++) {
        const char *nm = a->atom_name[id];
        uint32_t len = (uint32_t)strlen(nm);
        put32(&img, len);
        put(&img, nm, len);
    }
    for (uint32_t i = 0; i < a->used; i++) {
        put32(&img, a->nodes[i].l);         /* a copy: no jets, no indirections */
        put32(&img, a->nodes[i].r);
    }

    out side = { { 0 }, true };
    uint8_t sum[32];
    put(&side, "AVSM\x01\0\0\0", 8);
    put32(&side, *broot);
    put32(&side, a->used);
    if (img.ok) checksum(&img.b, *broot, a->used, sum);
    put(&side, sum, 32);

    char *sp = sum_path(path);
    bool ok = img.ok && side.ok && sp &&
              write_durably(path, img.b.s, img.b.len) &&      /* data first */
              write_durably(sp, side.b.s, side.b.len);        /* sidecar last */
    if (!ok && err) *err = "could not write snapshot";
    free(sp);
    av_buf_free(&img.b);
    av_buf_free(&side.b);
    av_arena_free(a);
    return ok;
}

/*  -------------------------------------------------------------- reading */

static uint8_t *slurp(const char *path, size_t *n) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    size_t cap = 1 << 16, len = 0;
    uint8_t *p = malloc(cap);
    while (p) {
        len += fread(p + len, 1, cap - len, f);
        if (len < cap) break;
        uint8_t *q = realloc(p, cap *= 2);
        if (!q) { free(p); p = NULL; }
        else p = q;
    }
    fclose(f);
    *n = len;
    return p;
}

static uint32_t get32(const uint8_t *p) {
    return (uint32_t)p[0] | (uint32_t)p[1] << 8 | (uint32_t)p[2] << 16 |
           (uint32_t)p[3] << 24;
}

/* A leaf named like a probe or jet marker ("@..."): an image may hold one,
 * since an arena that has probed or loaded jets interns them, but no node
 * may point at one, so no term in an image carries a marker. */
static bool reserved(const av_arena *a, uint32_t i) {
    if (a->nodes[i].l >> AV_TAG_SHIFT != AV_LEAF) return false;
    uint32_t id = a->nodes[i].r;
    return id >= SKI_ATOM_FIRST && id < a->n_leaves && a->atom_name[id][0] == '@';
}

/* Every node well formed, every leaf interned once, no term carrying a
 * marker, and no cycle. */
static const char *verify(const av_arena *a, uint32_t root) {
    uint32_t n = a->used;
    if (reserved(a, root)) return "the root is a probe marker";
    for (uint32_t i = 0; i < n; i++) {
        av_node x = a->nodes[i];
        switch (x.l >> AV_TAG_SHIFT) {
        case AV_APP:
            if ((x.l & AV_PAYLOAD) >= n || x.r >= n) return "index out of range";
            if (reserved(a, x.l & AV_PAYLOAD) || reserved(a, x.r))
                return "a term carries a probe marker";
            break;
        case AV_IND:
            if ((x.l & AV_PAYLOAD) >= n || x.r) return "malformed indirection";
            if (reserved(a, x.l & AV_PAYLOAD)) return "a term carries a probe marker";
            break;
        case AV_LEAF:
            if ((x.l & AV_PAYLOAD) || x.r >= a->n_leaves) return "malformed leaf";
            if (a->atom_node[x.r] != i) return "leaf not interned";
            break;
        default:
            return "jet node in image";
        }
    }

    /* acyclic: iterative depth-first search, three colours */
    uint8_t *colour = calloc(n, 1);
    uint32_t *stk = malloc((size_t)n * 2 * sizeof *stk + sizeof *stk);
    const char *msg = NULL;
    if (!colour || !stk) { msg = "out of memory"; goto done; }
    for (uint32_t s = 0; s < n && !msg; s++) {
        if (colour[s]) continue;
        size_t top = 0;
        stk[top++] = s;
        while (top && !msg) {
            uint32_t i = stk[top - 1];
            if (colour[i] == 0) {
                colour[i] = 1;                     /* on the path */
                av_node x = a->nodes[i];
                uint32_t tag = x.l >> AV_TAG_SHIFT;
                uint32_t kids[2], nk = 0;
                if (tag == AV_APP) { kids[nk++] = x.l & AV_PAYLOAD; kids[nk++] = x.r; }
                if (tag == AV_IND) kids[nk++] = x.l & AV_PAYLOAD;
                for (uint32_t k = 0; k < nk; k++) {
                    if (colour[kids[k]] == 1) { msg = "cycle in image"; break; }
                    if (colour[kids[k]] == 0) stk[top++] = kids[k];
                }
            } else {
                colour[i] = 2;                     /* finished */
                top--;
            }
        }
    }
done:
    free(colour);
    free(stk);
    return msg;
}

av_arena *av_snapshot_load(const char *path, uint32_t *root, const char **err) {
    const char *msg = NULL;
    size_t n = 0, ns = 0;
    char *sp = sum_path(path);
    uint8_t *side = sp ? slurp(sp, &ns) : NULL;
    uint8_t *img = side ? slurp(path, &n) : NULL;
    av_arena *a = NULL;
    free(sp);

    if (!side) { msg = "missing sidecar"; goto done; }
    if (!img) { msg = "missing image"; goto done; }
    if (ns != 48 || memcmp(side, "AVSM\x01\0\0\0", 8) != 0) {
        msg = "malformed sidecar";
        goto done;
    }
    uint32_t r = get32(side + 8), used = get32(side + 12);
    av_buf view = { (char *)img, n, n };
    uint8_t sum[32];
    checksum(&view, r, used, sum);
    if (memcmp(sum, side + 16, 32) != 0) { msg = "checksum mismatch"; goto done; }

    /* the checksum holds; now the structure */
    if (n < 16 || memcmp(img, "AVIM\x01\0\0\0", 8) != 0) { msg = "malformed image"; goto done; }
    if (get32(img + 8) != used) { msg = "node count disagrees with sidecar"; goto done; }
    if (used < SKI_ATOM_FIRST || used > AV_MAX_NODES) { msg = "bad node count"; goto done; }
    if (r >= used) { msg = "root at or beyond the node count"; goto done; }
    uint32_t leaves = get32(img + 12);
    if (leaves < SKI_ATOM_FIRST || leaves > used) { msg = "bad leaf count"; goto done; }

    a = av_arena_new(used < 64 ? 64 : used);
    if (!a) { msg = "out of memory"; goto done; }
    size_t pos = 16;
    for (uint32_t id = SKI_ATOM_FIRST; id < leaves; id++) {
        if (n - pos < 4) { msg = "truncated atom table"; goto done; }
        uint32_t len = get32(img + pos);
        pos += 4;
        if (len == 0 || len > n - pos) { msg = "truncated atom table"; goto done; }
        const char *nm = (const char *)img + pos;
        if (memchr(nm, 0, len)) { msg = "NUL in atom name"; goto done; }
        if (!a->allow_bird_atoms && av_is_bird(nm, len)) {
            msg = "atom named like a live aviary combinator (§4.3)";
            goto done;
        }
        if (av_leaf(a, nm, len) == AV_NONE) { msg = "out of memory"; goto done; }
        if (a->n_leaves != id + 1) { msg = "duplicate atom name"; goto done; }
        pos += len;
    }
    if ((n - pos) / 8 != used || (n - pos) % 8) { msg = "node array size wrong"; goto done; }

    /* The image's own nodes replace the leaves av_leaf allocated; the
     * leaves' positions come from the image. */
    for (uint32_t i = 0; i < used; i++) {
        a->nodes[i].l = get32(img + pos + 8 * (size_t)i);
        a->nodes[i].r = get32(img + pos + 8 * (size_t)i + 4);
    }
    a->used = used;
    for (uint32_t id = 0; id < leaves; id++) a->atom_node[id] = AV_NONE;
    for (uint32_t i = 0; i < used; i++)
        if (a->nodes[i].l >> AV_TAG_SHIFT == AV_LEAF && a->nodes[i].r < leaves) {
            if (a->atom_node[a->nodes[i].r] != AV_NONE) { msg = "leaf not interned"; goto done; }
            a->atom_node[a->nodes[i].r] = i;
        }
    for (uint32_t id = 0; id < leaves; id++)
        if (a->atom_node[id] == AV_NONE) { msg = "leaf missing"; goto done; }
    if (a->atom_node[SKI_S] != AV_NODE_S || a->atom_node[SKI_K] != AV_NODE_K ||
        a->atom_node[SKI_I] != AV_NODE_I) {
        msg = "S, K, I not at 0, 1, 2";
        goto done;
    }
    msg = verify(a, r);
    if (!msg) *root = r;

done:
    free(side);
    free(img);
    if (msg) {
        av_arena_free(a);
        if (err) *err = msg;
        return NULL;
    }
    return a;
}
