/**  pma.c
 *
 *  The persistent arena (docs/DESIGN.md §19.1).  The node array is the
 *  image file `nodes` -- a header page, then node i at header + 8i --
 *  mapped copy-on-write at the base of a reservation of address space big
 *  enough for every node an arena may hold, so the base never moves and
 *  indices stay positions.  Leaf names live in `atoms`.  Writes change
 *  memory only; a commit carries the changed 4 KiB chunks, the header and
 *  the names to the files through a redo journal:
 *
 *      journal.tmp written, synced; renamed to journal; directory synced;
 *      the records applied to the image; the image synced;
 *      journal removed; directory synced.
 *
 *  A crash before the rename leaves the old image, and journal.tmp is
 *  discarded on open; after it, open applies the journal again, which is
 *  idempotent.  Journal layout: "AVONJNL1", u64 events, u64 nodes file
 *  size, u64 atoms file size, u32 records; per record u8 file (0 nodes,
 *  1 atoms), u64 offset, u32 length, the bytes; then the SHA-256 of all
 *  of it.  Header page: "AVONPMA1", u32 version, u32 header size, u32
 *  nodes, u32 leaves, u32 root, u64 events, u64 atoms size, the atoms'
 *  SHA-256, then the SHA-256 of the fields before it.  Integers little
 *  endian.  Atoms: per leaf id from 3, u32 node, u32 length, the name.
 */

#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include "avon.h"
#include "jets.h"

#define CHUNK       4096u                  /* dirty-tracking granularity */
#define CHUNK_NODES (CHUNK / sizeof(av_node))
#define HDR_FIELDS  (8 + 4 * 5 + 8 * 2 + 32)

int av_pma_crash_at = 0;

struct av_pma {
    char     *dir;
    int       fd;                           /* the nodes file */
    uint8_t  *base;                         /* the reservation; a->nodes */
    size_t    reserve, mapped;              /* bytes */
    size_t    hdr;                          /* header bytes: the page size */
    size_t    file_nodes;                   /* node bytes the file maps */
    uint32_t  committed;                    /* nodes at the last commit */
    uint8_t  *dirty;                        /* a byte per chunk of the mapping */
    size_t    nchunks;
    bool      all_dirty;
    uint8_t   atoms_sha[32];                /* of the atoms last committed */
    uint64_t  last_bytes, last_chunks;
};

static void put32(uint8_t *p, uint32_t v) { for (int i = 0; i < 4; i++) p[i] = (uint8_t)(v >> 8 * i); }
static void put64(uint8_t *p, uint64_t v) { for (int i = 0; i < 8; i++) p[i] = (uint8_t)(v >> 8 * i); }
static uint32_t get32(const uint8_t *p) {
    return (uint32_t)p[0] | (uint32_t)p[1] << 8 | (uint32_t)p[2] << 16 | (uint32_t)p[3] << 24;
}
static uint64_t get64(const uint8_t *p) {
    uint64_t v = 0;
    for (int i = 7; i >= 0; i--) v = v << 8 | p[i];
    return v;
}

static char *path_in(const char *dir, const char *name) {
    size_t n = strlen(dir) + strlen(name) + 2;
    char *p = malloc(n);
    if (p) snprintf(p, n, "%s/%s", dir, name);
    return p;
}

static bool sync_dir(const char *dir) {
    int fd = open(dir, O_RDONLY);
    if (fd < 0) return false;
    bool ok = fsync(fd) == 0;
    close(fd);
    return ok;
}

static bool write_all(int fd, const void *p, size_t n, off_t off) {
    const uint8_t *b = p;
    while (n) {
        ssize_t w = pwrite(fd, b, n, off);
        if (w < 0) { if (errno == EINTR) continue; return false; }
        b += w;
        n -= (size_t)w;
        off += w;
    }
    return true;
}

static size_t page_size(void) {
    long p = sysconf(_SC_PAGESIZE);
    return p > 0 ? (size_t)p : 4096;
}

static size_t round_up(size_t n, size_t to) { return (n + to - 1) / to * to; }

/*  ------------------------------------------------------------ the mapping */

/*  Reserve the address space and map the file's node array at its base. */
static bool map_arena(av_pma *p, int fd, size_t file_nodes) {
    p->reserve = round_up((size_t)AV_MAX_NODES * sizeof(av_node), page_size());
    void *r = mmap(NULL, p->reserve, PROT_NONE, MAP_PRIVATE | MAP_ANON, -1, 0);
    if (r == MAP_FAILED) return false;
    p->base = r;
    if (file_nodes) {
        void *m = mmap(p->base, file_nodes, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_FIXED,
                       fd, (off_t)p->hdr);
        if (m == MAP_FAILED) { munmap(p->base, p->reserve); p->base = NULL; return false; }
    }
    p->mapped = p->file_nodes = file_nodes;
    return true;
}

/*  Make the first `bytes` of the reservation accessible. */
static bool map_to(av_pma *p, size_t bytes) {
    bytes = round_up(bytes, page_size());
    if (bytes > p->reserve) return false;
    if (bytes <= p->mapped) return true;
    void *m = mmap(p->base + p->mapped, bytes - p->mapped, PROT_READ | PROT_WRITE,
                   MAP_PRIVATE | MAP_ANON | MAP_FIXED, -1, 0);
    if (m == MAP_FAILED) return false;
    size_t chunks = bytes / CHUNK;
    uint8_t *d = realloc(p->dirty, chunks);
    if (!d) return false;
    memset(d + p->nchunks, 0, chunks - p->nchunks);
    p->dirty = d;
    p->nchunks = chunks;
    p->mapped = bytes;
    return true;
}

bool pma_grow(av_arena *a, uint64_t nodes) {
    av_pma *p = a->pma;
    if (nodes > AV_MAX_NODES) nodes = AV_MAX_NODES;
    if (!map_to(p, (size_t)nodes * sizeof(av_node))) return false;
    uint64_t cap = p->mapped / sizeof(av_node);
    a->cap = cap > AV_MAX_NODES ? AV_MAX_NODES : (uint32_t)cap;
    return true;
}

void pma_touch(av_arena *a, uint32_t i) {
    av_pma *p = a->pma;
    if (i < p->committed) p->dirty[i / CHUNK_NODES] = 1;
}

void pma_collected(av_arena *a, const av_node *to, uint32_t used) {
    memcpy(a->nodes, to, (size_t)used * sizeof(av_node));
    a->pma->all_dirty = true;
}

void pma_release(av_arena *a) {
    av_pma *p = a->pma;
    if (p->base) munmap(p->base, p->reserve);
    if (p->fd >= 0) close(p->fd);
    free(p->dirty);
    free(p->dir);
    free(p);
    a->pma = NULL;
    a->nodes = NULL;
}

/*  -------------------------------------------------------------- the atoms */

static uint8_t *atoms_blob(const av_arena *a, size_t *len) {
    size_t n = 0;
    for (uint32_t id = SKI_ATOM_FIRST; id < a->n_leaves; id++) n += 8 + strlen(a->atom_name[id]);
    uint8_t *b = malloc(n ? n : 1);
    if (!b) return NULL;
    size_t at = 0;
    for (uint32_t id = SKI_ATOM_FIRST; id < a->n_leaves; id++) {
        size_t l = strlen(a->atom_name[id]);
        put32(b + at, a->atom_node[id]);
        put32(b + at + 4, (uint32_t)l);
        memcpy(b + at + 8, a->atom_name[id], l);
        at += 8 + l;
    }
    *len = n;
    return b;
}

/*  ------------------------------------------------------------ the journal */

typedef struct { uint8_t *b; size_t len, cap; } buf;

static bool put(buf *j, const void *p, size_t n) {
    if (j->len + n > j->cap) {
        size_t cap = j->cap ? j->cap : 1 << 16;
        while (j->len + n > cap) cap *= 2;
        uint8_t *q = realloc(j->b, cap);
        if (!q) return false;
        j->b = q;
        j->cap = cap;
    }
    memcpy(j->b + j->len, p, n);
    j->len += n;
    return true;
}

static bool record(buf *j, uint8_t file, uint64_t off, const void *data, uint32_t len) {
    uint8_t h[13];
    h[0] = file;
    put64(h + 1, off);
    put32(h + 9, len);
    return put(j, h, sizeof h) && put(j, data, len);
}

static void crash_point(int n) {
    if (av_pma_crash_at == n) _exit(77);
}

/*  Apply a verified journal to the files: sizes first, then the records,
 *  then sync.  Idempotent. */
static bool apply(const char *dir, const uint8_t *j, size_t len, const char **err) {
    char *np = path_in(dir, "nodes"), *ap = path_in(dir, "atoms");
    int fn = np ? open(np, O_RDWR | O_CREAT, 0644) : -1;
    int fa = ap ? open(ap, O_RDWR | O_CREAT, 0644) : -1;
    free(np);
    free(ap);
    bool ok = fn >= 0 && fa >= 0;
    uint64_t nsize = get64(j + 16), asize = get64(j + 24);
    uint32_t nrec = get32(j + 32);
    struct stat st;
    /* the nodes file never shrinks: a private mapping of it must not end
     * beneath its own pages */
    if (ok && fstat(fn, &st) == 0 && (uint64_t)st.st_size < nsize) ok = ftruncate(fn, (off_t)nsize) == 0;
    if (ok) ok = ftruncate(fa, (off_t)asize) == 0;
    size_t at = 36;
    for (uint32_t r = 0; ok && r < nrec; r++) {
        if (r == nrec / 2) crash_point(3);
        uint8_t file = j[at];
        uint64_t off = get64(j + at + 1);
        uint32_t l = get32(j + at + 9);
        ok = write_all(file == 0 ? fn : fa, j + at + 13, l, (off_t)off);
        at += 13 + l;
    }
    if (ok) ok = fsync(fn) == 0 && fsync(fa) == 0;
    if (fn >= 0) close(fn);
    if (fa >= 0) close(fa);
    if (!ok && err) *err = "the journal cannot be applied to the image";
    (void)len;
    return ok;
}

/*  A journal's bytes, verified: NULL if there is none; *bad if it does
 *  not verify. */
static uint8_t *read_journal(const char *path, size_t *len, bool *bad) {
    *bad = false;
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *b = n > 0 ? malloc((size_t)n) : NULL;
    size_t got = b ? fread(b, 1, (size_t)n, f) : 0;
    fclose(f);
    *bad = true;
    if (!b || got != (size_t)n || n < 36 + 32 || memcmp(b, "AVONJNL1", 8) != 0) { free(b); return NULL; }
    uint8_t sha[32];
    av_sha256(b, (size_t)n - 32, sha);
    if (memcmp(sha, b + n - 32, 32) != 0) { free(b); return NULL; }
    /* the records lie within it */
    size_t at = 36, end = (size_t)n - 32;
    for (uint32_t r = 0, nrec = get32(b + 32); r < nrec; r++) {
        if (at + 13 > end || get32(b + at + 9) > end - at - 13) { free(b); return NULL; }
        at += 13 + get32(b + at + 9);
    }
    if (at != end) { free(b); return NULL; }
    *bad = false;
    *len = (size_t)n;
    return b;
}

/*  Apply and remove a journal left in dir, if any. */
static bool recover(const char *dir, const char **err) {
    char *tmp = path_in(dir, "journal.tmp"), *jp = path_in(dir, "journal");
    bool ok = tmp && jp;
    if (ok) unlink(tmp);                        /* never renamed: never happened */
    size_t len;
    bool bad;
    uint8_t *j = ok ? read_journal(jp, &len, &bad) : NULL;
    if (ok && !j && bad) { *err = "the journal does not verify"; ok = false; }
    if (ok && j) ok = apply(dir, j, len, err) && unlink(jp) == 0 && sync_dir(dir);
    free(j);
    free(tmp);
    free(jp);
    return ok;
}

/*  ------------------------------------------------------------- the header */

static void header(const av_arena *a, const av_pma *p, uint32_t root, uint64_t events,
                   uint64_t atoms_size, const uint8_t atoms_sha[32], uint8_t *h) {
    memset(h, 0, p->hdr);
    memcpy(h, "AVONPMA1", 8);
    put32(h + 8, 1);
    put32(h + 12, (uint32_t)p->hdr);
    put32(h + 16, a->used);
    put32(h + 20, a->n_leaves);
    put32(h + 24, root);
    put64(h + 28, events);
    put64(h + 36, atoms_size);
    memcpy(h + 44, atoms_sha, 32);
    av_sha256(h, HDR_FIELDS, h + HDR_FIELDS);
}

/*  ------------------------------------------------------------- the commit */

bool av_pma_commit(av_arena *a, uint32_t root, uint64_t events, const char **err) {
    *err = NULL;
    av_pma *p = a->pma;
    if (!p) { *err = "the arena has no image"; return false; }
    if (a->njets) { *err = "an arena with jets: the dashboard is never persisted"; return false; }
    if (root != AV_NONE && root >= a->used) { *err = "the root is not a node"; return false; }
    size_t alen;
    uint8_t *atoms = atoms_blob(a, &alen);
    uint8_t *hdr = malloc(p->hdr);
    buf j = { 0 };
    bool ok = atoms && hdr;
    uint8_t asha[32];
    if (ok) av_sha256(atoms, alen, asha);
    uint64_t node_bytes = (uint64_t)a->used * sizeof(av_node);
    uint64_t nsize = p->hdr + round_up((size_t)node_bytes, page_size());
    if (nsize < p->hdr + p->file_nodes) nsize = p->hdr + p->file_nodes;
    uint64_t chunks = 0, nrec = 0;
    uint8_t jh[36];
    memcpy(jh, "AVONJNL1", 8);
    put64(jh + 8, events);
    put64(jh + 16, nsize);
    put64(jh + 24, alen);
    ok = ok && put(&j, jh, sizeof jh);
    /* the chunks changed since the last commit, and those with new nodes */
    size_t last = (size_t)((node_bytes + CHUNK - 1) / CHUNK);
    for (size_t c = 0; ok && c < last; c++) {
        bool fresh = (uint64_t)(c + 1) * CHUNK_NODES > p->committed;
        if (!p->all_dirty && !fresh && !p->dirty[c]) continue;
        uint64_t off = (uint64_t)c * CHUNK;
        uint32_t len = (uint32_t)(node_bytes - off < CHUNK ? node_bytes - off : CHUNK);
        ok = record(&j, 0, p->hdr + off, p->base + off, len);
        chunks++;
        nrec++;
    }
    if (ok) {                                   /* the header's fields; the page's
                                                 * rest is zeros the file already has */
        header(a, p, root, events, alen, asha, hdr);
        ok = record(&j, 0, 0, hdr, HDR_FIELDS + 32);
        nrec++;
    }
    if (ok && memcmp(asha, p->atoms_sha, 32) != 0) {
        ok = record(&j, 1, 0, atoms, (uint32_t)alen);
        nrec++;
    }
    if (ok) {
        put32(j.b + 32, (uint32_t)nrec);
        uint8_t sha[32];
        av_sha256(j.b, j.len, sha);
        ok = put(&j, sha, 32);
    }
    char *tmp = path_in(p->dir, "journal.tmp"), *jp = path_in(p->dir, "journal");
    int fd = ok && tmp ? open(tmp, O_WRONLY | O_CREAT | O_TRUNC, 0644) : -1;
    ok = ok && fd >= 0 && write_all(fd, j.b, j.len, 0) && fsync(fd) == 0;
    if (fd >= 0) close(fd);
    if (ok) crash_point(1);
    ok = ok && jp && rename(tmp, jp) == 0 && sync_dir(p->dir);
    if (ok) crash_point(2);
    ok = ok && apply(p->dir, j.b, j.len, err);
    if (ok) crash_point(4);
    ok = ok && unlink(jp) == 0 && sync_dir(p->dir);
    if (ok) {
        p->committed = a->used;
        p->all_dirty = false;
        memset(p->dirty, 0, p->nchunks);
        memcpy(p->atoms_sha, asha, 32);
        if (nsize - p->hdr > p->file_nodes) p->file_nodes = (size_t)(nsize - p->hdr);
        p->last_bytes = j.len;
        p->last_chunks = chunks;
    } else if (!*err) {
        *err = "the journal cannot be written";
    }
    free(tmp);
    free(jp);
    free(j.b);
    free(atoms);
    free(hdr);
    return ok;
}

uint64_t av_pma_last_bytes(const av_arena *a) { return a->pma ? a->pma->last_bytes : 0; }
uint64_t av_pma_last_chunks(const av_arena *a) { return a->pma ? a->pma->last_chunks : 0; }

/*  ------------------------------------------------------ attach and open */

bool av_pma_attach(av_arena *a, const char *dir, const char **err) {
    *err = NULL;
    if (a->pma) { *err = "the arena has an image already"; return false; }
    if (mkdir(dir, 0777) != 0 && errno != EEXIST) { *err = "cannot make the image's directory"; return false; }
    char *np = path_in(dir, "nodes");
    if (!np) { *err = "out of memory"; return false; }
    if (access(np, F_OK) == 0) { free(np); *err = "an image is already there"; return false; }
    int fd = open(np, O_RDWR | O_CREAT | O_EXCL, 0644);
    free(np);
    if (fd < 0) { *err = "cannot create the image"; return false; }
    if (flock(fd, LOCK_EX | LOCK_NB) != 0) { close(fd); *err = "the image is in use"; return false; }
    av_pma *p = calloc(1, sizeof *p);
    if (!p || !(p->dir = strdup(dir))) { free(p); close(fd); *err = "out of memory"; return false; }
    p->fd = fd;
    p->hdr = page_size();
    if (!map_arena(p, fd, 0) || !map_to(p, (size_t)a->cap * sizeof(av_node))) {
        close(fd);
        if (p->base) munmap(p->base, p->reserve);
        free(p->dirty);
        free(p->dir);
        free(p);
        *err = "cannot map the arena";
        return false;
    }
    memcpy(p->base, a->nodes, (size_t)a->used * sizeof(av_node));
    free(a->nodes);
    a->nodes = (av_node *)(void *)p->base;
    a->pma = p;
    p->all_dirty = true;                        /* the first commit writes it all */
    uint64_t cap = p->mapped / sizeof(av_node);
    a->cap = cap > AV_MAX_NODES ? AV_MAX_NODES : (uint32_t)cap;
    return true;
}

av_arena *av_pma_open(const char *dir, uint32_t *root, uint64_t *events, const char **err) {
    *err = NULL;
    /* one process at a time: the lock is held until the arena is freed,
     * and taken before a journal is recovered */
    char *np = path_in(dir, "nodes"), *ap = path_in(dir, "atoms");
    int fd = np ? open(np, O_RDWR) : -1;
    free(np);
    if (fd >= 0 && flock(fd, LOCK_EX | LOCK_NB) != 0) {
        close(fd);
        free(ap);
        *err = "the image is in use";
        return NULL;
    }
    if (fd >= 0 && !recover(dir, err)) { close(fd); free(ap); return NULL; }
    FILE *af = ap ? fopen(ap, "rb") : NULL;
    free(ap);
    av_arena *a = NULL;
    av_pma *p = NULL;
    uint8_t *h = NULL, *atoms = NULL;
    size_t hdr = page_size();
    struct stat st;
    if (fd < 0 || !af || fstat(fd, &st) != 0) { *err = "no image"; goto fail; }
    h = malloc(HDR_FIELDS + 32);
    if (!h || pread(fd, h, HDR_FIELDS + 32, 0) != HDR_FIELDS + 32) { *err = "the header is short"; goto fail; }
    uint8_t sha[32];
    av_sha256(h, HDR_FIELDS, sha);
    if (memcmp(h, "AVONPMA1", 8) != 0 || get32(h + 8) != 1 || memcmp(sha, h + HDR_FIELDS, 32) != 0) {
        *err = "the header does not verify";
        goto fail;
    }
    hdr = get32(h + 12);
    uint32_t used = get32(h + 16), leaves = get32(h + 20);
    uint64_t asize = get64(h + 36);
    if (hdr % page_size() || used < SKI_ATOM_FIRST || leaves < SKI_ATOM_FIRST ||
        (uint64_t)st.st_size < hdr + (uint64_t)used * sizeof(av_node) || (st.st_size - hdr) % page_size()) {
        *err = "the header disagrees with the image";
        goto fail;
    }
    *root = get32(h + 24);
    *events = get64(h + 28);
    if (*root != AV_NONE && *root >= used) { *err = "the root lies past the nodes"; goto fail; }
    atoms = malloc(asize ? asize : 1);
    if (!atoms || fread(atoms, 1, asize, af) != asize || fgetc(af) != EOF) { *err = "the atoms are short"; goto fail; }
    av_sha256(atoms, asize, sha);
    if (memcmp(sha, h + 44, 32) != 0) { *err = "the atoms do not verify"; goto fail; }

    a = calloc(1, sizeof *a);
    p = calloc(1, sizeof *p);
    if (!a || !p || !(p->dir = strdup(dir))) { *err = "out of memory"; goto fail; }
    p->fd = fd;
    fd = -1;
    p->hdr = hdr;
    a->leaf_cap = leaves < 16 ? 16 : leaves;
    a->atom_name = calloc(a->leaf_cap, sizeof *a->atom_name);
    a->atom_node = calloc(a->leaf_cap, sizeof *a->atom_node);
    if (!a->atom_name || !a->atom_node) { *err = "out of memory"; goto fail; }
    for (ski_leaf id = 0; id < SKI_ATOM_FIRST; id++) a->atom_node[id] = id;
    a->n_leaves = SKI_ATOM_FIRST;
    for (size_t at = 0; at < asize;) {          /* id order, from 3 */
        if (at + 8 > asize || get32(atoms + at + 4) > asize - at - 8 || a->n_leaves == leaves) {
            *err = "the atoms are malformed";
            goto fail;
        }
        uint32_t node = get32(atoms + at), len = get32(atoms + at + 4);
        char *name = malloc(len + 1);
        if (!name) { *err = "out of memory"; goto fail; }
        memcpy(name, atoms + at + 8, len);
        name[len] = '\0';
        /* the image is local state: probe markers, `@N`, are its leaves as
         * much as any; only a name no arena could hold is refused */
        if (node >= used || !len || strlen(name) != len) {
            free(name);
            *err = "the atoms are malformed";
            goto fail;
        }
        a->atom_name[a->n_leaves] = name;
        a->atom_node[a->n_leaves++] = node;
        at += 8 + len;
    }
    if (a->n_leaves != leaves) { *err = "the atoms are short"; goto fail; }
    if (!map_arena(p, p->fd, (size_t)(st.st_size - hdr))) { *err = "cannot map the image"; goto fail; }
    p->nchunks = p->mapped / CHUNK;
    p->dirty = calloc(p->nchunks ? p->nchunks : 1, 1);
    if (!p->dirty) { *err = "out of memory"; goto fail; }
    a->pma = p;
    a->nodes = (av_node *)(void *)p->base;
    a->used = used;
    uint64_t cap = p->mapped / sizeof(av_node);
    a->cap = cap > AV_MAX_NODES ? AV_MAX_NODES : (uint32_t)cap;
    if (a->cap < 2 * a->used + 1024 && !pma_grow(a, 2 * (uint64_t)a->used + 1024)) {
        *err = "cannot map the arena";
        goto fail;
    }
    p->committed = used;
    memcpy(p->atoms_sha, h + 44, 32);
    /* leaves S, K and I sit at 0, 1, 2 in every arena (§2) */
    for (ski_leaf id = 0; id < SKI_ATOM_FIRST; id++)
        if (a->nodes[id].l >> AV_TAG_SHIFT != AV_LEAF || a->nodes[id].r != id) {
            *err = "the image's first nodes are not S, K and I";
            goto fail;
        }
    free(h);
    free(atoms);
    fclose(af);
    return a;
fail:
    if (a) {
        if (!a->pma && p) {
            if (p->base) munmap(p->base, p->reserve);
            if (p->fd >= 0) close(p->fd);
            free(p->dirty);
            free(p->dir);
            free(p);
        }
        av_arena_free(a);
    } else if (p) {
        free(p->dir);
        free(p);
    }
    if (fd >= 0) close(fd);
    if (af) fclose(af);
    free(h);
    free(atoms);
    return NULL;
}

/*  ------------------------------------------------------------- the check */

bool av_pma_verify(const av_arena *a, uint32_t root, const char **err) {
    if (root != AV_NONE && root >= a->used) { *err = "the root lies past the nodes"; return false; }
    for (uint32_t i = 0; i < a->used; i++) {
        av_node n = a->nodes[i];
        uint32_t tag = n.l >> AV_TAG_SHIFT, x = n.l & AV_PAYLOAD;
        if (tag == AV_APP ? x >= a->used || n.r >= a->used
            : tag == AV_IND ? x >= a->used
            : tag == AV_LEAF ? n.r >= a->n_leaves || a->atom_node[n.r] != i
            : true) {                           /* a jet node, or a bad index */
            *err = tag == AV_JET ? "a jet node in the image" : "a node points outside the image";
            return false;
        }
    }
    return true;
}
