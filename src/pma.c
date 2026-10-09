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
 *  idempotent.  The journal streams, a block at a time.  Journal layout: "AVONJNL1", u64 events, u64 nodes file
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
#include "durable.h"
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

static bool sync_dir(const char *dir) { return av_sync_dir(dir); }

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

/*  The journal is written and read as a stream: memory holds one block of
 *  it and one record, never the whole (AUDIT.md item 15). */

#define JBLOCK ((size_t)1 << 16)

static bool read_all(int fd, void *p, size_t n, off_t off) {
    uint8_t *b = p;
    while (n) {
        ssize_t r = pread(fd, b, n, off);
        if (r < 0) { if (errno == EINTR) continue; return false; }
        if (r == 0) return false;                   /* short: the file ends */
        b += r;
        n -= (size_t)r;
        off += r;
    }
    return true;
}

typedef struct {
    int           fd;
    off_t         off;                      /* bytes written to the file */
    uint8_t      *b;                        /* a block, JBLOCK bytes */
    size_t        fill;
    av_sha256_ctx sha;                      /* of everything put */
    bool          ok;
} jw;

static bool jw_flush(jw *w) {
    if (w->ok && w->fill) {
        w->ok = write_all(w->fd, w->b, w->fill, w->off);
        w->off += (off_t)w->fill;
        w->fill = 0;
    }
    return w->ok;
}

static void put_raw(jw *w, const void *p, size_t n) {
    if (w->fill + n > JBLOCK && !jw_flush(w)) return;
    if (n >= JBLOCK) {                          /* a large record goes straight out */
        w->ok = write_all(w->fd, p, n, w->off);
        w->off += (off_t)n;
        return;
    }
    memcpy(w->b + w->fill, p, n);
    w->fill += n;
}

static void put(jw *w, const void *p, size_t n) {
    if (!w->ok) return;
    av_sha256_update(&w->sha, p, n);
    put_raw(w, p, n);
}

static void record(jw *w, uint8_t file, uint64_t off, const void *data, uint32_t len) {
    uint8_t h[13];
    h[0] = file;
    put64(h + 1, off);
    put32(h + 9, len);
    put(w, h, sizeof h);
    put(w, data, len);
}

static void crash_point(int n) {
    if (av_pma_crash_at == n) _exit(77);
}

/*  Apply the journal at jp to the files: sizes first, then the records,
 *  then sync.  The journal is verified, or was just written.  Idempotent. */
static bool apply(const char *dir, const char *jp, const char **err) {
    char *np = path_in(dir, "nodes"), *ap = path_in(dir, "atoms");
    int fj = open(jp, O_RDONLY);
    int fn = np ? open(np, O_RDWR | O_CREAT, 0600) : -1;
    int fa = ap ? open(ap, O_RDWR | O_CREAT, 0600) : -1;
    free(np);
    free(ap);
    uint8_t jh[36], *rec = NULL;
    size_t cap = 0;
    bool ok = fj >= 0 && fn >= 0 && fa >= 0 && read_all(fj, jh, sizeof jh, 0);
    uint64_t nsize = ok ? get64(jh + 16) : 0, asize = ok ? get64(jh + 24) : 0;
    uint32_t nrec = ok ? get32(jh + 32) : 0;
    struct stat st;
    /* the nodes file never shrinks: a private mapping of it must not end
     * beneath its own pages */
    if (ok && fstat(fn, &st) == 0 && (uint64_t)st.st_size < nsize) ok = ftruncate(fn, (off_t)nsize) == 0;
    if (ok) ok = ftruncate(fa, (off_t)asize) == 0;
    off_t at = sizeof jh;
    for (uint32_t r = 0; ok && r < nrec; r++) {
        if (r == nrec / 2) crash_point(3);
        uint8_t h[13];
        ok = read_all(fj, h, sizeof h, at);
        uint32_t l = ok ? get32(h + 9) : 0;
        if (ok && l > cap) {
            uint8_t *q = realloc(rec, l);
            ok = q != NULL;
            if (ok) { rec = q; cap = l; }
        }
        ok = ok && read_all(fj, rec, l, at + 13)
                && write_all(h[0] == 0 ? fn : fa, rec, l, (off_t)get64(h + 1));
        at += 13 + (off_t)l;
    }
    if (ok) ok = av_sync_fd(fn) && av_sync_fd(fa);
    if (fj >= 0) close(fj);
    if (fn >= 0) close(fn);
    if (fa >= 0) close(fa);
    free(rec);
    if (!ok && err) *err = "the journal cannot be applied to the image";
    return ok;
}

/*  Whether a journal is at jp (*there), and whether it verifies: its
 *  digest, read a block at a time, and its records within it. */
static bool verify_journal(const char *jp, bool *there) {
    int fd = open(jp, O_RDONLY);
    *there = fd >= 0 || errno != ENOENT;
    if (fd < 0) return false;
    struct stat st;
    uint8_t *b = malloc(JBLOCK);
    bool ok = b && fstat(fd, &st) == 0 && st.st_size >= 36 + 32;
    off_t end = ok ? st.st_size - 32 : 0;
    if (ok) ok = read_all(fd, b, 36, 0) && memcmp(b, "AVONJNL1", 8) == 0;
    uint32_t nrec = ok ? get32(b + 32) : 0;
    av_sha256_ctx s;
    av_sha256_init(&s);
    for (off_t at = 0; ok && at < end; ) {
        size_t n = end - at < (off_t)JBLOCK ? (size_t)(end - at) : JBLOCK;
        ok = read_all(fd, b, n, at);
        if (ok) av_sha256_update(&s, b, n);
        at += (off_t)n;
    }
    uint8_t sha[32];
    av_sha256_final(&s, sha);
    if (ok) ok = read_all(fd, b, 32, end) && memcmp(sha, b, 32) == 0;
    off_t at = 36;
    for (uint32_t r = 0; ok && r < nrec; r++) {
        ok = end - at >= 13 && read_all(fd, b, 13, at) && get32(b + 9) <= end - at - 13;
        if (ok) at += 13 + (off_t)get32(b + 9);
    }
    ok = ok && at == end;
    free(b);
    close(fd);
    return ok;
}

/*  Apply and remove a journal left in dir, if any. */
static bool recover(const char *dir, const char **err) {
    char *tmp = path_in(dir, "journal.tmp"), *jp = path_in(dir, "journal");
    bool ok = tmp && jp, there = false;
    if (!ok) *err = "out of memory";
    if (ok) unlink(tmp);                        /* never renamed: never happened */
    bool good = ok && verify_journal(jp, &there);
    if (ok && there && !good) { *err = "the journal does not verify"; ok = false; }
    if (ok && there) ok = apply(dir, jp, err);
    if (ok && there && (unlink(jp) != 0 || !sync_dir(dir))) {
        *err = "the journal applied, but cannot be removed";   /* not NULL, printed as (null) */
        ok = false;
    }
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
    char *tmp = path_in(p->dir, "journal.tmp"), *jp = path_in(p->dir, "journal");
    jw w = { .fd = -1, .b = malloc(JBLOCK) };
    bool ok = atoms && hdr && tmp && jp && w.b;
    uint8_t asha[32];
    if (ok) av_sha256(atoms, alen, asha);
    bool new_atoms = ok && memcmp(asha, p->atoms_sha, 32) != 0;
    uint64_t node_bytes = (uint64_t)a->used * sizeof(av_node);
    uint64_t nsize = p->hdr + round_up((size_t)node_bytes, page_size());
    if (nsize < p->hdr + p->file_nodes) nsize = p->hdr + p->file_nodes;
    /* the chunks changed since the last commit, and those with new nodes;
     * counted first, since the count heads the journal */
    size_t last = (size_t)((node_bytes + CHUNK - 1) / CHUNK);
    uint64_t chunks = 0;
    for (size_t c = 0; c < last; c++)
        if (p->all_dirty || (uint64_t)(c + 1) * CHUNK_NODES > p->committed || p->dirty[c]) chunks++;
    uint8_t jh[36];
    memcpy(jh, "AVONJNL1", 8);
    put64(jh + 8, events);
    put64(jh + 16, nsize);
    put64(jh + 24, alen);
    put32(jh + 32, (uint32_t)(chunks + 1 + new_atoms));
    if (ok) {
        w.fd = open(tmp, O_WRONLY | O_CREAT | O_TRUNC, 0600);
        w.ok = w.fd >= 0;
        av_sha256_init(&w.sha);
    }
    put(&w, jh, sizeof jh);
    for (size_t c = 0; w.ok && c < last; c++) {
        bool fresh = (uint64_t)(c + 1) * CHUNK_NODES > p->committed;
        if (!p->all_dirty && !fresh && !p->dirty[c]) continue;
        uint64_t off = (uint64_t)c * CHUNK;
        uint32_t len = (uint32_t)(node_bytes - off < CHUNK ? node_bytes - off : CHUNK);
        record(&w, 0, p->hdr + off, p->base + off, len);
    }
    /* the header's fields; the page's rest is zeros the file already has */
    if (w.ok) header(a, p, root, events, alen, asha, hdr);
    record(&w, 0, 0, hdr, HDR_FIELDS + 32);
    if (new_atoms) record(&w, 1, 0, atoms, (uint32_t)alen);
    uint8_t sha[32];
    av_sha256_final(&w.sha, sha);
    if (w.ok) put_raw(&w, sha, 32);
    ok = jw_flush(&w) && av_sync_fd(w.fd);
    if (w.fd >= 0) close(w.fd);
    if (ok) crash_point(1);
    ok = ok && rename(tmp, jp) == 0 && sync_dir(p->dir);
    if (ok) crash_point(2);
    ok = ok && apply(p->dir, jp, err);
    if (ok) crash_point(4);
    ok = ok && unlink(jp) == 0 && sync_dir(p->dir);
    if (ok) {
        p->committed = a->used;
        p->all_dirty = false;
        memset(p->dirty, 0, p->nchunks);
        memcpy(p->atoms_sha, asha, 32);
        if (nsize - p->hdr > p->file_nodes) p->file_nodes = (size_t)(nsize - p->hdr);
        p->last_bytes = (uint64_t)w.off;
        p->last_chunks = chunks;
    } else if (!*err) {
        *err = "the journal cannot be written";
    }
    free(tmp);
    free(jp);
    free(w.b);
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
    if (mkdir(dir, 0700) != 0 && errno != EEXIST) { *err = "cannot make the image's directory"; return false; }
    char *np = path_in(dir, "nodes");
    if (!np) { *err = "out of memory"; return false; }
    if (access(np, F_OK) == 0) { free(np); *err = "an image is already there"; return false; }
    int fd = open(np, O_RDWR | O_CREAT | O_EXCL, 0600);
    if (fd < 0) { free(np); *err = "cannot create the image"; return false; }
    /* from here a failure removes the file it made, so a retry finds no
     * image already there (AUDIT.md item 15) */
    if (flock(fd, LOCK_EX | LOCK_NB) != 0) {
        close(fd); unlink(np); free(np); *err = "the image is in use"; return false;
    }
    av_pma *p = calloc(1, sizeof *p);
    if (!p || !(p->dir = strdup(dir))) {
        free(p); close(fd); unlink(np); free(np); *err = "out of memory"; return false;
    }
    p->fd = fd;
    p->hdr = page_size();
    if (!map_arena(p, fd, 0) || !map_to(p, (size_t)a->cap * sizeof(av_node))) {
        close(fd);
        unlink(np);
        if (p->base) munmap(p->base, p->reserve);
        free(p->dirty);
        free(p->dir);
        free(p);
        free(np);
        *err = "cannot map the arena";
        return false;
    }
    free(np);
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
    if (p) p->fd = -1;                          /* not 0, stdin, which fail: would close */
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
