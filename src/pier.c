/**  pier.c
 *
 *  A kernel's durable home: an event log and snapshots, in Nockchain's
 *  order---the event appended and synced before it is applied, a
 *  snapshot's image before its sidecar---so that reopening after a crash
 *  replays onto the newest snapshot that verifies exactly the events that
 *  were logged.
 */

#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/random.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <unistd.h>

#include "avon.h"
#include "durable.h"

struct av_pier {
    char      *dir;
    av_arena  *a;
    av_kernel  k;
    av_opts    o;
    int        log;             /* events.log, appended, locked: -1 if none */
    bool       pma;             /* committed to a persistent arena */
    bool       eny;             /* booted with --entropy           */
    bool       eny_from_file;   /* booted with --entropy=FILE: only a file */
    char      *eny_file;        /* --entropy=FILE: bits from it, not getentropy */
    uint64_t   eny_n;           /* eny records in the log                 */
    uint64_t   eny_replies;     /* replies the last poke drew             */
    uint64_t   eny_unanswered;  /* requests it left at the cap            */
    uint64_t   probe_from;      /* a->probe_steps when the poke began     */
    const char *eny_err;        /* why the last poke's replies stopped    */
    const char *commit_err;     /* why the last event's image did not commit */
    av_pier_event_fn event_fn;
    void      *event_ctx;
};

static char *path_in(const char *dir, const char *name) {
    size_t n = strlen(dir) + strlen(name) + 2;
    char *p = malloc(n);
    if (p) snprintf(p, n, "%s/%s", dir, name);
    return p;
}

static char *hex_put(char *o, const uint8_t *b, size_t n) {
    static const char hx[] = "0123456789abcdef";
    for (size_t i = 0; i < n; i++) {
        *o++ = hx[b[i] >> 4];
        *o++ = hx[b[i] & 15];
    }
    return o;
}

static int nibble(char c) {
    return c >= '0' && c <= '9' ? c - '0' : c >= 'a' && c <= 'f' ? c - 'a' + 10 : -1;
}

/*  Lowercase hex, two digits a byte, as hex_put writes it, and nothing
 *  else, read in one linear pass. */
static uint8_t *unhex(const char *s, size_t n, size_t *len) {
    if (n % 2) return NULL;
    uint8_t *out = malloc(n / 2 + 1);
    if (!out) return NULL;
    for (size_t i = 0; i < n / 2; i++) {
        int hi = nibble(s[2 * i]), lo = nibble(s[2 * i + 1]);
        if (hi < 0 || lo < 0) { free(out); return NULL; }
        out[i] = (uint8_t)(hi << 4 | lo);
    }
    *len = n / 2;
    return out;
}

/*  A record's checksum: the first 4 bytes of the SHA-256 of its text
 *  before ` =`, in hex, so a flipped digit in a record does not replay as
 *  another event. */
#define SUM_HEX 8
static void record_sum(const char *rec, size_t n, char out[SUM_HEX]) {
    uint8_t h[32];
    av_sha256(rec, n, h);
    hex_put(out, h, SUM_HEX / 2);
}

/*  Cut the log back to off, durably: a record that must not stand. */
static bool log_cut(int log, off_t off) {
    return ftruncate(log, off) == 0 && av_sync_fd(log);
}

/*  Append one record, whole, and sync it; *at is where it starts.  A
 *  record that fails to write or to sync is cut away again, so a pier
 *  kept open writes its next record after a whole one. */
static bool log_record(int log, const char *kind, uint64_t n, const uint8_t *a1, size_t n1,
                       const uint8_t *a2, size_t n2, off_t *at) {
    char head[48];
    int hn = snprintf(head, sizeof head, "%s %llu ", kind, (unsigned long long)n);
    if (hn < 0 || (size_t)hn >= sizeof head) return false;
    size_t body = (size_t)hn + 2 * n1 + (a2 ? 1 + 2 * n2 : 0);
    size_t len = body + 2 + SUM_HEX + 1;
    char *rec = malloc(len), *o = rec;
    if (!rec) return false;
    memcpy(o, head, (size_t)hn);
    o = hex_put(o + hn, a1, n1);
    if (a2) {
        *o++ = ' ';
        o = hex_put(o, a2, n2);
    }
    *o++ = ' ';
    *o++ = '=';
    record_sum(rec, body, o);
    o[SUM_HEX] = '\n';
    off_t start = lseek(log, 0, SEEK_END);
    bool ok = start >= 0;
    for (size_t done = 0; ok && done < len;) {
        ssize_t w = write(log, rec + done, len - done);
        if (w < 0 && errno == EINTR) continue;
        if (w <= 0) ok = false;
        else done += (size_t)w;
    }
    free(rec);
    if (ok) ok = av_sync_fd(log);
    if (!ok && start >= 0) log_cut(log, start);
    if (at) *at = start;
    return ok;
}

/*  Boot pill on subject in a, to a kernel: the new kernel's term. */
static uint32_t boot_term(av_arena *a, const uint8_t *pill, size_t npill, const uint8_t *subject,
                          size_t nsubject, const av_opts *o, const char **err) {
    uint32_t p = av_cue(a, pill, npill, err);
    if (p == AV_NONE) return AV_NONE;
    av_root_push(a, &p);
    uint32_t s = av_cue(a, subject, nsubject, err);
    av_root_pop(a);
    if (s == AV_NONE) return AV_NONE;
    av_kernel k;
    bool is_kernel;
    uint32_t value;
    av_result r;
    if (av_kernel_boot(&k, a, p, s, o, &is_kernel, &value, &r) != AV_WHNF) {
        *err = "the pill does not reach weak head normal form on the subject";
        return AV_NONE;
    }
    if (!is_kernel) { *err = "the pill's value is not a kernel"; return AV_NONE; }
    uint32_t t = k.k;
    av_kernel_free(&k);
    return t;
}

static bool snapshot(av_pier *p, const char **err) {
    char name[64];
    snprintf(name, sizeof name, "snap-%llu", (unsigned long long)p->k.events);
    char *path = path_in(p->dir, name);
    if (!path) { *err = "out of memory"; return false; }
    bool ok = av_snapshot_save(p->a, p->k.k, path, err);
    free(path);
    return ok;
}

bool av_pier_snapshot(av_pier *p, const char **err) { return snapshot(p, err); }

av_kernel *av_pier_kernel(av_pier *p) { return &p->k; }

void av_pier_free(av_pier *p) {
    if (!p) return;
    if (p->a) av_kernel_free(&p->k);
    if (p->log >= 0) close(p->log);
    av_arena_free(p->a);
    free(p->eny_file);
    free(p->dir);
    free(p);
}

/*  The log, opened to append, created (with create) readable by its owner
 *  only, as it holds the kernel's entropy, and locked for the pier's
 *  life: one process writes a pier.  -1 with *err; or, without create,
 *  with *missing if it is not there. */
static int open_log(const char *path, bool create, bool *missing, const char **err) {
    if (missing) *missing = false;
    int fd = open(path, O_RDWR | O_APPEND | (create ? O_CREAT : 0), 0600);
    if (fd < 0) {
        if (!create && errno == ENOENT && missing) *missing = true;
        else *err = "cannot open the event log";
        return -1;
    }
    if (flock(fd, LOCK_EX | LOCK_NB) != 0) {
        *err = errno == EWOULDBLOCK ? "the pier is in use" : "cannot lock the event log";
        close(fd);
        return -1;
    }
    return fd;
}

/*  A new pier's directory: made 0700, or one already there that is a
 *  directory, empty, the caller's own and closed to others, so that no
 *  one else can read the pier or plant a snapshot in it. */
static bool pier_dir(const char *dir, const char **err) {
    if (mkdir(dir, 0700) == 0) return true;
    if (errno != EEXIST) { *err = "cannot make the pier's directory"; return false; }
    struct stat st;
    if (lstat(dir, &st) != 0 || !S_ISDIR(st.st_mode)) { *err = "the pier's path is not a directory"; return false; }
    DIR *d = opendir(dir);
    if (!d) { *err = "cannot read the pier's directory"; return false; }
    struct dirent *e;
    bool empty = true;
    while (empty && (e = readdir(d)))
        if (strcmp(e->d_name, ".") != 0 && strcmp(e->d_name, "..") != 0) empty = false;
    closedir(d);
    if (!empty) { *err = "a pier is already there, or the directory is not empty"; return false; }
    if (st.st_uid != geteuid() || (st.st_mode & 077) != 0) {
        *err = "the pier's directory must be the caller's own and mode 0700";
        return false;
    }
    return true;
}

static av_pier *pier_alloc(const char *dir, const av_opts *o) {
    av_pier *p = calloc(1, sizeof *p);
    if (!p) return NULL;
    p->dir = strdup(dir);
    p->log = -1;
    p->o = *o;
    p->o.whnf_only = true;
    if (!p->dir) { free(p); return NULL; }
    return p;
}

static av_pier *pier_new(const char *dir, const uint8_t *pill, size_t npill,
                         const uint8_t *subject, size_t nsubject, const av_opts *o,
                         bool pma, bool eny, bool eny_file, const char **err) {
    char *logp = path_in(dir, "events.log");
    if (!logp) { *err = "out of memory"; return NULL; }
    if (access(logp, F_OK) == 0) { free(logp); *err = "a pier is already there"; return NULL; }
    if (!pier_dir(dir, err)) { free(logp); return NULL; }
    av_pier *p = pier_alloc(dir, o);
    if (!p || !(p->a = av_arena_new(1u << 16))) { free(logp); av_pier_free(p); *err = "out of memory"; return NULL; }
    /* the log first, empty and locked: the pier is this process's from
     * its first file; a crash before the image leaves a pier that will
     * not open, as no image verifies */
    p->log = open_log(logp, true, NULL, err);
    free(logp);
    if (p->log < 0) { av_pier_free(p); return NULL; }
    uint32_t k = boot_term(p->a, pill, npill, subject, nsubject, &p->o, err);
    if (k == AV_NONE) { av_pier_free(p); return NULL; }
    av_kernel_adopt(&p->k, p->a, k, &p->o);
    if (eny) {
        /* the opt-in before the image: a crash between them leaves a log
         * and no image, a pier that will not open, not one that opens
         * without its opt-in */
        const uint8_t from_file = 1;
        if (!log_record(p->log, "entropy", 0, &from_file, eny_file ? 1 : 0, NULL, 0, NULL)) {
            av_pier_free(p);
            *err = "the event log cannot be written";
            return NULL;
        }
        p->eny = true;
        p->eny_from_file = eny_file;
    }
    if (pma) {                                  /* the arena moves into its image */
        char *img = path_in(dir, "pma");
        p->pma = true;
        bool ok = img && av_pma_attach(p->a, img, err) &&
                  av_pma_commit(p->a, p->k.k, 0, err);
        free(img);
        if (!ok) { av_pier_free(p); return NULL; }
    } else if (!snapshot(p, err)) {
        av_pier_free(p);
        return NULL;
    }
    /* the log's entry, and the pier's in its parent, on the media */
    if (!av_sync_dir(dir) || !av_sync_parent(dir)) {
        *err = "cannot sync the pier's directory";
        av_pier_free(p);
        return NULL;
    }
    return p;
}

av_pier *av_pier_new(const char *dir, const uint8_t *pill, size_t npill,
                     const uint8_t *subject, size_t nsubject, const av_opts *o,
                     const char **err) {
    return pier_new(dir, pill, npill, subject, nsubject, o, false, false, false, err);
}

av_pier *av_pier_new_pma(const char *dir, const uint8_t *pill, size_t npill,
                         const uint8_t *subject, size_t nsubject, const av_opts *o,
                         const char **err) {
    return pier_new(dir, pill, npill, subject, nsubject, o, true, false, false, err);
}

av_pier *av_pier_new_ex(const char *dir, const uint8_t *pill, size_t npill, const uint8_t *subject,
                        size_t nsubject, const av_opts *o, unsigned flags, const char **err) {
    return pier_new(dir, pill, npill, subject, nsubject, o, flags & AV_PIER_PMA,
                    flags & (AV_PIER_ENTROPY | AV_PIER_ENTROPY_FILE),
                    flags & AV_PIER_ENTROPY_FILE, err);
}

/*  ------------------------------------------------------------ entropy
 *
 *  Under --entropy, a request is an element [0 id] of a poke's
 *  effects list, and its reply the event [0 [id bits]], bits 128 Scott
 *  Booleans in a list.  The pier finds requests by probing, never by
 *  name, and logs each reply as `eny N <id, jammed> <16 bytes>`. */

/*  Probes: copy mode writes nothing the kernel shares, and no collection
 *  moves the nodes being walked; bounded, so a diverging effect is no
 *  request rather than a hang. */
static av_opts probe_opts(const av_pier *p) {
    av_opts po = p->o;
    po.strategy = AV_COPY;
    po.no_collect = true;
    po.max_steps = 1000000;
    return po;
}

/*  The numeral 0, Zero of `Zero | Suc n`: one probe. */
static bool is_zero(av_arena *a, uint32_t t, const av_opts *po) {
    av_peeled z;
    return av_peel(a, t, 2, po, &z, NULL) && z.ctor == 0 && z.nfields == 0;
}

/*  t shown, by probing, to be a cell whose tag is a successor: an outside
 *  event the kernel cannot read as a reply.  Only a positive answer
 *  counts.  It is sound whatever the probe's fuel: probe markers are inert
 *  atoms, so if t m reduces to m g d and g z s to s n, then t applied to
 *  the kernel's own continuations reduces the same way, the markers
 *  replaced.  A probe that runs out, or anything else, is a refusal: a
 *  tag that reached 0 only past the probe's fuel would otherwise pass. */
static bool tagged_succ(av_arena *a, uint32_t t, const av_opts *po) {
    av_peeled c, g;
    return av_peel(a, t, 1, po, &c, NULL) && c.ctor == 0 && c.nfields == 2 &&
           av_peel(a, c.field[0], 2, po, &g, NULL) && g.ctor == 1 && g.nfields == 1;
}

/*  t a cell [0 x]: x. */
static bool tagged_zero(av_arena *a, uint32_t t, const av_opts *po, uint32_t *x) {
    av_peeled c;
    if (!av_peel(a, t, 1, po, &c, NULL) || c.ctor != 0 || c.nfields != 2) return false;
    if (!is_zero(a, c.field[0], po)) return false;
    *x = c.field[1];
    return true;
}

/*  pair x y, the Scott pair λc. c x y. */
static uint32_t pair_term(av_arena *a, uint32_t x, uint32_t y) {
    uint32_t si = av_app(a, AV_NODE_S, AV_NODE_I);
    uint32_t kx = av_app(a, AV_NODE_K, x), ky = av_app(a, AV_NODE_K, y);
    uint32_t f = si == AV_NONE || kx == AV_NONE ? AV_NONE : av_app(a, si, kx);
    uint32_t g = f == AV_NONE ? AV_NONE : av_app(a, AV_NODE_S, f);
    return g == AV_NONE || ky == AV_NONE ? AV_NONE : av_app(a, g, ky);
}

/*  The reply [0 [id bits]], id cued from its jam: bit 8i + j of the list
 *  is bit j of byte i, least significant first; true K, false K I; cons
 *  h t = K (pair h t), nil K. */
static uint32_t reply_event(av_arena *a, const uint8_t *idjam, size_t nid, const uint8_t *b,
                            const char **err) {
    uint32_t id = av_cue(a, idjam, nid, err);
    if (id == AV_NONE) return AV_NONE;
    uint32_t ki = av_app(a, AV_NODE_K, AV_NODE_I), t = AV_NODE_K;
    for (int i = 8 * AV_ENY_BYTES - 1; i >= 0 && t != AV_NONE && ki != AV_NONE; i--) {
        uint32_t c = pair_term(a, b[i / 8] >> (i % 8) & 1u ? AV_NODE_K : ki, t);
        t = c == AV_NONE ? AV_NONE : av_app(a, AV_NODE_K, c);
    }
    uint32_t inner = t == AV_NONE ? AV_NONE : pair_term(a, id, t);
    uint32_t ev = inner == AV_NONE ? AV_NONE : pair_term(a, AV_NODE_K, inner);
    if (ev == AV_NONE) *err = "out of memory";
    return ev;
}

/*  A queue of requests: their ids, jammed. */
typedef struct { av_buf *ids; size_t n, head, cap; } reqs;

static void reqs_free(reqs *q) {
    for (size_t i = q->head; i < q->n; i++) av_buf_free(&q->ids[i]);
    free(q->ids);
}

static bool reqs_push(reqs *q, av_buf b) {
    if (q->n == q->cap) {
        size_t c = q->cap ? 2 * q->cap : 8;
        av_buf *v = realloc(q->ids, c * sizeof *v);
        if (!v) return false;
        q->ids = v;
        q->cap = c;
    }
    q->ids[q->n++] = b;
    return true;
}

static bool boot_reply(av_pier *p, const char **err);

/*  The requests among effects eff, in order, onto q: eff a list (nil,
 *  cons), each element [0 id] a request, id with a normal form within the
 *  probes' fuel.  Anything else is no request; a list is walked at most
 *  AV_ENY_WALK elements.  False: out of memory. */
static bool find_requests(av_pier *p, uint32_t eff, reqs *q) {
    av_arena *a = p->a;
    av_opts po = probe_opts(p);
    for (unsigned i = 0; i < AV_ENY_WALK; i++) {
        if (a->probe_steps - p->probe_from > AV_ENY_PROBE_STEPS) {
            p->eny_err = "the probes of this event's effects spent their budget; later requests unread";
            return true;
        }
        av_peeled l;
        if (!av_peel(a, eff, 2, &po, &l, NULL) || l.ctor != 1 || l.nfields != 2) return true;
        uint32_t id;
        if (tagged_zero(a, l.field[0], &po, &id)) {
            /* the probe's field is a thunk over its marker, K id m: the
             * id's normal form is what the reply carries */
            av_opts no = po;
            no.whnf_only = false;
            av_result r = av_reduce(a, id, &no);
            a->probe_steps += r.steps;
            av_buf b = { 0 };
            if (r.status == AV_NORMAL && av_jam(a, r.term, 1u << 16, &b, NULL)) {
                if (!reqs_push(q, b)) { av_buf_free(&b); return false; }
            } else {
                av_buf_free(&b);                /* no normal form, or past the budget: no request */
            }
        }
        eff = l.field[1];
    }
    return true;
}

/*  16 fresh bytes: --entropy=FILE's from byte 16 n, n the draws logged,
 *  or getentropy's. */
static bool draw(av_pier *p, uint8_t b[AV_ENY_BYTES], const char **err) {
    if (p->eny_from_file && !p->eny_file) {
        *err = "the pier draws its bits from a file: give --entropy=FILE";
        return false;
    }
    if (!p->eny_file) {
        if (getentropy(b, AV_ENY_BYTES) != 0) { *err = "getentropy failed"; return false; }
        return true;
    }
    FILE *f = fopen(p->eny_file, "rb");
    if (!f) { *err = "cannot open the entropy file"; return false; }
    bool ok = fseeko(f, (off_t)(p->eny_n * AV_ENY_BYTES), SEEK_SET) == 0 &&
              fread(b, 1, AV_ENY_BYTES, f) == AV_ENY_BYTES;
    fclose(f);
    if (!ok) *err = "the entropy file has run out";
    return ok;
}

/*  The newest snapshot that verifies, and its event count. */
static av_arena *newest_snapshot(const char *dir, uint32_t *root, uint64_t *at) {
    DIR *d = opendir(dir);
    if (!d) return NULL;
    uint64_t *ns = NULL;
    size_t n = 0, cap = 0;
    struct dirent *e;
    while ((e = readdir(d))) {
        unsigned long long v;
        char tail;
        if (sscanf(e->d_name, "snap-%llu%c", &v, &tail) != 1) continue;
        if (n == cap) {
            uint64_t *q = realloc(ns, (cap = cap ? 2 * cap : 16) * sizeof *q);
            if (!q) break;
            ns = q;
        }
        ns[n++] = v;
    }
    closedir(d);
    av_arena *best = NULL;
    while (n && !best) {                        /* newest first */
        size_t m = 0;
        for (size_t i = 1; i < n; i++) if (ns[i] > ns[m]) m = i;
        char name[64];
        snprintf(name, sizeof name, "snap-%llu", (unsigned long long)ns[m]);
        char *path = path_in(dir, name);
        const char *err = NULL;
        best = path ? av_snapshot_load(path, root, &err) : NULL;
        free(path);
        if (best) *at = ns[m];
        ns[m] = ns[--n];
    }
    free(ns);
    return best;
}

av_pier *av_pier_open(const char *dir, const av_opts *o, const char **err) {
    av_pier *p = pier_alloc(dir, o);
    if (!p) { *err = "out of memory"; return NULL; }
    char *logp = path_in(dir, "events.log");
    if (!logp) { *err = "out of memory"; av_pier_free(p); return NULL; }
    bool missing;                               /* the lock before anything is read */
    p->log = open_log(logp, false, &missing, err);
    if (p->log < 0 && !missing) { free(logp); av_pier_free(p); return NULL; }
    uint32_t root;
    uint64_t at = 0;
    char *img = path_in(dir, "pma"), *imgnodes = path_in(dir, "pma/nodes");
    if (!img || !imgnodes) { free(img); free(imgnodes); free(logp); *err = "out of memory"; av_pier_free(p); return NULL; }
    p->pma = access(imgnodes, F_OK) == 0;
    free(imgnodes);
    if (p->pma) {
        const char *perr = NULL;
        p->a = av_pma_open(img, &root, &at, &perr);
        if (!p->a) { free(img); free(logp); *err = perr; av_pier_free(p); return NULL; }
        if (root == AV_NONE) { free(img); free(logp); *err = "the image holds no kernel"; av_pier_free(p); return NULL; }
    } else {
        p->a = newest_snapshot(dir, &root, &at);
        if (!p->a) { free(img); free(logp); *err = "no snapshot verifies"; av_pier_free(p); return NULL; }
    }
    free(img);
    av_kernel_adopt(&p->k, p->a, root, &p->o);
    p->k.events = at;
    /* A logged event is one the kernel took: it replays with no fuel limit
     * and no interrupt, whatever this run's options, and one that does not
     * reach weak head normal form stops the open; nothing logged is dropped
     * but a torn last record. */
    av_opts live = p->k.o, replay = p->o;
    replay.max_steps = UINT64_MAX / 2;
    replay.interrupt = NULL;
    p->k.o.max_steps = replay.max_steps;
    p->k.o.interrupt = NULL;

    /* an image and no log: a pier an earlier Avon made, before its first
     * event, which wrote the log after the image */
    if (p->log < 0) {
        p->log = open_log(logp, true, NULL, err);
        if (p->log < 0 || !av_sync_dir(dir)) {
            if (p->log >= 0) *err = "cannot sync the pier's directory";
            free(logp);
            av_pier_free(p);
            return NULL;
        }
    }
    FILE *in = fopen(logp, "rb");
    if (!in) { free(logp); *err = "no event log"; av_pier_free(p); return NULL; }
    char *line = NULL;
    size_t lcap = 0;
    ssize_t len;
    off_t good = 0;                             /* the end of the last whole record */
    const char *msg = NULL;
    while (!msg && (len = getline(&line, &lcap, in)) > 0) {
        if (line[len - 1] != '\n') break;       /* cut short by a crash */
        good += len;
        line[len - 1] = '\0';
        /* the checksum, if the record has one: an Avon before 2026-10-09
         * wrote none, and its records are read as they were */
        size_t ll = (size_t)len - 1;
        if (ll > 2 + SUM_HEX && line[ll - SUM_HEX - 2] == ' ' && line[ll - SUM_HEX - 1] == '=') {
            char want[SUM_HEX];
            record_sum(line, ll - SUM_HEX - 2, want);
            if (memcmp(want, line + ll - SUM_HEX, SUM_HEX) != 0) { msg = "a log record fails its checksum"; break; }
            line[ll - SUM_HEX - 2] = '\0';
        }
        char kind[8];
        unsigned long long n;
        int used;
        if (sscanf(line, "%7s %llu %n", kind, &n, &used) != 2) { msg = "a malformed log record"; break; }
        if (strcmp(kind, "entropy") == 0 && n == 0) {   /* the opt-in, and whether from a file */
            p->eny = true;
            p->eny_from_file = strcmp(line + used, "01") == 0;
            continue;
        }
        if (strcmp(kind, "eny") == 0) p->eny_n++;  /* every kept draw counts toward FILE's offset */
        if (n <= at) continue;                  /* in the snapshot already */
        if (n != p->k.events + 1) { msg = "the log skips an event"; break; }
        char *f1 = line + used, *sp = strchr(f1, ' ');
        size_t l1, l2 = 0;
        uint8_t *b1 = unhex(f1, sp ? (size_t)(sp - f1) : strlen(f1), &l1);
        uint8_t *b2 = sp ? unhex(sp + 1, strlen(sp + 1), &l2) : NULL;
        if (!b1) msg = "a malformed log record";
        else if (strcmp(kind, "poke") == 0 && !sp) {
            uint32_t ev = av_cue(p->a, b1, l1, &msg);
            uint32_t eff;
            av_result r;
            if (ev != AV_NONE && av_kernel_poke(&p->k, ev, &eff, &r) != AV_WHNF)
                msg = "a logged event does not replay";
        } else if (strcmp(kind, "eny") == 0 && b2 && l2 == AV_ENY_BYTES) {
            uint32_t ev = reply_event(p->a, b1, l1, b2, &msg);
            uint32_t eff;
            av_result r;
            if (ev != AV_NONE && av_kernel_poke(&p->k, ev, &eff, &r) != AV_WHNF)
                msg = "a logged reply does not replay";
        } else if (strcmp(kind, "load") == 0 && b2) {
            uint32_t nk = boot_term(p->a, b1, l1, b2, l2, &replay, &msg);
            if (nk != AV_NONE && !av_kernel_load(&p->k, nk)) msg = "out of memory";
        } else {
            msg = "a malformed log record";
        }
        free(b1);
        free(b2);
    }
    free(line);
    fclose(in);
    p->k.o = live;
    if (msg) { free(logp); *err = msg; av_pier_free(p); return NULL; }
    free(logp);
    off_t end = lseek(p->log, 0, SEEK_END);
    if (end < 0 || (end != good && !log_cut(p->log, good))) {
        *err = "cannot drop a torn record";
        av_pier_free(p);
        return NULL;
    }
    if (p->pma && p->k.events != at && !av_pma_commit(p->a, p->k.k, p->k.events, err)) {
        av_pier_free(p);                        /* the replayed events, committed */
        return NULL;
    }
    return p;
}

/*  Log the record (kind, a1, a2), sync, then poke with ev: the record
 *  removed again if the poke does not reach weak head normal form.  An
 *  event applied and logged is the pier's whether or not its image then
 *  commits: a failed commit is p->commit_err, beside the event, not its
 *  failure, so that no caller retries an applied event;
 *  the image's writes stay dirty, and the next commit or a reopen's
 *  replay carries them. */
static av_status poke_logged(av_pier *p, const char *kind, const uint8_t *a1, size_t n1,
                             const uint8_t *a2, size_t n2, uint32_t ev, uint32_t *effects,
                             av_result *r, bool *kept, const char **err) {
    *kept = false;
    av_root_push(p->a, &ev);
    off_t start;
    bool logged = log_record(p->log, kind, p->k.events + 1, a1, n1, a2, n2, &start);
    av_root_pop(p->a);
    if (!logged) {
        *err = "the event log cannot be written";
        r->status = AV_SIZE;
        return AV_SIZE;
    }
    av_status st = av_kernel_poke(&p->k, ev, effects, r);
    *kept = st == AV_WHNF;
    const char *cerr = NULL;
    if (st == AV_WHNF && p->pma && !av_pma_commit(p->a, p->k.k, p->k.events, &cerr))
        p->commit_err = cerr ? cerr : "the image did not commit";
    if (st != AV_WHNF) {
        /* it did not apply: it leaves the log */
        *err = "the event did not reach weak head normal form, and is not kept";
        if (!log_cut(p->log, start))
            *err = "the event did not apply, and could not be removed from the log";
    }
    return st;
}

/*  Answer the requests in q, each with its own logged reply event, and
 *  the requests the replies' effects make in turn, AV_ENY_MAX at most. */
static bool serve(av_pier *p, reqs *q, const char **err) {
    while (q->head < q->n) {
        if (p->eny_replies == AV_ENY_MAX) {
            p->eny_unanswered = q->n - q->head;
            return true;
        }
        av_buf *id = &q->ids[q->head];
        uint8_t b[AV_ENY_BYTES];
        if (!draw(p, b, err)) return false;
        uint32_t ev = reply_event(p->a, (const uint8_t *)id->s, id->len, b, err);
        if (ev == AV_NONE) return false;
        uint32_t eff;
        av_result r;
        bool kept;
        av_status st = poke_logged(p, "eny", (const uint8_t *)id->s, id->len, b, AV_ENY_BYTES, ev, &eff, &r,
                                   &kept, err);
        if (kept) p->eny_n++;                   /* logged: its bytes are spent */
        if (st != AV_WHNF) return false;
        p->eny_replies++;
        av_buf_free(id);
        q->head++;
        av_root_push(p->a, &eff);
        if (p->event_fn) p->event_fn(p->event_ctx, p->k.events, r.steps, eff, true);
        bool ok = find_requests(p, eff, q);
        av_root_pop(p->a);
        if (!ok) { *err = "out of memory"; return false; }
    }
    return true;
}

av_status av_pier_poke(av_pier *p, const uint8_t *event, size_t n, uint32_t *effects,
                       av_result *r, const char **err) {
    p->eny_replies = p->eny_unanswered = 0;
    p->eny_err = NULL;
    p->commit_err = NULL;
    p->probe_from = p->a->probe_steps;
    uint32_t ev = av_cue(p->a, event, n, err);  /* a term, or nothing is logged */
    if (ev == AV_NONE) { r->status = AV_SIZE; return AV_SIZE; }
    if (p->eny && p->eny_from_file && !p->eny_file) {
        *err = "the pier draws its bits from a file: give --entropy=FILE";
        r->status = AV_SIZE;
        return AV_SIZE;
    }
    if (p->eny) {
        /* tag 0 is the pier's: no outside event chooses a kernel's bits */
        av_opts po = probe_opts(p);
        if (!tagged_succ(p->a, ev, &po)) {
            *err = "not an event [tag data] with a tag shown nonzero; tag 0 is the pier's entropy replies'";
            r->status = AV_SIZE;
            return AV_SIZE;
        }
        /* boot's request, if a crash took its reply */
        if (p->k.events == 0 && !boot_reply(p, err)) { r->status = AV_SIZE; return AV_SIZE; }
    }
    bool kept;
    av_status st = poke_logged(p, "poke", event, n, NULL, 0, ev, effects, r, &kept, err);
    if (st != AV_WHNF) return st;
    av_root_push(p->a, effects);                /* the hook may collect */
    if (p->event_fn) p->event_fn(p->event_ctx, p->k.events, r->steps, *effects, false);
    av_root_pop(p->a);
    if (!p->eny) return st;
    /* the event is applied: a failure from here on is reported beside it,
     * not as its failure, so that no caller retries an applied event */
    reqs q = { 0 };
    const char *serr = NULL;
    av_root_push(p->a, effects);
    if (!find_requests(p, *effects, &q)) serr = "out of memory";
    else serve(p, &q, &serr);
    av_root_pop(p->a);
    reqs_free(&q);
    if (serr) p->eny_err = serr;
    return st;
}

/*  Boot's own request, [0 [0 bits]], answered unless the log holds a
 *  reply already: at boot, or on the first poke after a crash took it. */
static bool boot_reply(av_pier *p, const char **err) {
    if (p->eny_n) return true;
    av_buf zero = { 0 };
    if (!av_jam(p->a, AV_NODE_K, 16, &zero, err)) return false;
    reqs q = { 0 };
    if (!reqs_push(&q, zero)) { av_buf_free(&zero); *err = "out of memory"; return false; }
    bool ok = serve(p, &q, err);
    reqs_free(&q);
    return ok;
}

bool av_pier_entropy(av_pier *p, const char *file, const char **err) {
    if (!p->eny) { *err = "the pier was not booted with --entropy"; return false; }
    if (!file != !p->eny_from_file) {
        /* a test pier's bits never mix with the system's, nor the reverse */
        *err = p->eny_from_file ? "the pier draws its bits from a file: give --entropy=FILE"
                                : "the pier draws its bits from getentropy, not a file";
        return false;
    }
    free(p->eny_file);
    p->eny_file = NULL;
    if (file && !(p->eny_file = strdup(file))) { *err = "out of memory"; return false; }
    p->eny_replies = p->eny_unanswered = 0;
    p->eny_err = NULL;
    p->commit_err = NULL;
    p->probe_from = p->a->probe_steps;
    return p->k.events != 0 || boot_reply(p, err);
}

const char *av_pier_entropy_error(const av_pier *p) { return p->eny_err; }

const char *av_pier_commit_error(const av_pier *p) { return p->commit_err; }

void av_pier_on_event(av_pier *p, av_pier_event_fn fn, void *ctx) {
    p->event_fn = fn;
    p->event_ctx = ctx;
}

uint64_t av_pier_replies(const av_pier *p, uint64_t *unanswered) {
    if (unanswered) *unanswered = p->eny_unanswered;
    return p->eny_replies;
}

bool av_pier_load(av_pier *p, const uint8_t *pill, size_t npill, const uint8_t *subject,
                  size_t nsubject, const char **err) {
    p->commit_err = NULL;
    uint32_t nk = boot_term(p->a, pill, npill, subject, nsubject, &p->o, err);
    if (nk == AV_NONE) return false;
    av_root_push(p->a, &nk);
    off_t start;
    bool ok = log_record(p->log, "load", p->k.events + 1, pill, npill, subject, nsubject, &start);
    av_root_pop(p->a);
    if (!ok) { *err = "the event log cannot be written"; return false; }
    if (!av_kernel_load(&p->k, nk)) {           /* not applied: it leaves the log */
        *err = log_cut(p->log, start) ? "out of memory"
                                      : "out of memory, and the load could not be removed from the log";
        return false;
    }
    const char *cerr = NULL;                    /* applied: a failed commit is beside it */
    if (p->pma && !av_pma_commit(p->a, p->k.k, p->k.events, &cerr))
        p->commit_err = cerr ? cerr : "the image did not commit";
    return true;
}
