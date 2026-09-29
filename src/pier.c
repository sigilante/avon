/**  pier.c
 *
 *  A kernel's durable home (docs/DESIGN.md §19, §20.4): an event log and
 *  snapshots, in Nockchain's order -- the event appended and synced
 *  before it is applied, a snapshot's image before its sidecar -- so that
 *  reopening after a crash replays onto the newest snapshot that verifies
 *  exactly the events that were logged.
 */

#include <dirent.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#include "avon.h"

struct av_pier {
    char      *dir;
    av_arena  *a;
    av_kernel  k;
    av_opts    o;
    FILE      *log;
    bool       pma;             /* committed to a persistent arena (§19.1) */
};

static char *path_in(const char *dir, const char *name) {
    size_t n = strlen(dir) + strlen(name) + 2;
    char *p = malloc(n);
    if (p) snprintf(p, n, "%s/%s", dir, name);
    return p;
}

static bool hex_out(FILE *f, const uint8_t *b, size_t n) {
    for (size_t i = 0; i < n; i++)
        if (fprintf(f, "%02x", b[i]) < 0) return false;
    return true;
}

static uint8_t *unhex(const char *s, size_t n, size_t *len) {
    if (n % 2) return NULL;
    uint8_t *out = malloc(n / 2 + 1);
    if (!out) return NULL;
    for (size_t i = 0; i < n / 2; i++) {
        unsigned v;
        if (sscanf(s + 2 * i, "%2x", &v) != 1) { free(out); return NULL; }
        out[i] = (uint8_t)v;
    }
    *len = n / 2;
    return out;
}

/*  Append and sync one record. */
static bool log_record(FILE *log, const char *kind, uint64_t n, const uint8_t *a1, size_t n1,
                       const uint8_t *a2, size_t n2) {
    bool ok = fprintf(log, "%s %llu ", kind, (unsigned long long)n) >= 0 && hex_out(log, a1, n1);
    if (ok && a2) ok = fputc(' ', log) != EOF && hex_out(log, a2, n2);
    return ok && fputc('\n', log) != EOF && fflush(log) == 0 && fsync(fileno(log)) == 0;
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
    if (p->log) fclose(p->log);
    av_arena_free(p->a);
    free(p->dir);
    free(p);
}

static av_pier *pier_alloc(const char *dir, const av_opts *o) {
    av_pier *p = calloc(1, sizeof *p);
    if (!p) return NULL;
    p->dir = strdup(dir);
    p->o = *o;
    p->o.whnf_only = true;
    if (!p->dir) { free(p); return NULL; }
    return p;
}

static av_pier *pier_new(const char *dir, const uint8_t *pill, size_t npill,
                         const uint8_t *subject, size_t nsubject, const av_opts *o,
                         bool pma, const char **err) {
    if (mkdir(dir, 0777) != 0 && errno != EEXIST) { *err = "cannot make the pier's directory"; return NULL; }
    char *logp = path_in(dir, "events.log");
    if (!logp) { *err = "out of memory"; return NULL; }
    if (access(logp, F_OK) == 0) { free(logp); *err = "a pier is already there"; return NULL; }
    av_pier *p = pier_alloc(dir, o);
    if (!p || !(p->a = av_arena_new(1u << 16))) { free(logp); av_pier_free(p); *err = "out of memory"; return NULL; }
    uint32_t k = boot_term(p->a, pill, npill, subject, nsubject, &p->o, err);
    if (k == AV_NONE) { free(logp); av_pier_free(p); return NULL; }
    av_kernel_adopt(&p->k, p->a, k, &p->o);
    if (pma) {                                  /* the arena moves into its image */
        char *img = path_in(dir, "pma");
        p->pma = true;
        bool ok = img && av_pma_attach(p->a, img, err) &&
                  av_pma_commit(p->a, p->k.k, 0, err);
        free(img);
        if (!ok) { free(logp); av_pier_free(p); return NULL; }
    } else if (!snapshot(p, err)) {
        free(logp);
        av_pier_free(p);
        return NULL;
    }
    p->log = fopen(logp, "ab");                 /* the image first: an empty log */
    free(logp);
    if (!p->log) { *err = "cannot open the event log"; av_pier_free(p); return NULL; }
    return p;
}

av_pier *av_pier_new(const char *dir, const uint8_t *pill, size_t npill,
                     const uint8_t *subject, size_t nsubject, const av_opts *o,
                     const char **err) {
    return pier_new(dir, pill, npill, subject, nsubject, o, false, err);
}

av_pier *av_pier_new_pma(const char *dir, const uint8_t *pill, size_t npill,
                         const uint8_t *subject, size_t nsubject, const av_opts *o,
                         const char **err) {
    return pier_new(dir, pill, npill, subject, nsubject, o, true, err);
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
    uint32_t root;
    uint64_t at = 0;
    char *img = path_in(dir, "pma"), *imgnodes = path_in(dir, "pma/nodes");
    if (!img || !imgnodes) { free(img); free(imgnodes); *err = "out of memory"; av_pier_free(p); return NULL; }
    p->pma = access(imgnodes, F_OK) == 0;
    free(imgnodes);
    if (p->pma) {
        const char *perr = NULL;
        p->a = av_pma_open(img, &root, &at, &perr);
        if (!p->a) { free(img); *err = perr; av_pier_free(p); return NULL; }
        if (root == AV_NONE) { free(img); *err = "the image holds no kernel"; av_pier_free(p); return NULL; }
    } else {
        p->a = newest_snapshot(dir, &root, &at);
        if (!p->a) { free(img); *err = "no snapshot verifies"; av_pier_free(p); return NULL; }
    }
    free(img);
    av_kernel_adopt(&p->k, p->a, root, &p->o);
    p->k.events = at;

    char *logp = path_in(dir, "events.log");
    if (!logp) { *err = "out of memory"; av_pier_free(p); return NULL; }
    FILE *in = fopen(logp, "rb");
    if (!in && errno == ENOENT) {               /* a crash before the first event */
        FILE *mk = fopen(logp, "ab");
        if (mk) fclose(mk);
        in = fopen(logp, "rb");
    }
    if (!in) { free(logp); *err = "no event log"; av_pier_free(p); return NULL; }
    char *line = NULL;
    size_t lcap = 0;
    ssize_t len;
    off_t good = 0;                             /* the end of the last whole record */
    const char *msg = NULL;
    while (!msg && (len = getline(&line, &lcap, in)) > 0) {
        if (line[len - 1] != '\n') break;       /* cut short by a crash */
        off_t start = good;
        good += len;
        line[len - 1] = '\0';
        char kind[8];
        unsigned long long n;
        int used;
        if (sscanf(line, "%7s %llu %n", kind, &n, &used) != 2) { msg = "a malformed log record"; break; }
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
            if (ev != AV_NONE && av_kernel_poke(&p->k, ev, &eff, &r) != AV_WHNF) {
                /* A poke that fails is removed from the log when it fails;
                 * found last, it is one a crash left: it never applied. */
                int c = fgetc(in);
                if (c == EOF) good = start;
                else msg = "a logged event does not replay";
                free(b1);
                free(b2);
                break;
            }
        } else if (strcmp(kind, "load") == 0 && b2) {
            uint32_t nk = boot_term(p->a, b1, l1, b2, l2, &p->o, &msg);
            if (nk != AV_NONE && !av_kernel_load(&p->k, nk)) msg = "out of memory";
        } else {
            msg = "a malformed log record";
        }
        free(b1);
        free(b2);
    }
    free(line);
    fclose(in);
    if (msg) { free(logp); *err = msg; av_pier_free(p); return NULL; }
    if (truncate(logp, good) != 0) { free(logp); *err = "cannot drop a torn record"; av_pier_free(p); return NULL; }
    if (p->pma && p->k.events != at && !av_pma_commit(p->a, p->k.k, p->k.events, err)) {
        free(logp);                             /* the replayed events, committed */
        av_pier_free(p);
        return NULL;
    }
    p->log = fopen(logp, "ab");
    free(logp);
    if (!p->log) { *err = "cannot open the event log"; av_pier_free(p); return NULL; }
    return p;
}

av_status av_pier_poke(av_pier *p, const uint8_t *event, size_t n, uint32_t *effects,
                       av_result *r, const char **err) {
    uint32_t ev = av_cue(p->a, event, n, err);  /* a term, or nothing is logged */
    if (ev == AV_NONE) { r->status = AV_SIZE; return AV_SIZE; }
    long start = fseek(p->log, 0, SEEK_END) == 0 ? ftell(p->log) : -1;
    if (start < 0 || !log_record(p->log, "poke", p->k.events + 1, event, n, NULL, 0)) {
        *err = "the event log cannot be written";
        r->status = AV_SIZE;
        return AV_SIZE;
    }
    av_status st = av_kernel_poke(&p->k, ev, effects, r);
    if (st == AV_WHNF && p->pma && !av_pma_commit(p->a, p->k.k, p->k.events, err)) {
        /* applied and logged, not committed: a reopen replays it */
        return AV_SIZE;
    }
    if (st != AV_WHNF) {
        /* it did not apply: it leaves the log */
        *err = "the event did not reach weak head normal form, and is not kept";
        if (fflush(p->log) != 0 || ftruncate(fileno(p->log), start) != 0 ||
            fsync(fileno(p->log)) != 0)
            *err = "the event did not apply, and could not be removed from the log";
    }
    return st;
}

bool av_pier_load(av_pier *p, const uint8_t *pill, size_t npill, const uint8_t *subject,
                  size_t nsubject, const char **err) {
    uint32_t nk = boot_term(p->a, pill, npill, subject, nsubject, &p->o, err);
    if (nk == AV_NONE) return false;
    av_root_push(p->a, &nk);
    bool ok = log_record(p->log, "load", p->k.events + 1, pill, npill, subject, nsubject);
    av_root_pop(p->a);
    if (!ok) { *err = "the event log cannot be written"; return false; }
    if (!av_kernel_load(&p->k, nk)) { *err = "out of memory"; return false; }
    if (p->pma && !av_pma_commit(p->a, p->k.k, p->k.events, err)) return false;
    return true;
}
