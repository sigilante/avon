/**  scry.c
 *
 *  The fact store, its resolver, and its resume loop.  The store keeps its
 *  terms in its own arena, which nothing reduces, so nothing there moves.
 *  Each attempt of the loop runs in a fresh arena:  the program's terms and
 *  the facts are copied in, the resolver is built there, and whatever outlives
 *  the attempt---a blocked path, the answer given for it---is copied back out.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "avon.h"
#include "durable.h"
#include "jets.h"

struct av_facts {
    av_arena   *a;                  /* the store's terms; never reduced */
    av_objtype  obj;
    uint32_t   *key, *ans, *path;   /* per fact: key datum, answer, key path */
    char      **render;             /* the key path, printed */
    size_t      n, cap;
    FILE       *log;
};

/*  ----------------------------------------------------------- copying */

//  The log's names:  a run's key may hold probe markers, `@N`, in
//  positions nothing reads, and a container refuses `@` names.  In the log
//  a name starting with `@` or `~` gains a `~`; on replay it loses one.
enum { AS_IS, ESCAPE, UNESCAPE };

static uint32_t leaf_named(av_arena *dst, const char *nm, int mode) {
    if (mode == ESCAPE && (nm[0] == '@' || nm[0] == '~')) {
        size_t n = strlen(nm);
        char *e = malloc(n + 2);
        if (!e) return AV_NONE;
        e[0] = '~';
        memcpy(e + 1, nm, n + 1);
        uint32_t l = av_leaf(dst, e, n + 1);
        free(e);
        return l;
    }
    if (mode == UNESCAPE && nm[0] == '~') nm++;
    return av_leaf(dst, nm, strlen(nm));
}

//  t from arena src into arena dst, sharing kept, jets looked through,
//  names as mode says.
static uint32_t copy_as(av_arena *dst, const av_arena *src, uint32_t t, int mode) {
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 256, top = 0;
    item *todo = malloc(cap * sizeof *todo);
    nmap m = { 0 };
    uint32_t out = AV_NONE;
    if (!todo) goto done;
    todo[top++] = (item){ av_view(src, t), false };
    while (top) {
        item it = todo[--top];
        uint64_t v;
        if (!it.done && nmap_get(&m, it.node, &v)) continue;
        uint32_t built;
        if (av_tag(src, it.node) == AV_LEAF) {
            built = leaf_named(dst, av_leaf_name(src, av_right(src, it.node)), mode);
        } else if (!it.done) {
            if (top + 3 > cap) {
                item *q = realloc(todo, (cap *= 2) * sizeof *q);
                if (!q) goto done;
                todo = q;
            }
            todo[top++] = (item){ it.node, true };
            todo[top++] = (item){ av_view(src, av_right(src, it.node)), false };
            todo[top++] = (item){ av_view(src, av_left(src, it.node)), false };
            continue;
        } else {
            uint64_t l, r;
            if (!nmap_get(&m, av_view(src, av_left(src, it.node)), &l) ||
                !nmap_get(&m, av_view(src, av_right(src, it.node)), &r))
                goto done;
            built = av_app(dst, (uint32_t)l, (uint32_t)r);
        }
        if (built == AV_NONE || !nmap_put(&m, it.node, built)) goto done;
    }
    uint64_t r;
    if (nmap_get(&m, av_view(src, t), &r)) out = (uint32_t)r;
done:
    free(todo);
    nmap_free(&m);
    return out;
}

static uint32_t copy_term(av_arena *dst, const av_arena *src, uint32_t t) {
    return copy_as(dst, src, t, AS_IS);
}

//  x in arena a and y in arena b are the same tree, leaves by name.
static bool same_term(const av_arena *a, uint32_t x, const av_arena *b, uint32_t y) {
    size_t cap = 256, top = 0;
    uint32_t (*st)[2] = malloc(cap * sizeof *st);
    bool same = st != NULL;
    if (same) { st[0][0] = x; st[0][1] = y; top = 1; }
    while (same && top) {
        uint32_t p = av_view(a, st[top - 1][0]), q = av_view(b, st[top - 1][1]);
        top--;
        bool pa = av_tag(a, p) == AV_APP, qa = av_tag(b, q) == AV_APP;
        if (pa != qa) { same = false; break; }
        if (!pa) {
            same = strcmp(av_leaf_name(a, av_right(a, p)), av_leaf_name(b, av_right(b, q))) == 0;
            continue;
        }
        if (top + 2 > cap) {
            uint32_t (*s2)[2] = realloc(st, (cap *= 2) * sizeof *st);
            if (!s2) { same = false; break; }
            st = s2;
        }
        st[top][0] = av_left(a, p);  st[top][1] = av_left(b, q);  top++;
        st[top][0] = av_right(a, p); st[top][1] = av_right(b, q); top++;
    }
    free(st);
    return same;
}

/*  -------------------------------------------------- bracket abstraction */

static bool is_free(const av_arena *a, uint32_t x, uint32_t t, nmap *memo) {
    t = av_view(a, t);
    uint64_t v;
    if (nmap_get(memo, t, &v)) return v != 0;
    bool f;
    if (av_tag(a, t) != AV_APP) f = t == x;
    else f = is_free(a, x, av_left(a, t), memo) || is_free(a, x, av_right(a, t), memo);
    nmap_put(memo, t, f);
    return f;
}

static uint32_t abstract(av_arena *a, uint32_t x, uint32_t body, nmap *memo) {
    body = av_view(a, body);
    if (av_tag(a, body) != AV_APP)
        return body == x ? AV_NODE_I : av_app(a, AV_NODE_K, body);
    if (!is_free(a, x, body, memo)) return av_app(a, AV_NODE_K, body);
    uint32_t e = av_view(a, av_left(a, body)), f = av_view(a, av_right(a, body));
    if (f == x && !is_free(a, x, e, memo)) return e;        /* eta */
    uint32_t ae = abstract(a, x, e, memo);
    uint32_t af = ae == AV_NONE ? AV_NONE : abstract(a, x, f, memo);
    if (af == AV_NONE) return AV_NONE;
    uint32_t s = av_app(a, AV_NODE_S, ae);
    return s == AV_NONE ? AV_NONE : av_app(a, s, af);
}

uint32_t av_abstract(av_arena *a, uint32_t x, uint32_t body) {
    nmap memo = { 0 };
    uint32_t r = abstract(a, x, body, &memo);
    nmap_free(&memo);
    return r;
}

/*  --------------------------------------------------------- the store */

static av_facts *store_new(const av_objtype *obj) {
    av_facts *f = calloc(1, sizeof *f);
    if (!f) return NULL;
    f->a = av_arena_new(1024);
    f->obj = *obj;
    if (!f->a) { free(f); return NULL; }
    return f;
}

av_facts *av_facts_new(const av_objtype *obj) {
    return store_new(obj);
}

void av_facts_free(av_facts *f) {
    if (!f) return;
    for (size_t i = 0; i < f->n; i++) free(f->render[i]);
    free(f->render);
    free(f->key);
    free(f->ans);
    free(f->path);
    if (f->log) fclose(f->log);
    av_arena_free(f->a);
    free(f);
}

size_t av_facts_count(const av_facts *f) { return f->n; }
const char *av_facts_key(const av_facts *f, size_t i) { return i < f->n ? f->render[i] : NULL; }

//  A datum's path, decoded and printed, in arena a.
static char *render_path(av_arena *a, const av_objtype *obj, uint32_t datum,
                         uint32_t *path_out) {
    av_opts o = av_opts_default();
    o.strategy = AV_COPY;
    o.no_collect = true;
    o.max_steps = 5000000;
    uint32_t t = av_decode(a, datum, obj->nctors, obj->names, obj->app, 5000000, &o, NULL);
    if (t == AV_NONE) return NULL;
    av_buf b = { 0 };
    if (!av_print(a, t, 1000000, &b)) { av_buf_free(&b); return NULL; }
    if (path_out) *path_out = t;
    return b.s;
}

//  Append without logging: the terms are copied into the store.
static bool store_put(av_facts *f, av_arena *a, uint32_t key, uint32_t answer,
                      char *render, uint32_t path, const char **err) {
    for (size_t i = 0; i < f->n; i++)
        if (strcmp(f->render[i], render) == 0) {
            free(render);
            *err = "the key is already known: the store is append-only";
            return false;
        }
    if (f->n == f->cap) {
        size_t cap = f->cap ? 2 * f->cap : 16;
        uint32_t *k = realloc(f->key, cap * sizeof *k);
        if (k) f->key = k;
        uint32_t *v = realloc(f->ans, cap * sizeof *v);
        if (v) f->ans = v;
        uint32_t *p = realloc(f->path, cap * sizeof *p);
        if (p) f->path = p;
        char **r = realloc(f->render, cap * sizeof *r);
        if (r) f->render = r;
        if (!k || !v || !p || !r) { free(render); *err = "out of memory"; return false; }
        f->cap = cap;
    }
    uint32_t ck = copy_term(f->a, a, key), ca = copy_term(f->a, a, answer);
    uint32_t cp = copy_term(f->a, a, path);
    if (ck == AV_NONE || ca == AV_NONE || cp == AV_NONE) {
        free(render);
        *err = "out of memory";
        return false;
    }
    f->key[f->n] = ck;
    f->ans[f->n] = ca;
    f->path[f->n] = cp;
    f->render[f->n] = render;
    f->n++;
    return true;
}

static bool hex_out(FILE *out, const av_buf *b) {
    for (size_t i = 0; i < b->len; i++)
        if (fprintf(out, "%02x", (unsigned char)b->s[i]) < 0) return false;
    return true;
}

//  One log record: `fact <key SKIT, hex> <answer SKIT, hex>`, written and
//  synced before the fact is used.
static bool log_fact(FILE *log, av_arena *a, uint32_t key, uint32_t answer) {
    av_buf k = { 0 }, v = { 0 };
    const char *msg = NULL;
    av_arena *e = av_arena_new(1024);             /* the names escaped */
    uint32_t ek = e ? copy_as(e, a, key, ESCAPE) : AV_NONE;
    uint32_t ev = e ? copy_as(e, a, answer, ESCAPE) : AV_NONE;
    bool ok = ek != AV_NONE && ev != AV_NONE &&
              av_jam(e, ek, 100000000, &k, &msg) && av_jam(e, ev, 100000000, &v, &msg) &&
              fputs("fact ", log) >= 0 && hex_out(log, &k) && fputc(' ', log) != EOF &&
              hex_out(log, &v) && fputc('\n', log) != EOF && fflush(log) == 0 &&
              av_sync_fd(fileno(log));
    av_buf_free(&k);
    av_buf_free(&v);
    av_arena_free(e);
    return ok;
}

bool av_facts_append(av_facts *f, av_arena *a, uint32_t key, uint32_t answer,
                     const char **err) {
    uint32_t path;
    char *render = render_path(a, &f->obj, key, &path);
    if (!render) { *err = "the key does not decode as a path"; return false; }
    for (size_t i = 0; i < f->n; i++)
        if (strcmp(f->render[i], render) == 0) {
            free(render);
            *err = "the key is already known: the store is append-only";
            return false;
        }
    if (f->log && !log_fact(f->log, a, key, answer)) {
        free(render);
        *err = "the log cannot be written";
        return false;
    }
    return store_put(f, a, key, answer, render, path, err);
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

av_facts *av_facts_open(const av_objtype *obj, const char *path, const char **err) {
    av_facts *f = store_new(obj);
    if (!f) { *err = "out of memory"; return NULL; }
    FILE *in = fopen(path, "rb");
    if (in) {
        char *line = NULL;
        size_t lcap = 0;
        ssize_t n;
        while ((n = getline(&line, &lcap, in)) > 0) {
            char *k = line + 5, *sp = strchr(k, ' '), *nl;
            if (strncmp(line, "fact ", 5) != 0 || !sp) { *err = "a malformed log record"; goto bad; }
            nl = sp + 1 + strcspn(sp + 1, "\n");
            size_t klen, vlen;
            uint8_t *kb = unhex(k, (size_t)(sp - k), &klen);
            uint8_t *vb = unhex(sp + 1, (size_t)(nl - sp - 1), &vlen);
            av_arena *scratch = av_arena_new(1024);
            av_arena *raw = av_arena_new(1024);
            uint32_t kt = kb && raw ? av_cue(raw, kb, klen, NULL) : AV_NONE;
            uint32_t vt = vb && raw ? av_cue(raw, vb, vlen, NULL) : AV_NONE;
            if (kt != AV_NONE && scratch) kt = copy_as(scratch, raw, kt, UNESCAPE);
            if (vt != AV_NONE && scratch) vt = copy_as(scratch, raw, vt, UNESCAPE);
            av_arena_free(raw);
            free(kb);
            free(vb);
            uint32_t p = AV_NONE;
            char *render = kt != AV_NONE && vt != AV_NONE ? render_path(scratch, obj, kt, &p) : NULL;
            bool ok = render && store_put(f, scratch, kt, vt, render, p, err);
            av_arena_free(scratch);
            if (!ok) { if (!render) *err = "a log record that is not a fact"; goto bad; }
        }
        free(line);
        fclose(in);
        in = NULL;
        if (0) {
bad:
            free(line);
            fclose(in);
            av_facts_free(f);
            return NULL;
        }
    }
    f->log = fopen(path, "ab");
    if (!f->log) { *err = "the log cannot be opened"; av_facts_free(f); return NULL; }
    return f;
}

/*  --------------------------------------------------------- resolvers */

uint32_t av_facts_resolver(av_arena *a, const av_facts *f, size_t n,
                           uint32_t eq, uint32_t hit, uint32_t notyet) {
    if (n > f->n) n = f->n;
    uint32_t p = av_leaf(a, "@resolver", 9);        /* the binder */
    uint32_t body = notyet;
    av_root_push(a, &eq);
    av_root_push(a, &hit);
    av_root_push(a, &body);
    for (size_t i = n; i-- > 0 && body != AV_NONE;) {  /* EQ5 p key (hit ans) rest */
        uint32_t k = copy_term(a, f->a, f->key[i]), v = copy_term(a, f->a, f->ans[i]);
        uint32_t t = k == AV_NONE || v == AV_NONE ? AV_NONE : av_app(a, eq, p);
        if (t != AV_NONE) t = av_app(a, t, k);
        uint32_t h = v == AV_NONE ? AV_NONE : av_app(a, hit, v);
        if (t != AV_NONE && h != AV_NONE) t = av_app(a, t, h);
        body = t == AV_NONE ? AV_NONE : av_app(a, t, body);
    }
    av_root_pop(a);
    av_root_pop(a);
    av_root_pop(a);
    uint32_t r = body == AV_NONE ? AV_NONE : av_abstract(a, p, body);
    if (r == AV_NONE) return AV_NONE;
    char h[27];
    uint64_t d;
    if (!av_structural_hash(a, r, h) || !av_hash_parse(h, &d)) return AV_NONE;
    uint32_t id = jet_entry_for(a, d, r, NULL);
    if (id == AV_NONE) return AV_NONE;
    a->jets[id].resolves = (uint32_t)n + 1;
    a->jets[id].admitted = 0;
    a->facts = f;
    return r;
}

//  For the interpreter jet (src/interp.c):  which of the first n facts has
//  the path `path` of arena a, whose leaves are the object type's
//  constructors (leaf[i] the i-th constructor's leaf).
//    1 with *which,
//    0 if none,
//    -1 if the path cannot be printed.
int facts_find(const av_facts *f, size_t n, av_arena *a, uint32_t path,
               const uint32_t *leaf, size_t *which) {
    /* rename the leaves to the constructors' names, as av_decode does */
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 64, top = 0;
    item *todo = malloc(cap * sizeof *todo);
    nmap m = { 0 };
    int rc = -1;
    uint32_t named = AV_NONE;
    if (!todo) goto done;
    todo[top++] = (item){ av_view(a, path), false };
    while (top) {
        item it = todo[--top];
        uint64_t v;
        if (!it.done && nmap_get(&m, it.node, &v)) continue;
        uint32_t built = AV_NONE;
        if (av_tag(a, it.node) != AV_APP) {
            for (unsigned i = 0; i < f->obj.nctors; i++)
                if (i != f->obj.app && leaf[i] == it.node)
                    built = av_leaf(a, f->obj.names[i], strlen(f->obj.names[i]));
            if (built == AV_NONE) goto done;
        } else if (!it.done) {
            if (top + 3 > cap) {
                item *q = realloc(todo, (cap *= 2) * sizeof *q);
                if (!q) goto done;
                todo = q;
            }
            todo[top++] = (item){ it.node, true };
            todo[top++] = (item){ av_view(a, av_right(a, it.node)), false };
            todo[top++] = (item){ av_view(a, av_left(a, it.node)), false };
            continue;
        } else {
            uint64_t l, r;
            if (!nmap_get(&m, av_view(a, av_left(a, it.node)), &l) ||
                !nmap_get(&m, av_view(a, av_right(a, it.node)), &r))
                goto done;
            built = av_app(a, (uint32_t)l, (uint32_t)r);
        }
        if (built == AV_NONE || !nmap_put(&m, it.node, built)) goto done;
    }
    uint64_t r;
    if (!nmap_get(&m, av_view(a, path), &r)) goto done;
    named = (uint32_t)r;
    av_buf b = { 0 };
    if (!av_print(a, named, 1000000, &b)) { av_buf_free(&b); goto done; }
    rc = 0;
    for (size_t i = 0; i < n && i < f->n; i++)
        if (strcmp(f->render[i], b.s) == 0) { *which = i; rc = 1; break; }
    av_buf_free(&b);
done:
    free(todo);
    nmap_free(&m);
    return rc;
}

/*  Fact i's answer datum, or its key path with leaf[i] leaves, in arena a. */
uint32_t facts_answer(const av_facts *f, size_t i, av_arena *a) {
    return i < f->n ? copy_term(a, f->a, f->ans[i]) : AV_NONE;
}

bool facts_same_answer(const av_facts *f, size_t i, const av_arena *a, uint32_t t) {
    return i < f->n && same_term(a, t, f->a, f->ans[i]);
}

uint32_t facts_live_path(const av_facts *f, size_t i, av_arena *a, const uint32_t *leaf) {
    if (i >= f->n) return AV_NONE;
    /* the stored path's leaves are named; map each name to its leaf */
    typedef struct { uint32_t node; bool done; } item;
    size_t cap = 64, top = 0;
    item *todo = malloc(cap * sizeof *todo);
    nmap m = { 0 };
    uint32_t out = AV_NONE;
    const av_arena *s = f->a;
    if (!todo) goto done;
    todo[top++] = (item){ f->path[i], false };
    while (top) {
        item it = todo[--top];
        uint64_t v;
        if (!it.done && nmap_get(&m, it.node, &v)) continue;
        uint32_t built = AV_NONE;
        if (av_tag(s, it.node) != AV_APP) {
            const char *nm = av_leaf_name(s, av_right(s, it.node));
            for (unsigned c = 0; c < f->obj.nctors; c++)
                if (c != f->obj.app && strcmp(f->obj.names[c], nm) == 0) built = leaf[c];
            if (built == AV_NONE) goto done;
        } else if (!it.done) {
            if (top + 3 > cap) {
                item *q = realloc(todo, (cap *= 2) * sizeof *q);
                if (!q) goto done;
                todo = q;
            }
            todo[top++] = (item){ it.node, true };
            todo[top++] = (item){ av_right(s, it.node), false };
            todo[top++] = (item){ av_left(s, it.node), false };
            continue;
        } else {
            uint64_t l, r;
            if (!nmap_get(&m, av_left(s, it.node), &l) || !nmap_get(&m, av_right(s, it.node), &r))
                goto done;
            built = av_app(a, (uint32_t)l, (uint32_t)r);
        }
        if (built == AV_NONE || !nmap_put(&m, it.node, built)) goto done;
    }
    uint64_t r;
    if (nmap_get(&m, f->path[i], &r)) out = (uint32_t)r;
done:
    free(todo);
    nmap_free(&m);
    return out;
}

/*  ------------------------------------------------------- the resume loop */

static bool push_event(av_nsrun *r, const char *fmt, const char *arg, uint64_t n) {
    char buf[1100];
    if (arg) snprintf(buf, sizeof buf, fmt, arg);
    else snprintf(buf, sizeof buf, fmt, (unsigned long long)n);
    char **e = realloc(r->events, (r->nevents + 1) * sizeof *e);
    if (!e) return false;
    r->events = e;
    return (r->events[r->nevents++] = strdup(buf)) != NULL;
}

static bool push_attempt(av_nsrun *r, uint64_t fuel, av_result res, const av_arena *a) {
    av_attempt *t = realloc(r->attempts, (r->nattempts + 1) * sizeof *t);
    if (!t) return false;
    r->attempts = t;
    r->attempts[r->nattempts++] = (av_attempt){ fuel, res.steps, a->lookups, res.status };
    return true;
}

void av_nsrun_free(av_nsrun *r) {
    for (size_t i = 0; i < r->nevents; i++) free(r->events[i]);
    free(r->events);
    free(r->attempts);
    free(r->payload);
    memset(r, 0, sizeof *r);
}

/*  One attempt: a fresh arena, the program at `fuel` over the store's
 *  facts, reduced to weak head normal form.  The arena is the caller's to
 *  free; *term is the state reached. */
static av_arena *attempt(const av_nsprog *p, const av_facts *f, av_arena_fn fresh,
                         void *actx, uint64_t fuel, const av_opts *o, av_result *res) {
    av_arena *a = fresh ? fresh(actx) : av_arena_new(1u << 16);
    if (!a) return NULL;
    uint32_t eq = copy_term(a, p->terms, p->eq), hit = copy_term(a, p->terms, p->hit);
    uint32_t notyet = copy_term(a, p->terms, p->notyet);
    uint32_t t = AV_NONE;
    if (eq != AV_NONE && hit != AV_NONE && notyet != AV_NONE) {
        uint32_t resolver = av_facts_resolver(a, f, f->n, eq, hit, notyet);
        t = resolver == AV_NONE ? AV_NONE : copy_term(a, p->terms, p->interp);
        if (t != AV_NONE) t = av_app(a, t, resolver);
        for (unsigned i = 0; i < p->nparams && t != AV_NONE; i++) {
            uint32_t q = copy_term(a, p->terms, p->params[i]);
            t = q == AV_NONE ? AV_NONE : av_app(a, t, q);
        }
        /* the numeral: suc applied fuel times to zero, as with_fuel builds */
        uint32_t n = copy_term(a, p->terms, p->zero), suc = copy_term(a, p->terms, p->suc);
        for (uint64_t i = 0; i < fuel && n != AV_NONE && suc != AV_NONE; i++) n = av_app(a, suc, n);
        uint32_t d = copy_term(a, p->terms, p->datum);
        if (t != AV_NONE && n != AV_NONE && suc != AV_NONE && d != AV_NONE) {
            t = av_app(a, t, n);
            t = t == AV_NONE ? AV_NONE : av_app(a, t, d);
        } else {
            t = AV_NONE;
        }
    }
    if (t != AV_NONE) t = av_jets_match(a, t);
    if (t == AV_NONE) { av_arena_free(a); return NULL; }
    av_opts ro = *o;
    ro.strategy = AV_COPY;
    ro.whnf_only = true;
    *res = av_reduce(a, t, &ro);
    return a;
}

bool av_ns_run(const av_nsprog *p, av_facts *f, av_resolve_fn resolve, void *rctx,
               av_arena_fn fresh, void *actx, uint64_t fuel, uint64_t start,
               uint64_t cap, unsigned max_rounds, const av_opts *o,
               const char *const *result_names, av_nsrun *out) {
    memset(out, 0, sizeof *out);
    out->ctor = -1;
    for (unsigned rnd = 1; rnd <= max_rounds; rnd++) {
        out->rounds = rnd;
        av_arena *a = NULL;
        av_result res;
        uint64_t budget = fuel;
        if (fuel == 0) {                        /* @[]: deepen, doubling */
            budget = start ? start : 1;
            for (;;) {
                a = attempt(p, f, fresh, actx, budget, o, &res);
                if (!a || !push_attempt(out, budget, res, a)) goto oom;
                if (res.status != AV_WHNF) break;
                av_peeled pe;
                av_opts po = *o;
                po.strategy = AV_COPY;
                if (!av_peel(a, res.term, p->nres, &po, &pe, NULL)) break;
                if (pe.ctor != p->timeout || budget >= cap) break;
                budget = budget * 2 < cap ? budget * 2 : cap;
                av_arena_free(a);
                a = NULL;
            }
            if (res.status == AV_WHNF && !push_event(out, "budget %llu", NULL, budget)) goto oom;
        } else {
            a = attempt(p, f, fresh, actx, budget, o, &res);
            if (!a || !push_attempt(out, budget, res, a)) goto oom;
        }
        if (res.status != AV_WHNF) {
            push_event(out, "status:%s", res.status == AV_FUEL ? "fuel" : res.status == AV_SIZE ? "size"
                       : res.status == AV_NORMAL ? "normal" : "interrupted", 0);
            av_arena_free(a);
            return true;
        }
        av_peeled pe;
        av_opts po = *o;
        po.strategy = AV_COPY;
        if (!av_peel(a, res.term, p->nres, &po, &pe, NULL)) {
            push_event(out, "%s", "no result constructor", 0);
            av_arena_free(a);
            return true;
        }
        if (pe.ctor != p->block) {
            out->ctor = (int)pe.ctor;
            if (!push_event(out, "%s", result_names[pe.ctor], 0)) { av_arena_free(a); goto oom; }
            if (pe.nfields > 0) {
                uint32_t path;
                out->payload = render_path(a, &p->obj, pe.field[0], &path);
            }
            av_arena_free(a);
            return true;
        }
        uint32_t path;
        char *key = pe.nfields == 1 ? render_path(a, &p->obj, pe.field[0], &path) : NULL;
        if (!key) {
            push_event(out, "%s", "a blocked path that does not decode", 0);
            av_arena_free(a);
            return true;
        }
        bool pushed = push_event(out, "BLOCK on %s", key, 0);
        bool known = false;
        for (size_t i = 0; i < f->n; i++)
            if (strcmp(f->render[i], key) == 0) known = true;
        uint32_t ans = known || !resolve ? AV_NONE : resolve(rctx, a, key);
        free(key);
        if (!pushed) { av_arena_free(a); goto oom; }
        const char *err = NULL;
        if (ans == AV_NONE) {
            push_event(out, "%s", "STUCK", 0);
            av_arena_free(a);
            return true;
        }
        if (!av_facts_append(f, a, pe.field[0], ans, &err)) {
            push_event(out, "STUCK: %s", err, 0);
            av_arena_free(a);
            return true;
        }
        av_arena_free(a);
    }
    push_event(out, "%s", "EXCEEDED MAX ROUNDS", 0);
    return true;
oom:
    return false;
}
