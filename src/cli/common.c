/**  common.c
 *
 *  What the commands read with: a decimal number, a whole file, and a term in
 *  any of its forms.
 */

#include "cli.h"

/*  A decimal number, digits only: strtoull alone would take a sign or
 *  leading space, and wrap -1 to 2^64-1. */
bool number(const char *s, uint64_t *out) {
    char *end;
    if (*s < '0' || *s > '9') return false;
    errno = 0;
    unsigned long long v = strtoull(s, &end, 10);
    if (errno || end == s || *end) return false;
    *out = v;
    return true;
}

char *slurp(FILE *f, size_t *len) {
    size_t cap = 1 << 16, n = 0;
    char *s = malloc(cap);
    if (!s) return NULL;
    for (;;) {
        n += fread(s + n, 1, cap - n, f);
        if (n < cap) break;
        char *p = realloc(s, cap *= 2);
        if (!p) { free(s); return NULL; }
        s = p;
    }
    s[n] = '\0';                        /* n < cap: callers read it as a string */
    *len = n;
    return s;
}

/* A term from either format; reports its own errors. */
uint32_t load(av_arena *a, const char *src, size_t len) {
    size_t lead = 0;
    while (lead < len && (src[lead] == ' ' || src[lead] == '\n' ||
                          src[lead] == '\r' || src[lead] == '\t'))
        lead++;
    if (lead < len && src[lead] == '`') {
        const char *msg = NULL;
        uint32_t t = av_parse_prefix(a, src, len, &msg);
        if (t == AV_NONE) fprintf(stderr, "avon: bad prefix term: %s\n", msg);
        return t;
    }
    if (len - lead >= 4 && memcmp(src + lead, "dag ", 4) == 0) {
        const char *msg = NULL;
        uint32_t t = av_parse_dag(a, src + lead, len - lead, &msg);
        if (t == AV_NONE) fprintf(stderr, "avon: bad dag term: %s\n", msg);
        return t;
    }
    if (len >= 4 && memcmp(src, "SKIT", 4) == 0) {
        const char *msg = NULL;
        uint32_t t = av_cue(a, (const uint8_t *)src, len, &msg);
        if (t == AV_NONE) fprintf(stderr, "avon: bad container: %s\n", msg);
        return t;
    }
    av_parse_error err = { 0, NULL };
    uint32_t t = av_parse(a, src, len, &err);
    if (t == AV_NONE)
        fprintf(stderr, "avon: parse error at %zu: %s\n", err.pos, err.msg);
    return t;
}
