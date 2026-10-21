/**  test_wire.c
 *
 *  The wire format's acceptance: SHA-256 against the standard's vectors;
 *  the bitstring's codes; print(parse(s)) == s and cue(jam(t)) == t on
 *  every corpus term and on reduced states; hygiene; and cue on hostile
 *  bytes, which must never crash and must reject cleanly or decode to a
 *  term that jams back to the same bytes.  Run from the repository root.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "avon.h"
#include "test.h"

static void hex(const uint8_t *d, char *out) {
    for (int i = 0; i < 32; i++) snprintf(out + 2 * i, 3, "%02x", d[i]);
}

TEST(sha256_matches_the_standard) {
    uint8_t d[32];
    char h[65];
    av_sha256("", 0, d);
    hex(d, h);
    CHECK(strcmp(h, "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855") == 0);
    av_sha256("abc", 3, d);
    hex(d, h);
    CHECK(strcmp(h, "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad") == 0);
    const char *m = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    av_sha256(m, strlen(m), d);
    hex(d, h);
    CHECK(strcmp(h, "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1") == 0);
    av_sha256_ctx s;                     /* a million 'a', fed unevenly */
    av_sha256_init(&s);
    char as[1001];
    memset(as, 'a', sizeof as);
    for (int i = 0; i < 1000; i++) av_sha256_update(&s, as, i % 2 ? 999 : 1001);
    av_sha256_final(&s, d);
    hex(d, h);
    CHECK(strcmp(h, "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0") == 0);
}

/*  jam the printed form src; return the bitstring's bits as a "0101" string */
static char *bits_of(const char *src) {
    av_arena *a = av_arena_new(0);
    uint32_t t = av_parse(a, src, strlen(src), NULL);
    av_buf b = { 0 };
    const char *err;
    char *out = NULL;
    if (av_jam(a, t, 1000, &b, &err)) {
        const uint8_t *p = (const uint8_t *)b.s;
        size_t pos = 8;
        uint32_t natoms = p[pos] | p[pos + 1] << 8;
        pos += 4;
        for (uint32_t k = 0; k < natoms; k++) pos += 4 + (p[pos] | (size_t)p[pos + 1] << 8);
        uint64_t nbits = 0;
        for (int i = 0; i < 8; i++) nbits |= (uint64_t)p[pos + (size_t)i] << (8 * i);
        pos += 8;
        out = malloc(nbits + 1);
        for (uint64_t i = 0; i < nbits; i++)
            out[i] = (char)('0' + (p[pos + i / 8] >> (i % 8) & 1));
        out[nbits] = '\0';
    }
    av_buf_free(&b);
    av_arena_free(a);
    return out;
}

static int bits_are(const char *src, const char *want) {
    char *got = bits_of(src);
    int ok = got && strcmp(got, want) == 0;
    if (!ok) fprintf(stderr, "  %s: got %s, want %s\n", src, got ? got : "(none)", want);
    free(got);
    return ok;
}

TEST(the_codes_are_tromps_with_a_third_leaf) {
    CHECK(bits_are("S", "00"));
    CHECK(bits_are("K", "01"));
    CHECK(bits_are("I", "10"));
    CHECK(bits_are("S K", "110001"));
    CHECK(bits_are("S (K I)", "1100110110"));
    /* one atom: width 1, so I is 10 0 and the atom 10 1 */
    CHECK(bits_are("I X", "11100101"));
    /* two atoms: width 2, indices least significant bit first */
    CHECK(bits_are("X Z I", "1111101010011000"));
}

/*  --------------------------------------------------- the corpus, all of it */

typedef struct { char *text; char **line; size_t n; } corpus;

static corpus load_corpus(void) {
    corpus c = { NULL, NULL, 0 };
    FILE *f = test_open("tests/fixtures/corpus.tsv");
    fseek(f, 0, SEEK_END);
    size_t len = (size_t)ftell(f);
    fseek(f, 0, SEEK_SET);
    c.text = malloc(len + 1);
    len = fread(c.text, 1, len, f);
    c.text[len] = '\0';
    fclose(f);
    for (size_t i = 0; i < len; i++) if (c.text[i] == '\n') c.n++;
    c.line = malloc(c.n * sizeof *c.line);
    size_t k = 0;
    for (char *p = c.text; k < c.n; k++) {
        char *nl = strchr(p, '\n');
        *nl = '\0';
        char *term = strrchr(p, '\t') + 1;        /* program, name, term */
        c.line[k] = term;
        p = nl + 1;
    }
    return c;
}

static void free_corpus(corpus *c) {
    free(c->text);
    free(c->line);
}

static int jam_cue_print(av_arena *a, uint32_t t, const char *want) {
    av_buf j = { 0 }, p = { 0 }, j2 = { 0 };
    const char *err = NULL;
    int ok = av_jam(a, t, 100000000, &j, &err);
    av_arena *b = av_arena_new(0);
    uint32_t u = ok ? av_cue(b, (const uint8_t *)j.s, j.len, &err) : AV_NONE;
    ok = ok && u != AV_NONE && av_print(b, u, 100000000, &p) &&
         strcmp(p.s, want) == 0 &&
         av_jam(b, u, 100000000, &j2, &err) &&           /* canonical */
         j2.len == j.len && memcmp(j2.s, j.s, j.len) == 0;
    if (!ok) fprintf(stderr, "  round trip failed%s%s\n", err ? ": " : "", err ? err : "");
    av_buf_free(&j);
    av_buf_free(&p);
    av_buf_free(&j2);
    av_arena_free(b);
    return ok;
}

TEST(every_corpus_term_round_trips) {
    corpus c = load_corpus();
    CHECK(c.n == 285);
    for (size_t i = 0; i < c.n; i++) {
        const char *s = c.line[i];
        av_arena *a = av_arena_new(0);
        uint32_t t = av_parse(a, s, strlen(s), NULL);
        av_buf p = { 0 };
        CHECK(t != AV_NONE && av_print(a, t, 100000000, &p) && strcmp(p.s, s) == 0);
        CHECK(jam_cue_print(a, t, s));
        av_buf_free(&p);
        av_arena_free(a);
    }
    free_corpus(&c);
}

TEST(reduced_states_round_trip) {
    /* Each corpus term reduced a little, in both strategies: the states
     * carry sharing and, in share mode, indirections, which jam unfolds. */
    corpus c = load_corpus();
    size_t checked = 0;
    for (size_t i = 0; i < c.n; i++) {
        for (int st = 0; st < 2; st++) {
            av_arena *a = av_arena_new(0);
            uint32_t t = av_parse(a, c.line[i], strlen(c.line[i]), NULL);
            av_opts o = av_opts_default();
            o.strategy = st ? AV_SHARE : AV_COPY;
            o.max_steps = 200;
            av_result r = av_reduce(a, t, &o);
            av_buf p = { 0 };
            if (r.term != AV_NONE && av_print(a, r.term, 200000, &p)) {
                CHECK(jam_cue_print(a, r.term, p.s));
                checked++;
            }
            av_buf_free(&p);
            av_arena_free(a);
        }
    }
    CHECK(checked > c.n);
    free_corpus(&c);
}

TEST(atoms_round_trip_in_first_met_order) {
    av_arena *a = av_arena_new(0);
    const char *s = "X2 (S X1) (K X2 X3) (I X1)";
    uint32_t t = av_parse(a, s, strlen(s), NULL);
    CHECK(jam_cue_print(a, t, s));
    av_buf j = { 0 };
    CHECK(av_jam(a, t, 1000, &j, NULL));
    CHECK(memcmp(j.s + 12, "\2\0\0\0X2", 6) == 0);  /* X2 is met first */
    av_buf_free(&j);
    av_arena_free(a);
}

TEST(bird_named_atoms_are_refused) {
    av_arena *a = av_arena_new(0);
    av_parse_error e = { 0, NULL };
    CHECK(av_parse(a, "S (K B)", 7, &e) == AV_NONE);
    CHECK_EQ(e.pos, 5);
    CHECK(av_parse(a, "Y", 1, NULL) == AV_NONE);
    CHECK(av_parse(a, "\xce\xa6", 2, NULL) == AV_NONE);      /* Φ */
    CHECK(av_parse(a, "Bx", 2, NULL) != AV_NONE);             /* not a bird */
    a->allow_bird_atoms = true;
    CHECK(av_parse(a, "S (K B)", 7, NULL) != AV_NONE);
    CHECK(av_is_bird("Theta", 5));
    CHECK(!av_is_bird("S", 1));

    /* and in a container */
    uint32_t t = av_parse(a, "K W", 3, NULL);
    av_buf j = { 0 };
    CHECK(av_jam(a, t, 100, &j, NULL));
    av_arena *b = av_arena_new(0);
    const char *err = NULL;
    CHECK(av_cue(b, (const uint8_t *)j.s, j.len, &err) == AV_NONE && err);
    b->allow_bird_atoms = true;
    CHECK(av_cue(b, (const uint8_t *)j.s, j.len, NULL) != AV_NONE);
    av_buf_free(&j);
    av_arena_free(b);
    av_arena_free(a);
}

/*  ------------------------------------------------------ hostile input */

static const char *cue_err(const uint8_t *p, size_t n) {
    av_arena *a = av_arena_new(0);
    const char *err = NULL;
    uint32_t t = av_cue(a, p, n, &err);
    av_arena_free(a);
    return t == AV_NONE ? (err ? err : "(no message)") : NULL;
}

TEST(malformed_containers_are_rejected) {
    /* "S K": 6 bits 110001 -> byte 0x23 */
    uint8_t ok[] = { 'S','K','I','T', 1,0,0,0, 0,0,0,0, 6,0,0,0,0,0,0,0, 0x23 };
    CHECK(cue_err(ok, sizeof ok) == NULL);
    uint8_t m[sizeof ok];
#define MUTATE(i, v) (memcpy(m, ok, sizeof ok), m[i] = (v), cue_err(m, sizeof ok))
    CHECK(MUTATE(0, 'X') != NULL);            /* magic */
    CHECK(MUTATE(4, 2) != NULL);              /* version */
    CHECK(MUTATE(5, 1) != NULL);              /* reserved */
    CHECK(MUTATE(12, 5) != NULL);             /* bit count short: truncated */
    CHECK(MUTATE(12, 8) != NULL);             /* bits after the term */
    CHECK(MUTATE(20, 0x63) != NULL);          /* padding not zero */
    CHECK(MUTATE(8, 1) != NULL);              /* atom table past the end */
    CHECK(MUTATE(19, 0x80) != NULL);          /* absurd bit count */
#undef MUTATE
    CHECK(cue_err(ok, sizeof ok - 1) != NULL); /* truncated */
    CHECK(cue_err(ok, 0) != NULL);

    /* an atom table naming an unused atom, or out of first-met order */
    const char *e;
    uint8_t unused[] = { 'S','K','I','T', 1,0,0,0, 1,0,0,0, 1,0,0,0,'X',
                         3,0,0,0,0,0,0,0, 0x01 };           /* "I": 10 0 */
    e = cue_err(unused, sizeof unused);
    CHECK(e && strstr(e, "unused"));
    /* table [X, Z], term "Z X": 11 1001 1010, so Z (index 2) is met first */
    uint8_t order[] = { 'S','K','I','T', 1,0,0,0, 2,0,0,0,
                        1,0,0,0,'X', 1,0,0,0,'Z',
                        10,0,0,0,0,0,0,0, 0x67, 0x01 };
    e = cue_err(order, sizeof order);
    CHECK(e && strstr(e, "first-met order"));
    /* canonical: table [Z, X], bits 11 1010 1001 */
    order[16] = 'Z'; order[21] = 'X'; order[30] = 0x57; order[31] = 0x02;
    CHECK(cue_err(order, sizeof order) == NULL);
    uint8_t dup[] = { 'S','K','I','T', 1,0,0,0, 2,0,0,0,
                      1,0,0,0,'X', 1,0,0,0,'X',
                      10,0,0,0,0,0,0,0, 0x67, 0x01 };
    e = cue_err(dup, sizeof dup);
    CHECK(e && strstr(e, "duplicate"));
    /* one atom "@0", term I @0 would be 11 100 101: refused by name */
    uint8_t marker[] = { 'S','K','I','T', 1,0,0,0, 1,0,0,0, 2,0,0,0,'@','0',
                         8,0,0,0,0,0,0,0, 0xa7 };
    e = cue_err(marker, sizeof marker);
    CHECK(e && strstr(e, "invalid atom name"));
    uint8_t named_s[] = { 'S','K','I','T', 1,0,0,0, 1,0,0,0, 1,0,0,0,'S',
                          4,0,0,0,0,0,0,0, 0x05 };
    e = cue_err(named_s, sizeof named_s);
    CHECK(e && strstr(e, "invalid atom name"));
}

static uint64_t rng = 0x243f6a8885a308d3u;
static uint32_t next(void) {
    rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
    return (uint32_t)(rng >> 32);
}

/* cue(x) either refuses, or decodes to t with jam(t) == x exactly. */
static void cue_is_clean(const uint8_t *p, size_t n, size_t *accepted) {
    av_arena *a = av_arena_new(0);
    const char *err = NULL;
    uint32_t t = av_cue(a, p, n, &err);
    if (t == AV_NONE) {
        CHECK(err != NULL);
    } else {
        av_buf j = { 0 };
        CHECK(av_jam(a, t, 1u << 24, &j, NULL));
        CHECK(j.len == n && memcmp(j.s, p, n) == 0);
        av_buf_free(&j);
        (*accepted)++;
    }
    av_arena_free(a);
}

TEST(cue_never_crashes_and_is_bijective) {
    int cases = getenv("AVON_FUZZ") ? atoi(getenv("AVON_FUZZ")) : 20000;
    size_t accepted = 0;
    uint8_t buf[64];

    /* mutants of valid containers: most of the interesting damage */
    corpus c = load_corpus();
    REQUIRE(c.n >= 40);
    for (int i = 0; i < cases; i++) {
        const char *s = c.line[next() % 40];
        av_arena *a = av_arena_new(0);
        uint32_t t = av_parse(a, s, strlen(s), NULL);
        av_buf j = { 0 };
        av_jam(a, t, 1u << 24, &j, NULL);
        av_arena_free(a);
        int flips = 1 + (int)(next() % 3);
        for (int f = 0; f < flips; f++) {
            size_t at = next() % j.len;
            switch (next() % 3) {
            case 0: j.s[at] ^= (char)(1u << (next() % 8)); break;
            case 1: j.s[at] = (char)next(); break;
            case 2: j.len = at + 1; break;            /* truncate */
            }
        }
        cue_is_clean((const uint8_t *)j.s, j.len, &accepted);
        av_buf_free(&j);
    }
    free_corpus(&c);

    /* and noise behind a valid header */
    for (int i = 0; i < cases; i++) {
        size_t n = 8 + next() % (sizeof buf - 8);
        memcpy(buf, "SKIT\1\0\0\0", 8);
        for (size_t k = 8; k < n; k++) buf[k] = (uint8_t)next();
        if (next() % 2) memset(buf + 8, 0, 4);        /* often no atoms */
        cue_is_clean(buf, n, &accepted);
    }
    CHECK(accepted > 0);
}

/*  Atoms are interned through a hash index: names that share a prefix
 *  are distinct, a name is found again, a NUL is refused, a refused
 *  container interns nothing, and a hundred thousand atoms cue in linear
 *  time, where a scan per name took minutes. */
TEST(interning_is_a_probe) {
    av_arena *a = av_arena_new(0);
    uint32_t x = av_leaf(a, "ab", 2), y = av_leaf(a, "a", 1), z = av_leaf(a, "abc", 3);
    CHECK(x != AV_NONE && y != AV_NONE && z != AV_NONE);
    CHECK(x != y && y != z && x != z);
    CHECK_EQ(av_leaf(a, "ab", 2), x);
    CHECK_EQ(av_leaf(a, "abc", 2), x);                   /* a length, not a terminator */
    CHECK_EQ(av_leaf(a, "S", 1), AV_NODE_S);
    CHECK_EQ(av_leaf(a, "a\0b", 3), AV_NONE);
    uint32_t before = a->n_leaves;
    /* table [fresh, @x]: the second name is refused, and fresh is not interned */
    uint8_t bad[] = { 'S','K','I','T', 1,0,0,0, 2,0,0,0,
                      5,0,0,0,'f','r','e','s','h', 2,0,0,0,'@','x',
                      10,0,0,0,0,0,0,0, 0x67, 0x01 };
    const char *err = NULL;
    CHECK_EQ(av_cue(a, bad, sizeof bad, &err), AV_NONE);
    CHECK_EQ(a->n_leaves, before);
    av_arena_free(a);

    enum { N = 100000 };
    av_arena *b = av_arena_new(0);
    uint32_t t = AV_NODE_I;
    char nm[16];
    for (int i = 0; i < N; i++) {
        int len = snprintf(nm, sizeof nm, "x%d", i);
        t = av_app(b, t, av_leaf(b, nm, (size_t)len));
    }
    REQUIRE(t != AV_NONE);
    av_buf j = { 0 };
    REQUIRE(av_jam(b, t, 1u << 24, &j, NULL));
    av_arena *c = av_arena_new(0);
    clock_t c0 = clock();
    uint32_t u = av_cue(c, (const uint8_t *)j.s, j.len, &err);
    double secs = (double)(clock() - c0) / CLOCKS_PER_SEC;
    printf("  %d atoms cued in %.2f s\n", N, secs);
    CHECK(u != AV_NONE);
    CHECK_EQ(c->n_leaves, SKI_ATOM_FIRST + N);
    CHECK(secs < 30);
    av_buf_free(&j);
    av_arena_free(b);
    av_arena_free(c);
}

TEST_MAIN(
    TEST_CASE(sha256_matches_the_standard),
    TEST_CASE(the_codes_are_tromps_with_a_third_leaf),
    TEST_CASE(every_corpus_term_round_trips),
    TEST_CASE(reduced_states_round_trip),
    TEST_CASE(atoms_round_trip_in_first_met_order),
    TEST_CASE(bird_named_atoms_are_refused),
    TEST_CASE(malformed_containers_are_rejected),
    TEST_CASE(cue_never_crashes_and_is_bijective),
    TEST_CASE(interning_is_a_probe),
)
