/**  test_snap.c
 *
 *  Arena snapshots (docs/DESIGN.md §4.2, §19): a share-mode state with its
 *  sharing and indirections survives save and load, and reduction resumes
 *  from it to the same answer; a damaged image, a damaged or missing
 *  sidecar, and images that carry a valid checksum but a bad structure are
 *  all refused.  Writes under build/.  Run from the repository root.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "avon.h"
#include "test.h"

#define PATH "build/test_snap.img"

static char *slurp(const char *path, size_t *len) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    char *s = malloc((size_t)n + 1);
    *len = fread(s, 1, (size_t)n, f);
    fclose(f);
    return s;
}

static void spit(const char *path, const void *p, size_t n) {
    FILE *f = fopen(path, "wb");
    fwrite(p, 1, n, f);
    fclose(f);
}

static char *printed(const av_arena *a, uint32_t t) {
    av_buf b = { 0 };
    if (!av_print(a, t, 10000000, &b)) av_buf_free(&b);
    return b.s;
}

static const char *load_err(void) {
    uint32_t root;
    const char *err = NULL;
    av_arena *a = av_snapshot_load(PATH, &root, &err);
    av_arena_free(a);
    return a ? NULL : err;
}

TEST(a_reduced_state_survives_save_and_load) {
    size_t len;
    char *src = slurp("tests/fixtures/t0.ski", &len);
    CHECK(src != NULL);
    if (!src) return;
    av_arena *a = av_arena_new(0);
    uint32_t t = av_parse(a, src, len, NULL);
    av_opts o = av_opts_default();
    o.whnf_only = true;
    o.max_steps = 150;                  /* part way: the state is live work */
    av_result r = av_reduce(a, t, &o);
    CHECK_EQ(r.status, AV_FUEL);
    uint32_t root = r.term;
    const char *err = NULL;
    CHECK(av_snapshot_save(a, root, PATH, &err));
    char *before = printed(a, root);

    uint32_t root2;
    av_arena *b = av_snapshot_load(PATH, &root2, &err);
    CHECK(b != NULL);
    if (!b) { free(before); av_arena_free(a); free(src); return; }
    CHECK(b->used < a->used);           /* the graph below root, and no more */
    char *after = printed(b, root2);
    CHECK(before && after && strcmp(before, after) == 0);

    /* resume both to the normal form: the same term */
    o.whnf_only = false;
    o.max_steps = UINT64_MAX;
    av_result ra = av_reduce(a, root, &o), rb = av_reduce(b, root2, &o);
    CHECK_EQ(ra.status, AV_NORMAL);
    CHECK_EQ(rb.status, AV_NORMAL);
    CHECK_EQ(ra.steps, rb.steps);
    char *na = printed(a, ra.term), *nb = printed(b, rb.term);
    CHECK(na && nb && strcmp(na, nb) == 0);
    CHECK(na && strcmp(na, "K (S I (K (K (S (K K) K))))") == 0);
    free(before); free(after); free(na); free(nb);
    av_arena_free(a);
    av_arena_free(b);
    free(src);
}

TEST(atoms_survive_and_birds_are_refused) {
    av_arena *a = av_arena_new(0);
    uint32_t t = av_parse(a, "X1 (K X2) X1", 12, NULL);
    CHECK(av_snapshot_save(a, t, PATH, NULL));
    uint32_t r;
    av_arena *b = av_snapshot_load(PATH, &r, NULL);
    char *s = b ? printed(b, r) : NULL;
    CHECK(s && strcmp(s, "X1 (K X2) X1") == 0);
    free(s);
    av_arena_free(b);

    a->allow_bird_atoms = true;
    t = av_parse(a, "K W", 3, NULL);
    CHECK(av_snapshot_save(a, t, PATH, NULL));
    const char *e = load_err();
    CHECK(e && strstr(e, "aviary"));
    av_arena_free(a);
}

static void save_small(void) {
    av_arena *a = av_arena_new(0);
    uint32_t t = av_parse(a, "S (K X) (S I I)", 15, NULL);
    av_snapshot_save(a, t, PATH, NULL);
    av_arena_free(a);
}

TEST(damage_is_refused) {
    size_t n, ns;
    save_small();
    char *img = slurp(PATH, &n), *side = slurp(PATH ".sum", &ns);
    CHECK(load_err() == NULL);

    for (size_t i = 0; i < n; i++) {          /* every byte of the image */
        img[i] ^= 0x10;
        spit(PATH, img, n);
        CHECK(load_err() != NULL);
        img[i] ^= 0x10;
    }
    spit(PATH, img, n);
    for (size_t i = 0; i < ns; i++) {          /* every byte of the sidecar */
        side[i] ^= 0x01;
        spit(PATH ".sum", side, ns);
        CHECK(load_err() != NULL);
        side[i] ^= 0x01;
    }
    spit(PATH, img, n - 8);                    /* truncated */
    spit(PATH ".sum", side, ns);
    CHECK(load_err() != NULL);
    remove(PATH ".sum");                       /* no sidecar */
    spit(PATH, img, n);
    const char *e = load_err();
    CHECK(e && strstr(e, "sidecar"));
    free(img);
    free(side);
}

/*  Write an image of the given nodes (no atoms) and a sidecar whose
 *  checksum is valid for it, so only the structural checks stand between
 *  it and the reducer. */
static void forge(const uint32_t *nodes, uint32_t used, uint32_t root) {
    av_buf img = { 0 };
    size_t n = 16 + 8 * (size_t)used;
    img.s = calloc(1, n);
    img.len = n;
    memcpy(img.s, "AVIM\x01\0\0\0", 8);
    memcpy(img.s + 8, &used, 4);               /* the test host is little-endian */
    uint32_t leaves = 3;
    memcpy(img.s + 12, &leaves, 4);
    memcpy(img.s + 16, nodes, 8 * (size_t)used);
    uint8_t side[48], tail[8];
    memcpy(side, "AVSM\x01\0\0\0", 8);
    memcpy(side + 8, &root, 4);
    memcpy(side + 12, &used, 4);
    memcpy(tail, &root, 4);
    memcpy(tail + 4, &used, 4);
    av_sha256_ctx s;
    av_sha256_init(&s);
    av_sha256_update(&s, img.s, img.len);
    av_sha256_update(&s, tail, 8);
    av_sha256_final(&s, side + 16);
    spit(PATH, img.s, img.len);
    spit(PATH ".sum", side, sizeof side);
    free(img.s);
}

#define LEAF(id) (AV_LEAF << AV_TAG_SHIFT), (id)
#define IND(i)   ((AV_IND << AV_TAG_SHIFT) | (i)), 0

TEST(valid_checksums_on_bad_structure_are_refused) {
    const char *e;
    uint32_t good[] = { LEAF(0), LEAF(1), LEAF(2), 0, 1 };      /* S K */
    forge(good, 4, 3);
    CHECK(load_err() == NULL);

    forge(good, 4, 4);                                          /* root past end */
    e = load_err();
    CHECK(e && strstr(e, "root"));

    uint32_t cyc[] = { LEAF(0), LEAF(1), LEAF(2), 3, 4, 0, 3 };  /* 3 -> 3 */
    forge(cyc, 5, 4);
    e = load_err();
    CHECK(e && strstr(e, "cycle"));

    uint32_t indcyc[] = { LEAF(0), LEAF(1), LEAF(2), IND(4), IND(3) };
    forge(indcyc, 5, 3);
    e = load_err();
    CHECK(e && strstr(e, "cycle"));

    uint32_t twice[] = { LEAF(0), LEAF(1), LEAF(2), LEAF(1) };  /* K twice */
    forge(twice, 4, 3);
    e = load_err();
    CHECK(e && strstr(e, "interned"));

    uint32_t range[] = { LEAF(0), LEAF(1), LEAF(2), 0, 99 };
    forge(range, 4, 3);
    e = load_err();
    CHECK(e && strstr(e, "range"));

    uint32_t jet[] = { LEAF(0), LEAF(1), LEAF(2), (AV_JET << AV_TAG_SHIFT), 0 };
    forge(jet, 4, 3);
    e = load_err();
    CHECK(e && strstr(e, "jet"));

    uint32_t swapped[] = { LEAF(1), LEAF(0), LEAF(2), 0, 1 };   /* K at 0 */
    forge(swapped, 4, 3);
    CHECK(load_err() != NULL);
}

/*  An image of a term with one atom leaf, with a valid checksum: nodes
 *  as forge() takes them, leaves 0..2 S K I and 3 the atom. */
static void forge_atom(const char *atom, const uint32_t *nodes, uint32_t used,
                       uint32_t root) {
    size_t alen = strlen(atom), n = 16 + 4 + alen + 8 * (size_t)used;
    uint8_t *img = calloc(1, n);
    memcpy(img, "AVIM\x01\0\0\0", 8);
    uint32_t leaves = 4, len32 = (uint32_t)alen;
    memcpy(img + 8, &used, 4);
    memcpy(img + 12, &leaves, 4);
    memcpy(img + 16, &len32, 4);
    memcpy(img + 20, atom, alen);
    memcpy(img + 20 + alen, nodes, 8 * (size_t)used);
    uint8_t side[48], tail[8];
    memcpy(side, "AVSM\x01\0\0\0", 8);
    memcpy(side + 8, &root, 4);
    memcpy(side + 12, &used, 4);
    memcpy(tail, &root, 4);
    memcpy(tail + 4, &used, 4);
    av_sha256_ctx c;
    av_sha256_init(&c);
    av_sha256_update(&c, img, n);
    av_sha256_update(&c, tail, 8);
    av_sha256_final(&c, side + 16);
    spit(PATH, img, n);
    spit(PATH ".sum", side, sizeof side);
    free(img);
}

/*  No term in an image carries a probe or jet marker: save refuses such a
 *  graph, and the loader refuses a forged image in which any node or the
 *  root points at a marker leaf -- though it may hold one, since an arena
 *  that has probed or loaded jets interns them (a stage 4 review's
 *  finding: a planted "@x3" would alias the dashboard's marker). */
TEST(no_term_in_an_image_carries_a_marker) {
    av_arena *a = av_arena_new(0);
    uint32_t marker = av_leaf(a, "@x3", 3);
    uint32_t t = av_app(a, av_parse(a, "K X", 3, NULL), marker);
    const char *err = NULL;
    CHECK(!av_snapshot_save(a, t, PATH, &err) && err && strstr(err, "marker"));
    av_arena_free(a);

    uint32_t points[] = { LEAF(0), LEAF(1), LEAF(2), LEAF(3), 1, 3 };  /* K @x3 */
    forge_atom("@x3", points, 5, 4);
    const char *e = load_err();
    CHECK(e && strstr(e, "marker"));
    forge_atom("@x3", points, 5, 3);                  /* the root itself */
    e = load_err();
    CHECK(e && strstr(e, "marker"));
    uint32_t holds[] = { LEAF(0), LEAF(1), LEAF(2), LEAF(3), 1, 0 };   /* K S */
    forge_atom("@x3", holds, 5, 4);
    CHECK(load_err() == NULL);
}

TEST_MAIN(
    TEST_CASE(a_reduced_state_survives_save_and_load),
    TEST_CASE(atoms_survive_and_birds_are_refused),
    TEST_CASE(damage_is_refused),
    TEST_CASE(valid_checksums_on_bad_structure_are_refused),
    TEST_CASE(no_term_in_an_image_carries_a_marker),
)
