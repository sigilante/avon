/**  test_cli.c
 *
 *  The command line's exit codes, run on build/dbg/avon, which `make
 *  check` builds first.  A run's status is its line's: FUEL and SIZE exit
 *  0.  A failure of Avon's own exits 1: output that could not be written,
 *  or a term that does not parse.  --pins reads its file's kinds and
 *  terms, each path relative to the file, and refuses a bad file or a
 *  kind given twice with exit 1.
 */

#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#include "test.h"

#define AVON "build/dbg/avon"

static char dir[] = "/tmp/avon-cli-XXXXXX";

/*  Run sh -c cmd, the start of its stdout into out, the rest read and
 *  dropped so that it never writes to a closed pipe; its exit code, or -1. */
static int run(const char *cmd, char *out, size_t cap) {
    FILE *f = popen(cmd, "r");
    if (!f) return -1;
    size_t n = fread(out, 1, cap - 1, f);
    out[n] = '\0';
    char rest[4096];
    while (fread(rest, 1, sizeof rest, f) > 0) {}
    int st = pclose(f);
    return WIFEXITED(st) ? WEXITSTATUS(st) : -1;
}

static void teardown(void) {
    char cmd[128];
    snprintf(cmd, sizeof cmd, "/bin/rm -rf %s", dir);
    if (system(cmd) != 0) fprintf(stderr, "test_cli: cannot remove %s\n", dir);
}

/*  A file of src in the scratch directory, made on first use. */
static void term(const char *name, const char *src, char *path, size_t cap) {
    static bool made = false;
    if (!made) {
        REQUIRE(mkdtemp(dir) != NULL);
        REQUIRE(access(AVON, X_OK) == 0);
        atexit(teardown);
        made = true;
    }
    snprintf(path, cap, "%s/%s", dir, name);
    FILE *f = fopen(path, "w");
    REQUIRE(f != NULL);
    fputs(src, f);
    fclose(f);
}

TEST(a_status_is_the_line_s_and_exits_0) {
    char path[128], cmd[512], out[4096];
    term("loop", "S I I (S I I)\n", path, sizeof path);
    snprintf(cmd, sizeof cmd, AVON " reduce --fuel=100 %s", path);
    CHECK_EQ(run(cmd, out, sizeof out), 0);
    CHECK(strncmp(out, "FUEL 100", 8) == 0);
    term("grow", "S I I (S (K (S I I)) (S (S (K S) K) (K (S I I))))\n", path, sizeof path);
    snprintf(cmd, sizeof cmd, AVON " reduce --max-nodes=1000 %s", path);
    CHECK_EQ(run(cmd, out, sizeof out), 0);
    CHECK(strncmp(out, "SIZE ", 5) == 0);
    term("id", "I X\n", path, sizeof path);
    snprintf(cmd, sizeof cmd, AVON " reduce %s", path);
    CHECK_EQ(run(cmd, out, sizeof out), 0);
    CHECK(strcmp(out, "NORMAL 1\nX\n") == 0);
}

TEST(output_that_cannot_be_written_exits_1) {
    char path[128], cmd[512], out[4096];
    term("id", "I X\n", path, sizeof path);
    /* stdout open read-only, so every write fails: a closed stdout would be
     * reused by the first file the process opens, sanitizer runtimes
     * included, and the write might land there */
    snprintf(cmd, sizeof cmd, AVON " reduce %s 1</dev/null 2>/dev/null", path);
    CHECK_EQ(run(cmd, out, sizeof out), 1);
    snprintf(cmd, sizeof cmd, "printf 'I X\\nK X Foo\\n' | " AVON " batch 1</dev/null 2>/dev/null");
    CHECK_EQ(run(cmd, out, sizeof out), 1);
    snprintf(cmd, sizeof cmd, "printf 'I X\\nK X Foo\\n' | " AVON " batch");
    CHECK_EQ(run(cmd, out, sizeof out), 0);
}

TEST(a_term_that_does_not_parse_exits_1) {
    char path[128], cmd[512], out[4096];
    term("bad", "S (K\n", path, sizeof path);
    snprintf(cmd, sizeof cmd, AVON " reduce %s 2>/dev/null", path);
    CHECK_EQ(run(cmd, out, sizeof out), 1);
    term("dag", "dag 0=S 1=a(b 2=0.1 @2\n", path, sizeof path);
    snprintf(cmd, sizeof cmd, AVON " reduce %s 2>/dev/null", path);
    CHECK_EQ(run(cmd, out, sizeof out), 1);
}

/*  batch --dag answers every line, in order: a term it cannot read is `!`. */
TEST(batch_dag_answers_every_line) {
    char cmd[512], out[4096];
    snprintf(cmd, sizeof cmd, "printf 'S K K x\\nS (K\\nK a b\\n' | " AVON " batch --dag 2>/dev/null");
    CHECK_EQ(run(cmd, out, sizeof out), 1);
    CHECK(strcmp(out, "NORMAL 2 dag 0=x @0\n!\nNORMAL 1 dag 0=a @0\n") == 0);
    if (strcmp(out, "NORMAL 2 dag 0=x @0\n!\nNORMAL 1 dag 0=a @0\n") != 0)
        fprintf(stderr, "  got: %s", out);
}

TEST(pins_reads_its_file_and_refuses_a_bad_one) {
    char path[128], conf[160], cmd[1024], out[4096], cwd[512];
    REQUIRE(getcwd(cwd, sizeof cwd) != NULL);
    term("skk", "S K K x\n", path, sizeof path);
    /* the checkout's jets/pins.conf: every term loads, none occurs */
    snprintf(cmd, sizeof cmd, AVON " reduce --pins %s 2>&1", path);
    CHECK_EQ(run(cmd, out, sizeof out), 0);
    CHECK(strstr(out, "pins: no pinned term occurs in the term (p2 nock-dec hoon-dec)") != NULL);
    /* a term file relative to the file naming it */
    snprintf(cmd, sizeof cmd, "ln -s %s/jets/pins/jetT-hoonDecBodyF.dag %s/hd.dag", cwd, dir);
    REQUIRE(system(cmd) == 0);
    term("one.conf", "# Hoon's ++dec only\nhoon-dec  hd.dag\n", conf, sizeof conf);
    snprintf(cmd, sizeof cmd, AVON " reduce --pins=%s %s 2>&1", conf, path);
    CHECK_EQ(run(cmd, out, sizeof out), 0);
    CHECK(strstr(out, "(hoon-dec)") != NULL);
    term("bad.conf", "hoon-dec\n", conf, sizeof conf);
    snprintf(cmd, sizeof cmd, AVON " reduce --pins=%s %s 2>&1", conf, path);
    CHECK_EQ(run(cmd, out, sizeof out), 1);
    CHECK(strstr(out, ":1: a line is KIND and one TERM-FILE") != NULL);
    term("kind.conf", "dec x.dag\n", conf, sizeof conf);
    snprintf(cmd, sizeof cmd, AVON " reduce --pins=%s %s 2>&1", conf, path);
    CHECK_EQ(run(cmd, out, sizeof out), 1);
    CHECK(strstr(out, "not a pinned jet's kind") != NULL);
    term("gone.conf", "nock-dec missing.dag\n", conf, sizeof conf);
    snprintf(cmd, sizeof cmd, AVON " reduce --pins=%s %s 2>&1", conf, path);
    CHECK_EQ(run(cmd, out, sizeof out), 1);
    CHECK(strstr(out, "missing.dag: cannot open") != NULL);
    snprintf(cmd, sizeof cmd, AVON " reduce --pins --p2=x %s 2>&1", path);
    CHECK_EQ(run(cmd, out, sizeof out), 1);
    CHECK(strstr(out, "p2 given twice") != NULL);
    /* hoon-dec names two terms at most: the licensed jetT and the bare arm */
    term("two.conf", "hoon-dec hd.dag\nhoon-dec hd.dag\n", conf, sizeof conf);
    snprintf(cmd, sizeof cmd, AVON " reduce --pins=%s %s 2>&1", conf, path);
    CHECK_EQ(run(cmd, out, sizeof out), 0);
    term("three.conf", "hoon-dec hd.dag\nhoon-dec hd.dag\nhoon-dec hd.dag\n", conf, sizeof conf);
    snprintf(cmd, sizeof cmd, AVON " reduce --pins=%s %s 2>&1", conf, path);
    CHECK_EQ(run(cmd, out, sizeof out), 1);
    CHECK(strstr(out, "hoon-dec given twice") != NULL);
    /* skinock's whole program, its bare arm fired once its core is reduced */
    snprintf(cmd, sizeof cmd, AVON " reduce --pins tests/data/hoon-dec/hoon_dec_7.dag 2>&1");
    CHECK_EQ(run(cmd, out, sizeof out), 0);
    CHECK(strstr(out, "(jetT 0, bare 1); 1 decrements run natively") != NULL);
    CHECK(strstr(out, "NORMAL 1011\n") != NULL);
}

TEST_MAIN(
    TEST_CASE(pins_reads_its_file_and_refuses_a_bad_one),
    TEST_CASE(a_status_is_the_line_s_and_exits_0),
    TEST_CASE(output_that_cannot_be_written_exits_1),
    TEST_CASE(a_term_that_does_not_parse_exits_1),
    TEST_CASE(batch_dag_answers_every_line),
)
