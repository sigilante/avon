/**  test_cli.c
 *
 *  The command line's exit codes (AUDIT.md item 15), run on build/dbg/avon,
 *  which `make check` builds first.  A run's status is its line's: FUEL
 *  and SIZE exit 0.  A failure of Avon's own exits 1: output that could not
 *  be written, or a term that does not parse.
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
    snprintf(cmd, sizeof cmd, AVON " reduce %s >&- 2>/dev/null", path);
    CHECK_EQ(run(cmd, out, sizeof out), 1);
    snprintf(cmd, sizeof cmd, "printf 'I X\\nK X Foo\\n' | " AVON " batch >&- 2>/dev/null");
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

TEST_MAIN(
    TEST_CASE(a_status_is_the_line_s_and_exits_0),
    TEST_CASE(output_that_cannot_be_written_exits_1),
    TEST_CASE(a_term_that_does_not_parse_exits_1),
)
