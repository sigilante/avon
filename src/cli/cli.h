/**  cli.h
 *
 *  Internal to the avon command: what its commands share, and each one's
 *  entry point.  main.c dispatches on the command's name; each command
 *  is a file of src/cli.  Include it first: it sets the POSIX level the
 *  system headers read.
 */

#ifndef CLI_H
#define CLI_H

#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "avon.h"

/*  A command's arena starts with room for this many nodes, and grows. */
#define ARENA_START (1u << 16)

/*  main.c: the usage message, on stderr; returns 2. */
int       usage(void);

/*  common.c */
bool      number(const char *s, uint64_t *out);
char     *slurp(FILE *f, size_t *len);
uint32_t  load(av_arena *a, const char *src, size_t len);

/*  term.c: the reduction's options that front0 shares */
av_profile *profile_load(const char *path, const av_arena *a, uint32_t t);
bool      use_templates(av_arena *a, const char *dir, uint32_t *t, long counts[4],
                        bool data, long wc[3], bool fix);
void      report_data(const long wc[3], const av_result *r);
void      report_fix(const av_result *r);

/*  jetstat.c: a dictionary's rows and a names file's names, and the jet
 *  table front0 prints too */
typedef struct { uint64_t digest; char hash[27]; char *term; int file; } drow;
typedef struct { char *hash, *name; } jname;

int       load_rows(char **dicts, int nd, drow **out, size_t *count);
int       load_jnames(char **namefiles, int nn, jname **out, size_t *count);
void      print_jetstats(FILE *out, const av_jetstats *all, uint64_t total, size_t top,
                         const drow *rows, size_t nr, const jname *names, size_t nnames,
                         bool alone, const bool *alone_seen, const uint64_t *alone_abs,
                         const uint64_t *alone_fires);

/*  The commands */
int       term_main(int argc, char **argv);        /* reduce batch jam cue prefix witness */
int       kernel_main(int argc, char **argv);      /* boot poke peek load */
int       selfhost_main(int argc, char **argv);
int       scry_main(int argc, char **argv);
int       census_main(int argc, char **argv);
int       jetstat_main(int argc, char **argv);
int       front0_main(int argc, char **argv);
int       enum_main(int argc, char **argv);

#endif
