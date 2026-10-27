/**  main.c
 *
 *  The avon command.
 *
 *      avon reduce [options] [FILE]   reduce one term; print status, steps,
 *                                     and the term reached
 *      avon batch  [options]          reduce each stdin line; print one
 *                                     "STATUS steps term" line per term
 *      avon jam    [FILE]             printed form to a SKIT container
 *      avon cue    [FILE]             SKIT container to printed form
 *      avon prefix [FILE]             the term in prefix form (` for application)
 *      avon witness [--rows=N] [--cells=N] [--jet-table=JETS] [--plan=PLAN]
 *                   [FILE]
 *                                     the witness strategy's table, for
 *                                     lean-ski's aircheck and plonky3;
 *                                     with JETS, lean-ski's jet file for the
 *                                     term, instantiation rows
 *      avon witness --statement=PUBLIC --jet-table=JETS [WITNESS]
 *                                     a composed statement with jets: the
 *                                     witness's bits and region in the
 *                                     statement's heap, one jetted segment
 *                                     per root, padded to the statement's
 *                                     heights
 *      avon witness --statement=PUBLIC [WITNESS]
 *                                     a `p2pre` or `p2commit` statement:
 *                                     the composed machine with the
 *                                     Poseidon2 jet
 *                                     (lean-ski's P2Jet.p2Row), its table
 *                                     as bench/plonky3's compp-prove writes it
 *      avon census [--select=N] [--top=N] [--min-atoms=N] [--all]
 *                  [--names=FILE]... [--emit=DICT] MANIFEST...
 *                                     which terms the manifests' runs call,
 *                                     ranked by what a jet on each would
 *                                     absorb; --emit
 *                                     writes the shown rows and their layers
 *                                     as a jet dictionary
 *      avon jetstat [--jets=DICT]... [--ctors[=N]] [--names=FILE]... [--share]
 *                   [--alone] [--halting] [--top=N] MANIFEST...
 *                                     what each jet does on the manifests'
 *                                     runs: fires, absorbed contractions,
 *                                     misses, demotions, and each fire's
 *                                     origin; with --alone, each dictionary
 *                                     row by itself too
 *      avon scry [--log=DIR] [--jets=DICT [--interp=FILE]] [--jet-check=N]
 *                NAMESPACES
 *                                     the resume loop over
 *                                     a namespaces.tsv export: each run's
 *                                     events and attempts, checked against
 *                                     the reference host's; --log keeps each
 *                                     run's facts in DIR/ID.facts
 *      avon boot [--pier=DIR [--pma] [--entropy[=FILE]]] [--subject=FILE] PILL
 *      avon poke --pier=DIR [--snapshot] [--entropy=FILE] EVENT...
 *      avon peek --pier=DIR PATH...
 *      avon load --pier=DIR [--subject=FILE] [--snapshot] PILL
 *                                     a kernel: boot
 *                                     applies a pill (SKIT) to the initial
 *                                     subject (default I: skijack's standard
 *                                     subject is unbuilt), and with --pier
 *                                     makes a pier---an event log and
 *                                     snapshots, or with --pma a persistent
 *                                     arena committed every event---that
 *                                     poke, peek and load reopen; share mode
 *                                     by default.  --entropy: the
 *                                     pier answers a kernel's requests for
 *                                     entropy, and boot's own; =FILE draws
 *                                     the bits from FILE, not getentropy
 *      avon boot --drivers --pier=DIR [--strategy=copy|share] [--fuel=N]
 *                [--entropy[=FILE]] [--] FILE [ARG...]
 *      avon boot --drivers --pier=DIR [--fuel=N] [--entropy=FILE]
 *                                     run --kernel, durably: the kernel
 *                                     FILE run in a new pier, each answer
 *                                     logged before it is applied; without
 *                                     FILE, the pier's run reopened, its
 *                                     log replayed and the run continued
 *      avon selfhost [--jets] [--jet-check=N] [--every=N] DIR CALLS
 *                                     the compiler's core as a term: every
 *                                     call of a calls file, through
 *                                     DIR/abs.skit or its jet, checked
 *                                     against Python's by hash
 *      avon front0 [--profile=NAMES] [--jets=DICT]... [--ctors[=N]] [--jet-stats[=N]]
 *                  [--templates=DIR [--data] [--fix] [--memory] [--no-defer]] [--names=FILE]... [--fuel=N]
 *                  [--max-nodes=N] DIR SOURCE
 *                                     the SKIjack-0 front end on SOURCE:
 *                                     DIR/front.skit and the input's
 *                                     constructors; each name and its term's
 *                                     hash, read by probing
 *      avon enum N [--start=K] [--count=M]
 *      avon enum --base=FILE --shape=sxy,ssaq,hide
 *                                     the pure-S census's closed terms of
 *                                     size N (1 to 20), in its order, or
 *                                     shapes built on a file's terms
 *      avon --version
 *
 *  A FILE may be in the printed form, a SKIT container, or the prefix
 *  form, told apart by a magic or a leading `.  Options:
 *  --strategy=copy|share (default share), --whnf, --fuel=N, --max-nodes=N,
 *  --budget=N (nodes printed or jammed; default 1000000),
 *  --allow-bird-atoms (admit atoms named as the Python oracle's bird
 *  combinators are), --jets=DICT (a dictionary.tsv export: register it
 *  and match the term against it; repeatable), --ctors[=N] (register
 *  every Scott constructor of up to N atoms, default 64, in the term),
 *  --jet-floor=N (atoms, default 8), --jet-check=N (check every Nth fire
 *  against the unjetted run), --no-jets, --interp=FILE (interpreters.tsv:
 *  interpreter jets; needs --jets, and takes the constructors' terms from
 *  the first --jets= dictionary), --profile=NAMES (share mode: each
 *  contraction charged to the named term whose code it runs, reported on
 *  stderr), --templates=DIR (share mode: DIR/templates.tsv and
 *  DIR/template_terms.tsv, supercombinator templates checked against the
 *  terms and instantiated), --data (with --templates: data jets,
 *  constructor templates dispatched, fused into the branch's template,
 *  numerals held as words, and DIR/words.tsv's numeral operations run on
 *  them natively), --fix (with --templates: Y g unfolded to g (Y g) in one
 *  step), --no-defer (with --templates: every instance's root and spine
 *  written at once, not deferred, for comparing the two), --p2=FILE (share
 *  mode: FILE holds lean-ski's Poseidon2 term P, as `lake exe p2run`
 *  prints it; P applied to a state runs natively).  reduce and batch take
 *  --trace-frame[=summary] (copy mode's head run observed for the hider
 *  census) with --passenger=NAME, --records[=CONF], --frame-dump=SPEC and
 *  --defect[=CONF] (the paper's defect count);
 *  options_fit refuses an option the command would ignore.  A term may
 *  also be in the DAG form, `dag <id>=... @<root>`.  docs/RUNTIME.md is
 *  the user's guide.  Each command is a file of src/cli; this one
 *  dispatches.
 */

#include "cli/cli.h"
#include "sstats.h"

#define AVON_VERSION "0.1.0"

int usage(void) {
    fprintf(stderr,
        "usage: avon reduce [--strategy=copy|share] [--whnf] [--fuel=N]\n"
        "                   [--max-nodes=N] [--budget=N] [--dag] [FILE]\n"
        "       avon batch  [same options]\n"
        "       avon jam    [--budget=N] [FILE]\n"
        "       avon cue    [--budget=N] [FILE]\n"
        "       avon prefix [--budget=N] [FILE]\n"
        "       avon witness [--rows=N] [--cells=N] [--jet-table=JETS] [--plan=PLAN]\n"
        "       avon witness --statement=PUBLIC --jet-table=JETS [WITNESS]\n"
        "       avon witness --statement=P2PUBLIC [WITNESS]\n"
        "                    [FILE]\n"
        "       (all but witness --statement accept --allow-bird-atoms; reduce and batch accept\n"
        "        --jets=DICT... --ctors[=N] --jet-floor=N --jet-check=N --no-jets\n"
        "        --interp=FILE --profile=NAMES --templates=DIR --data --fix --memory --no-defer\n"
        "        --p2=FILE)\n"
        "       avon census [--select=N] [--top=N] [--min-atoms=N] [--all]\n"
        "                   [--names=FILE]... [--emit=DICT] MANIFEST...\n"
        "       avon jetstat [--jets=DICT]... [--ctors[=N]] [--names=FILE]... [--share]\n"
        "                    [--alone] [--halting] [--top=N] MANIFEST...\n"
        "       avon scry [--log=DIR] [--jets=DICT [--interp=FILE]] [--jet-check=N]\n"
        "                 NAMESPACES\n"
        "       avon boot [--pier=DIR [--pma] [--entropy[=FILE]]] [--subject=FILE] PILL\n"
        "       avon poke --pier=DIR [--snapshot] [--entropy=FILE] EVENT...\n"
        "       avon peek --pier=DIR PATH...\n"
        "       avon load --pier=DIR [--subject=FILE] [--snapshot] PILL\n"
        "       avon run [reduce's options] FILE      (avon reduce FILE)\n"
        "       avon run --kernel [--strategy=copy|share] [--fuel=N] [--entropy[=FILE]]\n"
        "                FILE [ARG...]                (FILE a kernel, run with drivers)\n"
        "       avon boot --drivers --pier=DIR [run --kernel's options] [FILE [ARG...]]\n"
        "                                             (durably; without FILE, resumed)\n"
        "       (boot, poke, peek, load accept --strategy=, --fuel=, and --budget=,\n"
        "        which boot --pier takes only with --entropy)\n"
        "       avon selfhost [--jets] [--jet-check=N] [--every=N] DIR CALLS\n"
        "       avon front0 [--profile=NAMES] [--jets=DICT]... [--ctors[=N]] [--jet-stats[=N]]\n"
        "                   [--templates=DIR [--data] [--fix] [--memory] [--no-defer]]\n"
        "                   [--names=FILE]... [--fuel=N] [--max-nodes=N] DIR SOURCE\n"
        "       avon enum N [--start=K] [--count=M]      (N from 1 to 20)\n"
        "       avon enum --base=FILE --shape=sxy,ssaq,hide\n"
        "       (reduce and batch accept --trace-frame[=summary] --passenger=NAME\n"
        "        --records[=CONF] --frame-dump=STEPS|records|census|halt|last-restart\n"
        "        --defect[=CONF])\n"
        "       avon --version\n");
    return 2;
}

static int run_main(int argc, char **argv);

/*  Every command, then its output checked: a write that failed, a full
 *  disk or a closed pipe, is a failure, not a run that printed nothing. */
int main(int argc, char **argv) {
    int rc = run_main(argc, argv);
    if (fflush(stdout) != 0 || ferror(stdout)) {
        fprintf(stderr, "avon: writing the output failed\n");
        if (rc == 0) rc = 1;
    }
    return rc;
}

static int run_main(int argc, char **argv) {
#ifdef AV_STRICT_STATS
    sstats_begin();                 /* build/stats/avon: one run's cells (sstats.h) */
    atexit(sstats_report);
#endif
    if (argc == 2 && strcmp(argv[1], "--version") == 0) {
        printf("avon %s\n", AVON_VERSION);
        return 0;
    }
    if (argc < 2) return usage();
    if (strcmp(argv[1], "census") == 0) return census_main(argc, argv);
    if (strcmp(argv[1], "jetstat") == 0) return jetstat_main(argc, argv);
    if (strcmp(argv[1], "scry") == 0) return scry_main(argc, argv);
    if (strcmp(argv[1], "selfhost") == 0) return selfhost_main(argc, argv);
    if (strcmp(argv[1], "front0") == 0) return front0_main(argc, argv);
    if (strcmp(argv[1], "enum") == 0) return enum_main(argc, argv);
    if (strcmp(argv[1], "run") == 0) return program_main(argc, argv);
    if (strcmp(argv[1], "boot") == 0)          /* --drivers among the options: a run */
        for (int i = 2; i < argc && argv[i][0] == '-' && strcmp(argv[i], "--") != 0; i++)
            if (strcmp(argv[i], "--drivers") == 0) return boot_drivers_main(argc, argv);
    if (strcmp(argv[1], "boot") == 0 || strcmp(argv[1], "poke") == 0 ||
        strcmp(argv[1], "peek") == 0 || strcmp(argv[1], "load") == 0)
        return kernel_main(argc, argv);
    return term_main(argc, argv);
}
