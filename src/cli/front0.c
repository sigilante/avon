/**  front0.c
 *
 *  avon front0: the SKIjack-0 front end (docs/DESIGN.md §20.3) on a
 *  source.
 */

#include "cli.h"

/*  avon front0 [--profile=NAMES] [--fuel=N] [--max-nodes=N] DIR SOURCE:
 *  the SKIjack-0 front end (§20.3) on SOURCE, DIR holding its term and the
 *  input's constructors as SKIT files; a line `name TAB hash` per name, or
 *  `RErr`, and the contractions on stderr. */
int front0_main(int argc, char **argv) {
    const char *dir = NULL, *source = NULL, *profile = NULL, *templates = NULL;
    bool data = false, fix = false;
    char *dicts[16], *namefiles[64];
    int nd = 0, nn = 0;
    uint64_t ctors = 0, stats_top = 0;
    av_opts o = av_opts_default();
    o.jets = false;
    uint64_t v;
    for (int i = 2; i < argc; i++) {
        const char *s = argv[i];
        if (strncmp(s, "--profile=", 10) == 0 && s[10]) profile = s + 10;
        else if (strncmp(s, "--jets=", 7) == 0 && s[7] && nd < 16) dicts[nd++] = argv[i] + 7;
        else if (strcmp(s, "--ctors") == 0) ctors = 64;
        else if (strncmp(s, "--ctors=", 8) == 0 && number(s + 8, &v) && v) ctors = v;
        else if (strncmp(s, "--templates=", 12) == 0 && s[12]) templates = s + 12;
        else if (strcmp(s, "--data") == 0) data = true;
        else if (strcmp(s, "--fix") == 0) fix = true;
        else if (strcmp(s, "--memory") == 0) fix = o.fix_shared = true;
        else if (strcmp(s, "--no-defer") == 0) o.no_defer = true;
        else if (strncmp(s, "--names=", 8) == 0 && s[8] && nn < 64) namefiles[nn++] = argv[i] + 8;
        else if (strcmp(s, "--jet-stats") == 0) stats_top = 40;
        else if (strncmp(s, "--jet-stats=", 12) == 0 && number(s + 12, &v)) stats_top = v;
        else if (strncmp(s, "--fuel=", 7) == 0 && number(s + 7, &v)) o.max_steps = v;
        else if (strncmp(s, "--max-nodes=", 12) == 0 && number(s + 12, &v) && v <= AV_MAX_NODES)
            o.max_nodes = (uint32_t)v;
        else if (s[0] != '-' && !dir) dir = s;
        else if (s[0] != '-' && !source) source = s;
        else return usage();
    }
    if (!dir || !source || ((data || fix) && !templates)) return usage();
    FILE *sf = fopen(source, "rb");
    if (!sf) { perror(source); return 1; }
    size_t slen;
    char *src = slurp(sf, &slen);
    fclose(sf);
    if (!src) return 1;
    static const char *const names[6] = { "front", "SCons", "SNil", "Code", "Lo", "Hi" };
    av_arena *a = av_arena_new(ARENA_START);
    uint32_t terms[6];
    for (int i = 0; i < 6; i++) {
        char path[1100];
        snprintf(path, sizeof path, "%s/%s.skit", dir, names[i]);
        FILE *tf = fopen(path, "rb");
        size_t tl = 0;
        char *tb = tf ? slurp(tf, &tl) : NULL;
        if (tf) fclose(tf);
        terms[i] = tb && a ? av_cue(a, (const uint8_t *)tb, tl, NULL) : AV_NONE;
        free(tb);
        if (terms[i] == AV_NONE) {
            fprintf(stderr, "avon: %s: not a term\n", path);
            free(src);
            av_arena_free(a);
            return 1;
        }
    }
    av_front0 f;
    _Static_assert(sizeof f == sizeof terms, "six terms");
    memcpy(&f, terms, sizeof f);
    uint32_t t = av_front0_input(a, &f, src, slen);
    free(src);
    if (t == AV_NONE) {
        fprintf(stderr, "avon: %s: not ASCII, or out of memory\n", source);
        av_arena_free(a);
        return 1;
    }
    /* jets: constructors found in the program, then the dictionaries */
    av_root_push(a, &t);
    bool jets_ok = !ctors || av_jets_ctors(a, t, (size_t)ctors) >= 0;
    for (int d = 0; jets_ok && d < nd; d++) {
        const char *jerr = NULL;
        if (av_jets_load(a, dicts[d], 1, &jerr) < 0) {
            fprintf(stderr, "avon: %s: %s\n", dicts[d], jerr);
            jets_ok = false;
        }
    }
    av_root_pop(a);
    long tc[4] = { 0, 0, 0, 0 }, wc[3] = { 0, 0, 0 };
    if (jets_ok && templates) {
        jets_ok = use_templates(a, templates, &t, tc, data, wc, fix);
        o.jets = true;
        o.templates = true;
        o.data = data;
        o.fix = fix;
    } else if (jets_ok && a->njets) {
        t = av_jets_match(a, t);
        o.jets = true;
    }
    av_jetstats *stats = stats_top ? av_jetstats_new() : NULL;
    if (!jets_ok || t == AV_NONE || (stats && !av_jetstats_begin(stats, a, t))) {
        av_jetstats_free(stats);
        av_arena_free(a);
        return 1;
    }
    o.jetstats = stats;
    av_profile *prof = NULL;
    if (profile && !(prof = profile_load(profile, a, t))) { av_arena_free(a); return 1; }
    o.profile = prof;
    uint64_t steps = 0;
    const char *err = NULL;
    av_result tally = { 0 };
    int rc = av_front0_read(a, t, &o, stdout, &steps, &tally, &err);
    fprintf(stderr, "contractions %llu\n", (unsigned long long)steps);
    if (templates)
        fprintf(stderr, "templates: %ld accepted, %ld refused, %ld skipped, %ld unbound; "
                "%llu instantiations among the contractions\n", tc[0], tc[1], tc[2], tc[3],
                (unsigned long long)tally.tmpl_calls);
    if (data) report_data(wc, &tally);
    if (fix) report_fix(&tally);
    if (stats) {
        drow *rows = NULL;
        size_t nr = 0, nlabels = 0;
        jname *labels = NULL;
        if (!load_rows(dicts, nd, &rows, &nr) && !load_jnames(namefiles, nn, &labels, &nlabels))
            print_jetstats(stderr, stats, steps, (size_t)stats_top, rows, nr, labels, nlabels,
                           false, NULL, NULL, NULL);
        for (size_t i = 0; i < nr; i++) free(rows[i].term);
        free(rows);
        for (size_t i = 0; i < nlabels; i++) { free(labels[i].hash); free(labels[i].name); }
        free(labels);
        av_jetstats_free(stats);
    }
    if (rc < 0) fprintf(stderr, "avon: the result does not read: %s\n", err ? err : "?");
    if (prof) {
        av_profile_report(prof, stderr, SIZE_MAX);
        av_profile_free(prof);
    }
    av_arena_free(a);
    return rc < 0 ? 1 : 0;
}
