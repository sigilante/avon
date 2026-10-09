# Audit, 2026-10-05

Five reviewers read the codebase in parallel: failure paths, documentation against
code, the build and its gates, the security edges, and the shape of `reduce.c` and
`main.c`. This file ranks what they found. "Reproduced" means the finding was
re-run by hand after the review. Each fix becomes its own pull request (`WORKLIST.md`,
step 5). Findings already fixed on the `stage8-m1` branch are listed at the end.

The core holds. No reviewer found a way to make a verifier accept a wrong result, or
to forge an entropy reply. `make check` passes, with 25 suites under ASan and UBSan.
The weak spots are the pier, and the jets admitted by testing rather than by identity.

## 1. Data loss and secrecy

1. **Replay deletes an acknowledged event (reproduced).** `pier.c:439-459`.
   - Replay runs under the current invocation's `--fuel` and `--strategy`. Neither
     is logged.
   - When the last logged record fails to reach weak head normal form, open treats
     it as a crash leftover and truncates it.
   - Repro: boot `tests/kernel/pill.skit` and poke `events.tick`; the log is
     50 bytes. Then `poke --fuel=5 events.poke5`; the log is 0 bytes.
   - When the failing record is not last, the pier refuses to open.
   - On an entropy pier the truncation also rolls back `eny_n`. A file pier then
     reuses 16 bytes.
   - Fix: replay without a fuel limit, or under fuel and strategy logged with each
     record. Never truncate a record whose failure is FUEL; refuse instead.
2. **The kernel's entropy is readable by every local user (reproduced).**
   `pier.c:134, 147, 167, 479`; `snap.c:62`; `pma.c:223, 224, 367, 403, 407`.
   - Under umask 022 the pier is 0755, and `events.log` and the snapshots are 0644.
     The log holds each `eny` reply's 128 bits in hex. §9.1 says the pier is as
     secret as the bits.
   - `mkdir` also accepts an existing directory. Another user can pre-create it and
     plant a newer `snap-N`.
   - Fix: create the directory 0700 and files 0600. Refuse an existing directory
     unless it is empty, the caller's own, and 0700.
3. **`fsync` is not durable on macOS.** `pier.c:71`, `snap.c:71`, `pma.c`.
   - There is no `F_FULLFSYNC`, so "logged before applied" can lose an event on
     power loss.
   - `pier_new` never syncs the directory after creating `events.log`.
4. **A failed append leaves a torn record.** `pier.c:67-72, 492-499, 638`.
   - An embedder that keeps the pier open appends the next record onto the torn
     bytes, and the pier no longer opens. The CLI recovers, because it exits and
     open truncates the tail.
   - Fix: `ftruncate` to the record's start on failure.
5. **Snapshot-mode piers take no lock.** `pier.c:399, 479`. Two processes interleave
   appends. Only PMA piers lock. Fix: `flock` `events.log` at open.
6. **A failed PMA commit after an applied event reports `AV_SIZE` with `kept=true`.**
   `pier.c:502-505`. A caller that retries applies the event twice. Return a
   distinct status.

## 2. Wrong results from jets (share mode; the proof is unaffected)

7. **A word operation admitted by sampling changes a normal form (reproduced).**
   `words.c:191-232`, `tmpl.c:641-656`.
   - `word_admit` tests a `words.tsv` term on operands 0 to 5 only. An addition
     that is wrong from 7 on is admitted.
   - `fake6 7 1` reduces to 7 in plain share mode, and to 8 with `--templates --data`.
   - Fix: admit word operations by structural identity with pinned reference terms,
     as P2 is pinned (`p2.c:171`), never by samples.
8. **Residual, interpreter and compiler jets bind by a 64-bit digest or by
   declaration.**
   - `jets.c:543-591` never compares a matched node with the jet's term.
     `interp.c:48` reads dictionary rows without checking their hashes.
     `compiler.c:183-225` admits after 10 samples.
   - Whoever supplies both the jet metadata and a term can find a collision in
     about 2^32 work.
   - Fix: bind structurally, as templates and P2 are; check row hashes; use the full
     digest.

## 3. Denial of service and robustness

9. **Interning is quadratic.** `arena.c:112` (`av_leaf` scans every leaf),
   `wire.c:194, 211`.
   - An event of 80,000 atoms takes 9 s to refuse.
   - A logged event of 60,000 atoms costs 12 s on every open after.
   - Fix: a hash table, a check of the whole atom table before interning, and caps on
     the atom count and event size.
10. **`unhex` is quadratic.** `pier.c:59`: `sscanf` per byte. 800 KB of hex takes
    2.6 s. Replace it with a nibble decoder, and add a checksum per record. A flipped
    hex digit replays as a different event today.
11. **The defaults can exhaust host memory before SIZE.** `gc.c:47-48`,
    `av_opts_default`.
    - `--max-nodes` defaults to 2^30 nodes and fuel to unbounded.
    - Each collection allocates a to-space of the full capacity plus a forwarding
      array, about 2.5 times the arena.
    - Fix: size to-space by `used`, and choose a smaller default.
12. **Reservation invariants are `assert`s only.** `reduce.c:582, 722, 725, 1301`,
    `jets.h:147`. Release builds drop them, so a wrong reservation count would be a
    heap overflow rather than SIZE. Keep a cheap `used < cap` check, or name the
    trade.
13. **The DAG form skips name hygiene.** `read.c:196-204`. Names may hold `(`, `)`,
    a backtick or NUL; the output then does not re-parse, and a NUL aliases a prefix.
    Reuse `cue`'s `valid_name`.
14. **front0's probes each get the full fuel, and names print raw.** `front0.c:100,
    162, 254`.
    - Work is probes times fuel.
    - A decoded name holding a newline can forge an output line.
15. **Exit codes and smaller items.**
    - `run_one` returns 0 for FUEL, SIZE, INTERRUPTED and a failed jet check
      (`main.c:720`), and stdout errors go unchecked. So scripts cannot see failure.
    - Smaller: a PMA journal held whole in memory (`pma.c:343`), a `close(0)` on a
      failed open (`pma.c:481`), a NULL error string (`pma.c:289`), a leftover
      `nodes` file after a failed attach (`pma.c:403`).

## 4. Gates

16. **CI runs only the unit tests, against committed fixtures.**
    - The conformance, data and selfhost fixtures record no exporter commit, and
      every skijack and lean-ski check is manual.
    - Fix: record provenance, and add a scheduled job against pinned revisions.
17. **The release binary is built in CI but never run.** The optimized code, with
    its asserts gone, meets no behavioural test. Run a smoke manifest on `build/avon`.
18. **Some tests pass with their fixture missing.**
    - `test_data.c`, `test_jets.c:58, 135, 344`, `test_kernel.c:334, 356` and
      `test_entropy.c` return early on a failed open.
    - `tests/test.h` cannot flag a case that checked nothing. Add a `REQUIRE`, and
      fail a case with no checks.
19. **Nothing is pinned.**
    - Floating: the CI images, clang and `actions/checkout`.
    - Taken from whatever is checked out: the skijack branch and the lean-ski commit.
    - Off any repo: `hider_check.sh` defaults to a personal path.
20. **DESIGN §10.3 claims fuzzing at millions of cases in CI.** CI runs 20,000
    reduce cases, 20 jet rounds and 150 interpreter cases, and there is no
    wire-format fuzzer.

## 5. Documentation against code

21. **RUNTIME.md says SKIT and `jam` hold no atoms.** `jam` accepts `S x`, and the
    SKIT header (`avon.h:268`) has an atom table. The code is right.
22. **`options_fit` lets ignored options through.**
    - `reduce --rows --plan --jet-table` exits 0 (`main.c:326`).
    - `batch FILE` ignores FILE.
    - `boot --entropy` without `--pier` is ignored.
23. **Undocumented behaviour.**
    - `witness --statement`, and the 2^21 row default.
    - The kernel commands' fuel and budget defaults.
    - The 1,000,000-step normalization behind printed effects.
    - Options of `scry`, `front0` (`--memory`, `--no-defer`), and `jam`/`cue`
      (`--budget`).
    - `make p2-witness-check`.
24. **BENCHMARK.md cites branches that no longer exist.** The wall-clock table has
    no harness in the repository. Tag the commits, and add the harness or a
    Reproduce block.

## 6. The shape of `reduce.c` and `main.c`, and the two slated questions

25. **Plain SKI's residual 1.9 to 3.9% since deferred roots (hypotheses, unmeasured).**
    - Most likely: `cur` is passed by address to non-inlined helpers (`hensure`,
      `materialize`, `prepare`, `dispatch`, `case_join`, `tmpl_defer`), which keeps
      it in memory.
    - Next: `hensure` and the stack-kind tests run unguarded in the `D=false` copy.
    - Try first: make `hensure` `D`-aware, then pass `cur` by value, then split the
      jet path out of the leaf loop into a `noinline` function.
26. **Deferral's 8 to 39 MB of extra peak (hypotheses, unmeasured).**
    - Most likely: the live-set figure counts arena nodes only, not `stk`, `dstk`
      and the `nvirt` reserve, which double and never shrink.
    - Next: power-of-two arena growth, which makes the deltas step-sized.
    - Measure first: record peak `top`, `ndstk`, the reserve and `cap`.
27. **Shape.**
    - `reduce.c` is four programs in one file: the copy reference, the share
      machine, the deferred spine stack, and jet and template dispatch.
    - Name the stack as a module (`SK_*`, `materialize`, `root_set`, `defer_*`), and
      put the copy machine in its own file.
    - `main.c` is eight subcommands over one flag struct. Split it along its
      `*_main` seams, and name the repeated `av_arena_new(1u << 16)`.

## Order of fixes

1. Items 1 and 2, the pier's log integrity and secrecy.
2. Items 7 and 8, binding jets by identity.
3. Items 3 to 6, the pier's durability.
4. Items 9 to 15, robustness.
5. Items 16 to 20, the gates.
6. Items 21 to 24, the documents.
7. Items 25 to 27, measured first, then restructured.

## Fixed since

- Items 1 and 2 (`pier-replay`). Replay runs logged events with no fuel limit and
  never drops one but a torn record. Piers are 0700 with files 0600, and a pier
  refuses a directory that is not empty, the caller's own, and 0700.
- Item 7 (`pin-words`). A word operation is admitted only if its term is skijack's,
  node for node: `words.c` pins the five. The forged addition is refused, and
  `fake6 7 1` gives 7 with `--templates --data` as without.
- Item 8 (`bind-jets`).
  - A residual jet wraps a node only if the node is its term, tree for tree.
  - An interpreter's dictionary rows must have their hashes.
  - The compiler jet is admitted only if its nine terms match full digests pinned
    in `compiler.c`.
- Items 3 to 6 (`pier-durable`).
  - Syncs reach the media (`F_FULLFSYNC` on macOS), and directories are synced
    after a create or a rename.
  - A record is written whole or cut away again.
  - `events.log` is locked for the pier's life.
  - A failed commit after an applied event is reported beside it, not as its
    failure.
- Item 8, again (`match-identity`). #26 compared a candidate with the jet's
  term under a budget set by the jet's size. That refused templates whose
  copies in the program shared less, and front1's fixed point rose from
  80,541,877 contractions to 88,316,487. Matching is now by canonical ids,
  exact and linear, and both fixed points are back to their counts.
- Items 9 and 10 (`robust-intern`).
  - Atoms are interned through a hash index. A container's whole atom table is
    checked before any name is interned, and duplicates are found by sorting.
    100,000 atoms cue in 0.04 s.
  - The log's hex decodes in linear time, lowercase only.
  - Each record carries a checksum. Records written before 2026-10-09, without
    one, still read.
  - No caps on atom count or event size: with linear interning the cost the
    caps were to bound is linear in the event.
- Items 11 and 12 (`robust-mem`).
  - `--max-nodes` defaults to physical memory over 64 bytes, between 2^20 and
    2^30. A collection peaks near 40 bytes a live node, so a runaway run
    reports SIZE before it can take the host's memory.
  - The reservation invariants that guard writes into the arena are
    `AV_ALWAYS`, checked in release builds too. A breach aborts with its place
    instead of writing past the arena.
  - The checks cost nothing measurable once their failure path is marked cold.
    Unmarked, they cost templates mode 4 to 7.5%. On the five Reduceron ports
    against master, the geometric means are +0.4% as SKI, -0.1% with
    templates, -0.2% with data jets and -0.5% with Y unfolded, with every step
    count the same.
  - To-space is still allocated at the arena's capacity. A collection runs when
    the arena is full, so sizing it by `used` saves nothing.
- Items 13 to 15 (`robust-io`).
  - A DAG leaf name holding a parenthesis, a backtick or a NUL is refused.
  - `front0`'s probes share `--fuel`, a name it reads is at most 65,536
    characters, and a name with a control character or a space is refused,
    since one could forge an output line.
  - `reduce` and `batch` exit 1 when a jet check fails, and every command exits
    1 when its output could not be written. A run that stops on FUEL or SIZE
    still exits 0, its status on its line: the census client, `parity.py` and
    `diff_aviary.py` read it there.
  - The persistent arena no longer closes stdin on a failed open, gives every
    failure a message, and removes the `nodes` file a failed attach made.
- Item 15's last point (`pma-journal`). The PMA journal streams: a commit
  writes it 64 KiB at a time, and open verifies its digest and records a
  block at a time before it applies them one record at a time. Memory holds
  one block and one record, whatever the journal's size; the largest record
  is the atoms table, which a commit builds whole as before. `test_pma`
  damages an 800 KB journal two ways and sees both refused.
- Tests for items 13 to 15 (`robust-io-tests`).
  - `test_front0` reads Scott results built in the test, with no front end:
    the probes share `--fuel`, and a name with a control character, a space
    or 65,537 characters is refused. All three cases fail on the code
    before #30.
  - `test_cli` checks the exit codes: 0 for FUEL and SIZE, 1 for a term
    that does not parse and for output that cannot be written.
  - `test_pma` checks that a failed open leaves stdin open. `test_trace`
    already covered the DAG names.
  - Untested: the PMA attach's failure paths, its open's out-of-memory
    path, and a jet check failing from the command line, which needs a
    corrupted jet.

## Fixed on `stage8-m1`

- DESIGN.md's status line said the full front end remained.
- WORKLIST listed CI and the entropy check as next.
- RUNTIME.md's checks lacked `make front1-check`.
