# Testing Avon

Avon is checked in two layers.  The unit tests and the smoke test need
nothing outside this repository and run in minutes.  The other checks
compare Avon with the implementations it must agree with, the Python
compiler, the Python reducer and the proof system, each at a pinned
revision.

## The unit tests: `make check`

```sh
make check        # about 7.5 min on an Apple M4 Max
```

`make check` builds `build/dbg/avon` and each of the 27 suites
`tests/test_*.c` with AddressSanitizer and UndefinedBehaviorSanitizer, and
runs them.  Each suite prints `tests/test_NAME.c: N/N passed`; some print a
line of figures too.  Then `tests/drivers_check.sh` runs `build/dbg/avon run
--kernel` on the worlds of `tests/drivers/expected.tsv` and compares each
run's output, error and status with the reference host's, printing
`drivers: N of N runs agree with the reference host`.  The target exits 0
only if every suite and every run passes; it prints no summary.

One line in its output looks like a failure and is not: `avon: internal
invariant broken at ... jets.h: allocation past what was reserved`, printed
just before `tests/test_reduce.c` passes.  That suite checks that an
over-allocation stops the process, in a child.

A suite whose fixture is missing fails, not skips (`tests/test.h`).

## The smoke test: `make smoke`

```sh
make smoke        # about 4 s: smoke: 30/30 commands as recorded
```

`tests/smoke.tsv` records, for 30 commands, the exit status and the SHA-256
of stdout and stderr, taken from `build/dbg/avon` under the sanitizers.
`make smoke` runs them on the release binary, whose `assert`s are compiled
out, and compares.  The commands cover every subcommand but `front0`, each
strategy, jets, templates, data jets, `--fix`, `--no-defer`, three piers,
six refused options, a bird-named atom, the DAG form out, and a witness of a
term with atoms, which is refused.

When a change alters a recorded output on purpose, record it again from the
sanitized binary, then check that only the rows you meant changed:

```sh
make check                                   # builds build/dbg/avon
tests/smoke.sh --record build/dbg/avon
git diff tests/smoke.tsv
make smoke
```

## CI

`.github/workflows/check.yml` runs the release build, `make smoke`, `make
stats` and `make check` on Linux (clang 18) for every pull request and push
to master, and on macOS too for pushes to master.  A change to
documentation alone (Markdown, `docs/`, `img/`, `LICENSE`) runs nothing.
`.github/workflows/pinned.yml` runs `fixtures-check`, `selfhost-check`,
`front0-check` and `front1-check` weekly against the public repositories
at their pins, and in a job of its own the seven checks that need lean-ski,
at lean-ski's pin.  `hider-check`, which needs the paper's scripts, runs by
hand.

## The checks against other repositories

| target | what it proves | needs | time |
|---|---|---|---|
| `make selfhost-check` | the compiler core gives Python's result, hash for hash, for every abstraction of its own compilation and the corpus's, as a term and through its jet (`DESIGN.md` §20.3) | SKIjack | |
| `make front0-check` | the SKIjack-0 front end compiles its own source to Python's terms, and 67 edge programs and 1,000 random ones as spec0 does: as SKI, with templates, with data jets, and with Y unfolded | SKIjack | 27 min |
| `make front1-check` | the full language's front end, through M4: its own source and every corpus program to the expander's terms, and 303 edge programs and 400 random ones as the expander does (bar 12 edges aviary's environment decides), in the same four modes; and, with data jets, front1's own templates (`front0 --emit`) for the corpus and its own source as `skijack.templates` has them | SKIjack | 106 min |
| `make fixtures-check` | every one of the 236 exported fixtures is what its exporter writes at the pins | SKIjack, SKIlark, aviary | 1 min |
| `make witness-check` | the corpus's witnesses check and prove in lean-ski (`DESIGN.md` §17) | lean-ski | |
| `make jet-witness-check` | the same, jetted (`DESIGN.md` §18) | lean-ski | |
| `make probe-witness-check` | the same, with probe segments | lean-ski | |
| `make zk-jet-witness-check` | composed statements with jets: Avon's tables are ski-air's, accepted by `check-cj`, proved under hiding and verified; bad witnesses and budgets refused (`ZK-JETS.md`) | lean-ski | |
| `make p2-witness-check` | the Poseidon2 statements: Avon's tables are byte-identical to ski-air's for `p2pre` and the two `p2commit` hand-off stages, proved and verified, a flipped bit refused; `reduce --p2` runs each test vector's permutation natively in one step, and a chain of three in three | lean-ski | |
| `make words-lean-check` | `lean/Words.lean` elaborates: each of the fifteen word operations' pinned terms, on numerals, lists and bit strings, computes its function on every input, and `word_fire`, `list_fire` and `bits_walk`, modelled, are sound, every printed theorem on Lean's axioms only; its print is `src/word_pins.h`, byte for byte (`LEAN-JETS.md`) | lean-ski | 11 s |
| `make templates-lean-check` | `lean/Templates.lean` elaborates: `tmpl.c`'s load check computes lean-ski's bracket abstraction, and an accepted template's fire is a reduct of its redex, on Lean's axioms only; its replay of the loader counts what Avon counts on the five template sets the tests ship and on eight copies changed to reach each refusal (`LEAN-JETS.md` §6) | lean-ski | 11 s |
| `make hider-check` | `avon enum` gives the census's terms in its order; every frame trace of a term of size 12 or less equals the census's run line for line, and of size 10 or less at horizons 1 to 21; the census through Avon gives its verdicts and trails; every defect count of a term of size 11 or less equals the definitions', and their totals the paper's mode `defect`; the five named cases (`DESIGN.md` §22) | the pure-S paper's scripts | 35 min |
| `tests/diff_aviary.py` | `copy` mode against `aviary_kernel` on random terms | `aviary_kernel` installed, and `build/dbg/avon` | |

Times are on an Apple M4 Max; a blank is not measured here.

### Where the other repositories come from

| repository | variable | default path | public |
|---|---|---|---|
| [SKIjack](https://github.com/sigilante/SKIjack) | `SKIJACK` | `~/skijack` | yes |
| [SKIlark](https://github.com/sigilante/SKIlark) | `SKILARK` | `~/Code/ski/skilark` | yes |
| [aviary](https://github.com/sigilante/aviary) | `AVIARY` | `~/Code/urbit/aviary` | yes |
| lean-ski | `LEAN_SKI` | `~/Code/ski/lean-ski` | not yet |
| the pure-S paper's scripts | `HIDER_SCRIPTS` | none: set it to the paper's `scripts/` | not yet |

The SKIjack checks also need the `aviary_kernel` Python package that
SKIjack imports to be aviary's at its pin; the lean-ski checks need Lean's
`lake` and lean-ski's Rust prover.  A check pointed at a missing checkout
stops at once and names the directory it looked in; `hider-check` names
`HIDER_SCRIPTS`.  A checkout elsewhere is named by its variable, for
example `SKIJACK=../SKIjack make selfhost-check`.

### Pins

A check that needs another repository runs against the commit
`tests/pins.sh` pins.  It also accepts a descendant of that commit whose
commits since, and whose tracked changes, touch only documentation:
`*.md`, `*.tex` and `*.txt` files, except lean-ski's statements, witnesses
and corpora (`*public*.txt`, `*witness*.txt`, `*corpus*.txt`), which the
checks read.  The repository's own CI workflows (`.github/`) count as
documentation too, since no check reads them.  A rename counts on both
sides.  It refuses any other checkout
unless `AVON_UNPINNED=1`.

To move a pin, run the checks it serves at the new commit, regenerate any
fixture that changes (`make fixtures-check` says which), and change the pin
in `tests/pins.sh`.

## Adding a test

A unit test is a `TEST(name)` in a `tests/test_*.c` suite, listed in its
`TEST_MAIN` (`tests/test.h`); a new suite is picked up by the Makefile's
wildcard.  A command whose output should not drift between the sanitized
and release binaries belongs in `tests/smoke.tsv`; record it as above.
