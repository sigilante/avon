# Running Avon

This is the user's guide: what each command does, the options it takes,
the files it reads and where they come from, and what each check proves.
`docs/DESIGN.md` is the design and its reasons; section numbers below
(§6.9) point there. `docs/BENCHMARK.md` has the measurements.

Commands run from the repository root. Paths like `~/skijack` assume a
skijack checkout there, and `~/lean-ski` a lean-ski checkout; the scripts
take `SKIJACK=` and `LEAN_SKI=` to change them. (skijack's own
`RUNTIME-DESIGN.md` is a design note about the runtime, not this guide.)

## Building

Avon is C11 with no dependencies. It needs clang and GNU Make 3.81 or
later.

```sh
make                  # build/avon, optimized
make check            # every tests/test_*.c under ASan and UBSan; also build/dbg/avon
make clean            # removes build/
```

If clang refuses to run until the Xcode license is accepted, either run
`sudo xcodebuild -license accept` or build with the Command Line Tools:
`DEVELOPER_DIR=/Library/Developer/CommandLineTools make`.

## Terms and their forms

A term is S, K, I and atoms under application. A command that takes a
`FILE` reads it in any of three forms, told apart by a magic or a leading
backquote, or reads standard input when no file is given:

| form | looks like | notes |
|---|---|---|
| printed | `S (K S) K f g x` | aviary's `pretty`: application to the left, parentheses around an argument that is an application |
| SKIT | a binary container (§4.2) | what skijack's `jam` writes; closed S/K/I terms, no atoms |
| prefix | `` ``SKK `` for `S K K`: `` ` `` before an application | closed S/K/I only |

```sh
echo 'S K K' | build/avon jam > t.skit       # printed -> SKIT
build/avon cue t.skit                        # SKIT -> printed: S K K
build/avon prefix t.skit                     # -> prefix form: ``SKK
```

SKIT and the prefix form hold closed terms only: `jam` and `prefix` refuse
a term with an atom such as `x`.

Atom names beginning with `@` are reserved (Avon's probe markers), and an
atom named like a live aviary bird is refused unless `--allow-bird-atoms`.

## Reducing: `reduce` and `batch`

```sh
build/avon reduce --strategy=copy --whnf tests/fixtures/t0.ski
echo 'S K K x' | build/avon reduce
```

`reduce` prints two lines: the status and the contraction count, then the
term reached. The status is `WHNF` or `NORMAL` when the run finished,
`FUEL` or `SIZE` when a budget stopped it, and `INTERRUPTED` when a
`--jet-check` found a jet disagreeing with its term. `batch`
reduces each line of standard input and prints one `STATUS steps term`
line per term. Jet and template reports go to standard error.

**Two strategies** (§1.1, §3):

- `--strategy=copy` is the reference host's algorithm. Its contraction
  counts are the paper's, and conformance holds them exactly.
- `--strategy=share`, the default, is Turner's graph reduction: a
  duplicated redex is contracted once. Its counts are its own, reported
  and never asserted.

| option | meaning |
|---|---|
| `--whnf` | stop at weak head normal form; otherwise reduce to normal form |
| `--fuel=N` | at most N contractions; a jet fire or template instantiation is charged as §6.5 and §6.9 say |
| `--max-nodes=N` | live nodes allowed after a collection before `SIZE` |
| `--budget=N` | nodes read or printed (default 1,000,000) |
| `--allow-bird-atoms` | accept atoms named like aviary birds |

## Jets

Jets replace reduction with a precomputed result; each kind is licensed
differently (§6).

| option | what it loads | modes | counts |
|---|---|---|---|
| `--jets=DICT` | a `dictionary.tsv`: residual jets, keyed by §5 hash (§6.5) | both | `copy` counts unchanged; `share` charges each fire its copy cost |
| `--ctors[=N]` | every Scott constructor of up to N atoms (default 64) in the term (§6.8) | both | as `--jets` |
| `--jet-floor=N` | skip dictionary terms under N atoms (default 8) | | |
| `--jet-check=N` | check every Nth fire against the unjetted run (§6.6) | both | |
| `--no-jets` | match nothing | | |
| `--interp=FILE` | `interpreters.tsv`: interpreter jets (§7); needs `--jets` | both | changes counts; off unless asked |
| `--templates=DIR` | `DIR/templates.tsv` and `DIR/template_terms.tsv`: supercombinator templates (§6.9) | `share` only; `copy` refuses | one step per instantiation, reported |
| `--data` | with `--templates`: data jets (§6.10), constructor dispatch and numerals held as words, and `DIR/words.tsv`'s numeral operations | `share` only | one step per dispatch or operation, reported |

```sh
build/avon reduce --strategy=copy --jets=tests/conformance/dictionary.tsv --jet-check=1 \
    tests/conformance/<target>.skit
```

**Templates** are each compiled rule's formals and body, beside the pure
SKI term. Avon keeps a template only if its body abstracts back to its
key, and fires it only on a node whose term is that key, compared as
trees; a template that fails either check is refused or unbound, and the
term runs as SKI. The report line on stderr counts them:

```
templates: 641 accepted, 0 refused, 352 skipped, 0 unbound; 18930884 instantiations among the contractions
```

`refused` counts templates whose body does not abstract to their key, or
malformed lines; `skipped` counts duplicates, η-templates, open bodies,
bare-leaf keys, and templates of more than 32 formals (a constructor of a
128-way type takes 128), the most one fire takes.

**Data jets** (`--data`, §6.10) add three things to templates, and print a
second line:

```
data: 5 numeral operations admitted, 0 refused; 95 numerals made words; 1750 dispatches (1395 fused), 8 numeral operations among the contractions
```

- A constructor's template -- its body a formal applied to the fields --
  meeting its continuations dispatches: the selected continuation applied
  to the fields replaces the redex, one step. When that continuation is a
  case branch's template with what it captured, the branch is
  instantiated in the same step, `fused`.
- Closed numerals (`Suc (Suc Zero)`, whatever the type is called) become
  words, numbers whose term is still the numeral; a word meeting its two
  continuations dispatches without allocating.
- skijack's numeral operations (`natAdd`, `natSub`, `natMul`, `natIfEq`,
  `natIfLe`), listed in `words.tsv` by the §5 hash of their terms, run
  natively when both operands are words already, and otherwise run as
  their terms. Each is `admitted` only after its term, run on the numerals
  0 to 5, agrees with the native operation; one that does not is
  `refused` and runs as its term.

Normal forms are the unjetted ones, byte for byte; a WHNF state is
templates' (which may differ from SKI's in form, not value).

## Measuring

| tool | question it answers | notes |
|---|---|---|
| `reduce --profile=NAMES` | which named code each contraction runs (§6.7) | `share` only; NAMES is `kind TAB name TAB hash` lines; report on stderr |
| `census MANIFEST...` | which terms the manifests' runs call, ranked by what a jet on each would absorb (§6.7) | `copy`, never collects |
| `jetstat MANIFEST...` | per jet: fires, absorbed contractions, misses, demotions, each fire's origin | `copy` unless `--share` |
| `front0 --jet-stats[=N]` | the same, on the front end's run | |

`census` options: `--select=N` (prefixes captured, default 400),
`--top=N` (rows shown, default 40), `--min-atoms=N` (default 5), `--all`
(layers and non-jets too), `--names=FILE` (labels, repeatable),
`--emit=DICT` (write the shown rows and their layers as a jet dictionary).

`jetstat` options (at least one of `--jets` or `--ctors` is required):
`--jets=DICT` (repeatable), `--ctors[=N]`,
`--names=FILE`, `--share`, `--halting` (skip the runs the manifest says
fuel stops), `--alone` (each dictionary row by itself too), `--top=N`.

```sh
build/avon census --top=40 --emit=census40.tsv \
    tests/conformance/manifest.tsv tests/workloads/skilark/manifest.tsv
build/avon jetstat --halting --alone --jets=census40.tsv --jets=jets/birds.tsv \
    --names=jets/birds_names.tsv tests/conformance/manifest.tsv tests/workloads/skilark/manifest.tsv
```

A census or jetstat run checks every `copy` count against its manifest,
with jets on, and fails if one is off.

## The self-hosted compiler

**`front0`** runs skijack's SKIjack-0 front end, itself a SKIjack program
compiled to one term, on a source file, and prints each name and its
term's §5 hash (§20.3):

```sh
cd ~/skijack/python
D=$(PYTHONPATH=. python3 -c "from skijack.selfhost import run0; print(run0.term_dir())")
~/avon/build/avon front0 $D skijack/selfhost/front0.ascii.ski               # SKI
~/avon/build/avon front0 --templates=$D $D skijack/selfhost/front0.ascii.ski # with templates
```

`DIR` holds `front.skit` and the input's constructors (`SCons`, `SNil`,
`Code`, `Lo`, `Hi`), and the front end's templates. `run0` writes it and
drives the checks:

```sh
PYTHONPATH=. python3 -m skijack.selfhost.run0 --avon ~/avon/build/avon --edges --random 1000
PYTHONPATH=. python3 -m skijack.selfhost.run0 --avon ~/avon/build/avon --templates --edges --random 1000
PYTHONPATH=. python3 -m skijack.selfhost.run0 --avon ~/avon/build/avon --templates --data --edges --random 1000
PYTHONPATH=. python3 -m skijack.selfhost.run0 --avon ~/avon/build/avon --profile
```

`front0` also takes `--templates=DIR`, `--data`, `--profile=NAMES`, `--jets=DICT`,
`--ctors[=N]`, `--jet-stats[=N]`, `--names=FILE`, `--fuel=N` and
`--max-nodes=N`.

**`selfhost`** runs the compiler's core -- bracket abstraction written in
SKIjack -- on every abstraction in a calls file, or through its native
jet with `--jets`, and compares each result with Python's by hash:

```sh
build/avon selfhost tests/selfhost tests/selfhost/own.tsv
build/avon selfhost --jets --jet-check=1 tests/selfhost tests/selfhost/own.tsv
```

`--jet-check=N` checks every Nth jet fire against the term, and
`--every=N` runs every Nth call only.

## Kernels: `boot`, `poke`, `peek`, `load`

A kernel is a term with state that events update and paths read (§9,
§20). Events, paths and pills are SKIT files.

```sh
build/avon boot --pier=/tmp/pier tests/kernel/pill.skit        # a pier: log and snapshots
build/avon poke --pier=/tmp/pier tests/kernel/events.tick.skit tests/kernel/events.poke5.skit
build/avon peek --pier=/tmp/pier tests/kernel/events.zero.skit
build/avon load --pier=/tmp/pier tests/kernel/pill.skit        # a new kernel onto the old state
```

- `boot PILL` applies the pill to the initial subject (`--subject=FILE`,
  default `I`). Without `--pier` it only reports whether the value is a
  kernel.
- `boot --pma` makes the pier a persistent arena, committed after every
  event (§19); otherwise a pier is an event log and snapshots, and
  `--snapshot` on `poke` or `load` takes one. `--pma` matters only to
  `boot`: the pier remembers which it is.
- All four accept `--strategy=`, `--fuel=` and `--budget=`; share mode is
  the default.

## Scry: `scry`

`scry NAMESPACES` runs the resume loop (§8) over a `namespaces.tsv`
export, checking each run's events and attempts against the reference
host's; `--log=DIR` keeps each run's facts.

```sh
build/avon scry tests/conformance/namespaces.tsv
```

## Proofs: `witness`

`witness` writes the witness strategy's table for lean-ski's checker and
prover (§17); `--jet-table=JETS` adds lean-ski's jet file for the term
(§18.1), `--plan=PLAN` probe segments. `--rows=N` and `--cells=N` are
budgets. `make witness-check` runs the corpus through lean-ski.

## The files Avon reads

| file | what it is | written by |
|---|---|---|
| `tests/conformance/manifest.tsv`, `*.skit` | the conformance targets: term, fuel, status, `copy` count | skijack `python3 -m skijack.export OUTDIR` |
| `dictionary.tsv` | distinct corpus terms, `hash atoms printed-term`: residual jets | the same |
| `dictionary_names.tsv` | `program name hash`: labels | the same |
| `interpreters.tsv` | interpreter jets' specs | the same |
| `namespaces.tsv` | the resume loop's runs | the same |
| `templates.tsv`, `template_terms.tsv` | supercombinator templates and the terms they reference | the same; `run0` for the front end |
| `words.tsv` | numeral operations: `hash op atoms printed-term`, written only when a program names one | skijack `templates.write_words` |
| `tests/data/*` | data-jet fixtures: two programs, their templates, words and names printed | `tests/data/export.py` |
| `tests/workloads/skilark/manifest.tsv` | SKIlark's workloads | skilark's export |
| `tests/workloads/reduceron/*.ascii.ski` | five Reduceron benchmarks in SKIjack; `run.py` compiles, runs and times them (`docs/BENCHMARK.md`) | written by hand |
| `jets/birds.tsv`, `jets/joy.tsv` | bird and Joy dictionaries; `*_names.tsv` label them | `jets/birds.py`, `jets/joy.py` |
| `tests/selfhost/*` | the compiler core's terms and calls | `tests/selfhost/export.py` |
| `tests/kernel/*` | kernel pills, events, expected values | `tests/kernel/export.py` |
| a front0 `DIR` | `front.skit`, the input's constructors, templates | skijack `run0.term_dir()` |

## The checks

| target | what it proves | needs |
|---|---|---|
| `make check` | every unit test, under ASan and UBSan | |
| `make selfhost-check` | the compiler core gives Python's result, hash for hash, for every abstraction of its own compilation and the corpus's, as a term and through its jet (§20.3) | skijack |
| `make front0-check` | the front end compiles its own source to Python's terms, and 67 edge programs and 1,000 random ones as spec0 does: as SKI, with templates, and with templates and data jets | skijack |
| `make witness-check` | the corpus's witnesses check and prove in lean-ski (§17) | lean-ski |
| `make jet-witness-check` | the same, jetted (§18) | lean-ski |
| `make probe-witness-check` | the same, with probe segments | lean-ski |
| `tests/diff_aviary.py` | `copy` mode against `aviary_kernel` on random terms | aviary-kernel |
