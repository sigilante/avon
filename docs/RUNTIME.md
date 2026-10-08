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

**Exit status.** A run's status is its line's, for a script to read: a
term that runs out of fuel or room still exits 0. Exit 1 is a failure of
Avon's own:
- a `--jet-check` that found a jet disagreeing with its term;
- output that could not be written, a full disk or a closed pipe;
- an input that does not parse.

Exit 2 is a usage error.

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
| `--max-nodes=N` | live nodes allowed after a collection before `SIZE`; by default physical memory over 64 bytes (between 2^20 and 2^30), so that a run's collections stay within the host's memory |
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
| `--fix` | with `--templates`: Curry's Y at the head with an argument, `Y g`, rewritten to `g (Y g)` in one step (§6.11) | `share` only | one step per unfolding, reported |
| `--memory` | with `--templates`: `--fix`, and every unfolding of a generator `g` passes on one `Y g`, never written, leading to one shared unfolding (§6.11, "Shared"): peak memory of a few MB where `--fix` holds hundreds, at about `--fix`'s time | `share` only | one step per unfolding, and one per call through the shared `Y g`, reported |
| `--no-defer` | with `--templates`: every instance writes its root and spine at once, as before deferred roots (§6.13), for comparing the two | `share` only | none: every count and state is the same |
| `--p2=FILE` | lean-ski's Poseidon2 term `P` (`lake exe p2run` writes `P.dag`): `P` applied to a state of sixteen 31-bit elements runs natively (§6.12) | `share` only; `copy` refuses | one step per permutation, reported |

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

**Y unfolded** (`--fix`, §6.11) prints a third line,
`fix: 124279 unfoldings of Y among the contractions`. The rewrite is
convertible, not a reduct: normal forms and answers are SKI's, a term
without a normal form still stops at FUEL, and a WHNF state may differ in
form (`Y K` stops at `K (Y K)`).

**Poseidon2 run natively** (`--p2=FILE`, §6.12) prints
`p2: 1 occurrences of P bound (skijack-1:43f97c21e068ebe7); 1
permutations run natively among the contractions, 0 declined (an argument
neither a state nor a chain of calls ending in one), 0 unbound at a call`. FILE must hold
lean-ski's `P`: Avon pins its 256-bit digest and refuses any other term. Only a jet node whose term is `P`'s,
node for node, fires. `P` fires on a state as it stands, or on a chain
`P (P … x)` ending in one, innermost call first; it runs its term on
anything else, counted as a decline, so the normal form is SKI's. Any
other computation between calls, `P (f (P x))`, declines unless each
state is built before it is passed on.

```sh
(cd ~/lean-ski && lake exe p2run 1 /tmp/p2)
build/avon reduce --p2=/tmp/p2/P.dag /tmp/p2/p2.dag   # NORMAL 1, then p2.expected
```

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

`front0` also takes `--templates=DIR`, `--data`, `--fix`, `--profile=NAMES`, `--jets=DICT`,
`--ctors[=N]`, `--jet-stats[=N]`, `--names=FILE`, `--fuel=N` and
`--max-nodes=N`.
- `--fuel` bounds the whole read: every probe draws on the same fuel.
- A name the result holds is at most 65,536 characters, with no control
  character or space, since the output is a line per name with a tab
  before its hash. A result that breaks either rule is refused.

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
build/avon boot --pier=/tmp/epier --entropy tests/kernel/entropy.pill.skit   # answers requests for bits
build/avon poke --pier=/tmp/epier tests/kernel/entropy.ask5.skit
```

- `boot PILL` applies the pill to the initial subject (`--subject=FILE`,
  default `I`). Without `--pier` it only reports whether the value is a
  kernel.
- `boot --pier=DIR` makes DIR 0700 and its files 0600, since a pier holds
  the kernel's entropy. It also takes a DIR that already exists, if the
  directory is empty, yours, and 0700.
- A pier replays its logged events with no fuel limit and no interrupt,
  whatever this run's `--fuel`. A logged event that does not replay stops
  the open, and its record stays in the log. Only a record torn by a crash
  is dropped.
- One process holds a pier at a time; a second gets "the pier is in use".
- On a `--pma` pier, if the image fails to commit after an event applied,
  `poke` says the event applied and is logged, and exits 1. Do not poke
  that event again: a reopen replays it.
- `boot --pma` makes the pier a persistent arena, committed after every
  event (§19); otherwise a pier is an event log and snapshots, and
  `--snapshot` on `poke` or `load` takes one. `--pma` matters only to
  `boot`: the pier remembers which it is.
- `boot --entropy` opts the pier into entropy (§9.1): it answers each
  request `[0 id]` in a poke's effects list with the event `[0 [id
  bits]]`, 128 Scott Booleans, logged before it applies, and boot's own
  request with the first event. Each reply prints as `event N, an entropy
  reply, …`. One outside event draws 16 replies at most. Every outside
  event must be a cell `[tag data]` whose tag a probe shows nonzero; any
  other is refused. A reply that cannot be drawn leaves its event applied,
  and the failure is reported after it.
- `boot --entropy=FILE` makes a test pier, whose bits come from FILE, from
  byte 16 n, n the replies already logged; every later `poke` must give
  `--entropy=FILE` too, and a pier booted with plain `--entropy` refuses
  one.
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

## Frame traces: `--trace-frame`, `enum`

For the pure-S paper's hider census (§22): an observation of copy mode's
head run on a term of S and one opaque atom, the passenger (`X` unless
`--passenger=NAME`). Verdicts and certificates stay with the census's
scripts; `tests/hider/client.py` runs the census through Avon:
`python3 tests/hider/client.py 16 build/avon 16` is the census of size 16
(`N AVON NMIN`), about six minutes.

```sh
echo "S (S S) (S S) S X" | build/avon reduce --trace-frame --fuel=600
build/avon enum 12 | sed 's/$/ X/' | build/avon batch --trace-frame=summary --fuel=600 \
    --records --frame-dump=census,halt
```

`--trace-frame` runs copy mode, head run only, never collecting, with no
jets; a term with K, I or another atom is refused. Options it would ignore
are refused: `--strategy=share`, `--jets`, `--ctors`, `--interp`,
`--jet-floor`, `--jet-check`, `--templates`, `--data`, `--fix`,
`--profile`. So are `--passenger`, `--records` and `--frame-dump` without
it. Each term gives one block:

```
> 1                       the term's input line
0 4 1 0 0 - 1             per step, before it: n L positions d D event arity
...
4 3 3 2 0 o 0
. WHNF 5 OPEN             status, contractions, exit: HALT-X HALT-B OPEN FUEL
                          (FUEL H OPEN: the opening contraction spent the last fuel)
R 3 9 ...                 records (--records), when the run reaches the horizon
C 3 9 ...                 the confirmed ones: n + CONF <= H (CONF 150)
K 3 4 2 0                 each confirmed record: n, L, the lowest X-headed position (- none),
                          and 1 if an X-headed item sits at L-1
d 7=X                     dumped nodes, once each, children first:
d 9=5.7                   S, X, or <left>.<right>
f 2 9 10                  a dumped frame: its step, then its items from the x-seat
$                         the block ends
```

- The frame is the S head's arguments, the first at the x-seat; positions
  count from the end, 1 the last item; `-` none.
- With exactly one X-headed item, the passenger P: `d = pos(P) - 1`, the
  stack depth, and `D` = the front items with sigma >= 1 plus the stack
  items with sigma >= 2, sigma(u) the X-headed items among u's head's
  arguments; otherwise `- -`.
- The event is the front-most passenger's seat: `o` the x-seat (OPEN: the
  census stops here; Avon takes one more step, to X at the head), `y` the
  y-seat, `z` the z-seat, `-` deeper. The arity is the front item's
  argument count (1 shed, >= 2 free at a y-step). A restart is a line with
  L = 3 and position 1.
- A halt (L < 3) is HALT-X with an X-headed item, HALT-B without.
- `--trace-frame=summary` omits the per-step lines.
- `--frame-dump=` takes steps and the keywords `records` (each confirmed
  record n and n+1: a second pass), `census` (only the frames the census
  reads, in its order over the confirmed records: frame n where an
  X-headed item sits at or below L-3, and it stops; else frame n+1, and it
  stops if one sits at L-1; also a second pass), `halt` (the final frame
  at a halt) and `last-restart`. `census` chooses frames, not verdicts.
- `reduce` and `batch` also read the DAG form, `dag 0=S 1=X 2=0.1 ... @2`
  on one line: a dumped term handed back without unfolding it. Ids are
  numbers below 2^64-1, local to the term, each defined once and before
  its use; the root comes last, and only blanks may follow it. Input that
  begins `dag ` is always read in this form, so an atom named `dag` cannot
  head a printed term there.
- `client.py` checks every position the census decides on against the
  dumped frames, and stops with an error, rather than a short count, if
  any avon process dies or the terms classified fall short of the
  Catalan count.

`avon enum N` prints every closed S-term of size N in the census's order,
N from 1 to 20: it keeps every tree below N as a node, 6.4 x 10⁸ of them
(6 GB) for N = 20 (`--start=K --count=M` for a slice; progress on stderr
every 10⁵); `avon
enum --base=FILE --shape=sxy,ssaq,hide` builds `S a q`, `S (S a) q` and
`S (S (S (S S) (S a))) q` for every ordered pair of the file's terms.

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
| `make hider-check` | `avon enum` gives the census's terms in its order; every frame trace of a term of size <= 12 equals the census's run line for line, and of size <= 10 at horizons 1 to 21; the census through Avon gives its verdicts and trails; the five named cases (§22) | the pure-S paper's scripts (`HIDER_SCRIPTS`) |
| `make front0-check` | the front end compiles its own source to Python's terms, and 67 edge programs and 1,000 random ones as spec0 does: as SKI, with templates, with data jets, and with Y unfolded | skijack |
| `make front1-check` | the full language's front end, through M4: its own source and every corpus program to the expander's terms, and 303 edge programs and 400 random ones as the expander does (bar 12 edges aviary's environment decides), in the same four modes | skijack |
| `make witness-check` | the corpus's witnesses check and prove in lean-ski (§17) | lean-ski |
| `make jet-witness-check` | the same, jetted (§18) | lean-ski |
| `make probe-witness-check` | the same, with probe segments | lean-ski |
| `make zk-jet-witness-check` | composed statements with jets: Avon's tables are ski-air's, accepted by `check-cj`, proved under hiding and verified; bad witnesses and budgets refused (`docs/ZK-JETS.md`) | lean-ski |
| `tests/diff_aviary.py` | `copy` mode against `aviary_kernel` on random terms | aviary-kernel |
