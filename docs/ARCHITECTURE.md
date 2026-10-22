# Architecture

A map of Avon's source: what each file does, and how a term moves through
them.  `DESIGN.md` gives the reasons; this page gives the places.

## A term's path through `avon reduce`

1. **Read.**  `term_main` (`src/cli/term.c`) reads FILE or stdin
   (`slurp`, `src/cli/common.c`) and `load` tells the form apart: printed
   or DAG (`src/read.c`), SKIT (`src/wire.c`), prefix (`src/witness.c`).  The
   term becomes nodes in an arena (`src/arena.c`): eight bytes each,
   addressed by 32-bit index, S, K and I interned at 0, 1 and 2.
2. **Match.**  With `--jets`, `--ctors`, `--templates` or `--p2`, the
   structural hash (`src/jets.c`) finds the subterms the dashboard knows
   and binds each to its jet; templates (`src/tmpl.c`) and words
   (`src/words.c`) register theirs the same way.
3. **Reduce.**  `av_reduce` (`src/reduce.c`) runs the copy machine
   (`src/copy.c`, the reference host's algorithm, whose counts are the
   papers') or the share machine (`src/reduce.c`, graph reduction with
   update in place, its spine in `src/stack.h`).  Both machines share their
   state and helpers (`src/machine.h`) and collect through `src/gc.c`.
   Jets fire from the reducer: residual jets (`src/jets.c`), templates,
   data jets, the interpreter jet (`src/interp.c`), the compiler jet
   (`src/compiler.c`), the unquoter (`src/install.c`) and Poseidon2
   (`src/p2.c`).
4. **Print.**  `src/print.c` writes the printed form under a node budget,
   or `src/wire.c` jams the result.

`avon witness` replaces step 3 with `src/witness.c`, lean-ski's heap
machine run as written, and prints its table.  `--trace-frame` adds an
observer to the copy machine (`src/trace.c`).

## Reading values: probing

Avon reads what a term means by applying it to fresh marker atoms and
watching which comes back (`src/probe.c`): a Scott numeral, a Boolean, a
constructor and its fields.  Scry (`src/scry.c`), the kernel
(`src/kernel.c`), install (`src/install.c`) and the front end
(`src/front0.c`) all read their results this way.

## Kernels and piers

`src/kernel.c` is the kernel door: a pill applied to a subject gives a
kernel `[battery state]`, which `poke` applies to an event and `peek` to a
path, both by axis.  `src/pier.c` keeps a kernel's home: the event log,
synced before an event applies, snapshots (`src/snap.c`) with checksum
sidecars, a lock, and the entropy replies.  `boot --pma` keeps the arena
itself in a mapped file with a redo journal instead (`src/pma.c`).  Every
sync that must reach the disk goes through `src/durable.c`.

## The files

`include/`

| file | what it holds |
|---|---|
| `avon.h` | the runtime's public interface: the arena, the reducer and its options, jets, the wire forms, witness, probing, scry, kernels and piers |
| `ski.h` | the calculus independent of storage: leaves (S, K, I and atoms), their arities, expressions as trees |

`src/`, the runtime

| file | what it does |
|---|---|
| `arena.c` | allocation, leaf interning, caller roots, the default node cap |
| `read.c` | the printed form and the DAG form, parsed without recursion |
| `print.c` | the printed form, written without recursion under a node budget |
| `wire.c` | terms at rest: the SKIT container, Tromp's bitstring with a third leaf, the atom-name hygiene check |
| `sha256.c` | SHA-256 (FIPS 180-4), for snapshot checksums and the structural hash |
| `gc.c` | stop-and-copy collection, Cheney's scan with forwarding in a side array |
| `machine.h` | the state both machines run on, and their shared helpers |
| `copy.c` | the copy machine: `aviary_kernel.reduce`'s algorithm on nodes |
| `reduce.c` | the share machine, jet and template dispatch, and the `av_reduce` driver |
| `stack.h` | the share machine's spine stack, with deferred roots |
| `jets.c`, `jets.h` | the structural hash, the dashboard, residual jets, the loader's match |
| `tmpl.c` | supercombinator templates, each checked by abstracting its body back to its key |
| `words.c` | Scott numerals held as numbers, and the numeral operations on them |
| `interp.c` | the interpreter jet: a generated interpreter's fuel loop, run natively |
| `compiler.c` | the compiler jet: bracket abstraction run natively, checked against its term |
| `install.c` | install: an encoded term becomes the live term it encodes; the unquoter's jet |
| `front0.c` | running the SKIjack-0 front end, and reading its output by probing |
| `probe.c` | reading values by applying terms to marker atoms |
| `scry.c` | the fact store, its resolver, and the resume loop |
| `kernel.c` | the kernel door: boot, poke, peek, load |
| `pier.c` | a kernel's durable home: event log, snapshots, lock, entropy |
| `snap.c` | arena snapshots, with checksum sidecars |
| `pma.c` | the persistent arena: a mapped node image and a redo journal |
| `durable.c`, `durable.h` | syncs that reach the disk (`F_FULLFSYNC` on macOS) |
| `witness.c` | the witness strategy: lean-ski's machine, its trace written as a table; and the prefix form's reader and writer |
| `p2.c`, `p2_consts.h`, `p2_prog.h` | Poseidon2 over BabyBear and its jet; the two headers are generated from Lean |
| `census.c` | a census of the terms a run calls, for choosing jets |
| `jetstats.c` | each jet's fires, misses, demotions and their origins |
| `profile.c` | which named terms a share-mode run's contractions execute |
| `trace.c` | frame traces and the defect count, for the pure-S paper's census |
| `sstats.h` | strictness counters, built only by `make stats` |

`src/cli/`, the command line: one file a command, over `cli.h`

| file | commands |
|---|---|
| `main.c` (in `src/`) | dispatch, the usage text, `--version` |
| `common.c` | number parsing, reading a file, loading a term in any form |
| `term.c` | `reduce`, `batch`, `jam`, `cue`, `prefix`, `witness`, and `options_fit`, which refuses an option the command would ignore |
| `kernel.c` | `boot`, `poke`, `peek`, `load` |
| `scry.c`, `census.c`, `jetstat.c`, `selfhost.c`, `front0.c`, `enum.c` | the command each is named for |

Outside `src/`

| path | what it holds |
|---|---|
| `lean/P2Prog.lean` | the Lean program printed as `src/p2_prog.h`, with its proof against the specification |
| `jets/` | the bird and Joy jet dictionaries and the scripts that write them |
| `tests/test_*.c`, `tests/test.h` | the unit suites (`TESTING.md`) |
| `tests/*_check.sh`, `tests/pins.sh` | the checks against other repositories, and their pins |
| `tests/smoke.sh`, `tests/smoke.tsv` | the smoke test |
| `tests/fixtures/`, `tests/conformance/`, `tests/data/`, `tests/kernel/`, `tests/selfhost/`, `tests/workloads/` | fixtures exported from SKIjack, SKIlark and aviary, each with its exporter |
| `tests/hider/` | the pure-S paper's census, driven through Avon |

## Conventions

Comments stand alone: they say what they mean without citing `DESIGN.md`
sections, though pointers to other projects' specifications stay.  A
term's depth is unbounded, so the reader, the printer, `jam` and `cue`
work from explicit stacks rather than recursion.  An option a command would
ignore is refused, not accepted.
