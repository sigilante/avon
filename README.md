# Avon

![](./img/hero.jpg)

Avon is a solid-state $SKI$ interpreter runtime with accelerated supercombinator support.  It is particularly designed to evaluate [SKIjack](https://github.com/sigilante/SKIjack) and [SKIlark](https://github.com/sigilante/SKIlark) programs.

Avon reduces the pure $SKI$ combinator calculus, and every acceleration it offers carries a licence: an argument that the fast path agrees with the term it replaces.  One term can therefore run fast, run conformant to the published contraction counts, or run as a zero-knowledge proof, and the three agree.

Avon also supports a "solid-state" event loop: a kernel with persistent state, updated by a poke and queried by a peek.  A kernel can also run as a program: `avon run --kernel FILE ARG…` performs the cards it emits, reading standard input, writing standard output and error, reading the environment and exiting with a status, as SKIjack's reference drivers do.

Avon was inspired by [Urbit](https://urbit.org), [NockApp](https://github.com/nockchain/nockchain/tree/master/crates/nockapp), and [PLAN](https://github.com/sol-plunder/reaver).  The underlying $SKI$ work was originally inspired by Stephen Wolfram's [_Combinators:  A Centennial View_](https://writings.stephenwolfram.com/2020/12/combinators-a-centennial-view/) and Raymond Smullyan's _To Mock a Mockingbird_.

## Details

Avon reduces closed $SKI$ terms, plus inert atoms, using three strategies:
- Copy mode reproduces the $SKI$ self-interpreter paper's contraction counts exactly. This is the conformance contract.
- Share mode is graph reduction with update in place, for speed. It is the default.
- Witness mode writes the tables lean-ski proves, byte for byte what lean-ski's own prover (ski-air) writes.

Around those it supports:
- code jets, including an interpreter jet;
- supercombinator templates, handed over by the front end or discovered in the term itself;
- data jets;
- a bound scry namespace that running code reads from; and
- a kernel loop with a persistent arena; and
- drivers, which run a kernel as a program (`avon run --kernel`), and durably in a pier (`avon boot --drivers`).

## Building

Avon is C11 with no dependencies.  It needs clang and GNU Make 3.81 or later.

```sh
make            # build/avon, optimized; about 3 s on an Apple M4 Max
make check      # 27 unit-test suites under ASan and UBSan; also build/dbg/avon; about 7.5 min
make smoke      # the release binary against 30 recorded commands
```

The build treats every warning as an error (`-Werror`), so a compiler other than the clang the Makefile names may fail it; `make CC=clang-18` picks another clang.  There is no install step: run `build/avon` in place.

## Quick start

A term is `S`, `K`, `I` and atoms.  Any other word is an atom, which never reduces.  Application is juxtaposition and associates left, so `S K K x` is `((S K) K) x`; parentheses group an argument.  `avon reduce` reads a term from a file or from stdin and prints the status and the number of contractions, then the term reached:

```console
$ echo 'S K K x' | build/avon reduce
NORMAL 2
x
$ echo 'S (K a) I b' | build/avon reduce
NORMAL 3
a b
$ echo 'K a (S I I (S I I))' | build/avon reduce --whnf
WHNF 1
a
$ echo 'S I I (S I I)' | build/avon reduce --fuel=5
FUEL 5
S I I (I (S I I))
```

The status is `NORMAL` (normal form), `WHNF` (weak head normal form, with `--whnf`), `FUEL` (the `--fuel` bound was spent) or `SIZE` (the node cap was reached).  Fuel is unbounded by default, so a term with no normal form runs until it is stopped.

Copy mode (`--strategy=copy`) counts as `aviary_kernel.reduce`, the Python reference host, does; share mode, the default, shares work and counts fewer contractions:

```console
$ echo 'S I I (K a b)' | build/avon reduce --strategy=copy
NORMAL 5
a a
$ echo 'S I I (K a b)' | build/avon reduce
NORMAL 4
a a
```

The repository carries the paper's three targets.  In copy mode, to weak head normal form, they take 340, 91,556 and 504,930 contractions:

```sh
build/avon reduce --strategy=copy --whnf tests/fixtures/t0.ski    # WHNF 340
build/avon reduce --strategy=copy --whnf tests/fixtures/t2.ski    # WHNF 504930
```

Jets leave every copy-mode count as it is; `--jet-check=1` checks each fire against the unjetted run.  The interpreter jet runs a generated interpreter's fuel loop natively, and changes counts, so it is off unless asked for:

```sh
J=tests/conformance
build/avon reduce --strategy=copy --whnf --jets=$J/dictionary.tsv --jet-check=1 tests/fixtures/t2.ski
#   WHNF 504930   (stderr: jets: 139 registered ..., 12801 fired)
build/avon reduce --strategy=copy --whnf --jets=$J/dictionary.tsv --interp=$J/interpreters.tsv tests/fixtures/t2.ski
#   WHNF 342
```

`docs/GETTING-STARTED.md` continues the tour: batches, the binary form, templates and data jets, kernels on a pier, scry and frame traces.

## Documentation

Start at [`docs/README.md`](docs/README.md), the index.  In brief:

- [`docs/GETTING-STARTED.md`](docs/GETTING-STARTED.md): a tour of the commands, with their output.
- [`docs/RUNTIME.md`](docs/RUNTIME.md): the reference for every command, option, file and exit status.
- [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md): a map of the source.
- [`docs/TESTING.md`](docs/TESTING.md): every check, and the outside checkouts some of them need.
- [`docs/DESIGN.md`](docs/DESIGN.md): the design, its reasons and its history.
- [`docs/SKA.md`](docs/SKA.md): how Avon recovers a program's functions, after Afonin's subject knowledge analysis.

## Checks that need other repositories

`make check` and `make smoke` need nothing outside this repository.  The other checks compare Avon with the implementations it must agree with, each a checkout at the revision pinned in `tests/pins.sh`:

| check | needs |
|---|---|
| `selfhost-check`, `front0-check`, `front1-check` | [SKIjack](https://github.com/sigilante/SKIjack) and [aviary](https://github.com/sigilante/aviary)'s `aviary_kernel` |
| `fixtures-check` | SKIjack, [SKIlark](https://github.com/sigilante/SKIlark) and aviary |
| `witness-check` and the other four `*-witness-check`s | [lean-ski](https://github.com/sigilante/lean-ski) |
| `hider-check` | the pure-S paper's scripts, not yet public |

`docs/TESTING.md` gives each check's variable, default path and running time.

## Status

Avon is a research proof of concept.  Built: the three strategies, jets, templates (from Python's front end, from front1 itself, or discovered with no front end), data jets, scry, kernels on a durable pier, the persistent arena, drivers in memory and in a pier (`avon run --kernel`, `avon boot --drivers`), and the SKIjack front end through its sixth milestone, which checks a program as Python's Stage A and Stage B do and compiles every corpus program to Python's terms.  Open: the proof-side items in `docs/DESIGN.md` §11.1.  The structural hash keeps 128 bits of SHA-256.  A jet fires only where its own term stands, so a collision cannot merge two jets.

## References

* N E Davis (2027, in review) A Self-Interpreter for $SKI$: Authoring Semantics for New Symbols. *Journal of Functional Programming*.  doi:10.5281/zenodo.22867957
* N E Davis (2027a, in review) SKIjack: A Low-Level Native Language for the $SKI$ Calculus.  *The Art, Science, and Engineering of Programming*.

## Licence

MIT; see [`LICENSE`](LICENSE).
