# Getting started

A tour of Avon's commands, each with the output it prints.  Every command
runs from the repository root on files in the repository.  `RUNTIME.md` is
the reference for each command's options; this page shows what they do.

## Words used here

- A **contraction** is one rewrite: `S x y z` to `x z (y z)`, `K x y` to
  `x`, `I x` to `x`.  Avon reports how many a run took.
- A term is in **normal form** when no contraction applies anywhere in it,
  and in **weak head normal form** when none applies at its head.
- **Fuel** bounds the contractions a run may take.
- An **atom** is any name but `S`, `K` and `I`.  It never reduces.
- A **jet** is native code that stands for a term.  Avon keeps a jet only
  where it can show the jet agrees with the term; `RUNTIME.md` and
  `DESIGN.md` §6 (Jets) say how.

## 1. Build

```sh
make            # build/avon, in about 3 s on an Apple M4 Max
make check      # the unit tests under the sanitizers, about 7.5 min
```

## 2. Reduce a term

Application is juxtaposition and associates left: `S K K x` is
`((S K) K) x`.  `reduce` reads a file, or stdin when none is named, and
prints the status and the contractions, then the term:

```console
$ echo 'S K K x' | build/avon reduce
NORMAL 2
x
$ echo 'K a b' | build/avon reduce
NORMAL 1
a
$ echo 'S (K a) I b' | build/avon reduce
NORMAL 3
a b
```

`--whnf` stops at weak head normal form, so an argument left unreduced
stays as it is:

```console
$ echo 'S K K x (S K K y)' | build/avon reduce --whnf
WHNF 2
x (S K K y)
$ echo 'K a (S I I (S I I))' | build/avon reduce --whnf
WHNF 1
a
```

`S I I (S I I)` has no normal form.  Fuel is unbounded by default, so
bound it:

```console
$ echo 'S I I (S I I)' | build/avon reduce --fuel=5
FUEL 5
S I I (I (S I I))
```

A run that spends its last fuel on its last contraction still reports
`FUEL`: `echo 'K a b' | build/avon reduce --fuel=1` prints `FUEL 1` and `a`.

Names of aviary's combinators (`B`, `C`, `W`, `Y`, `Phi` and about forty
more) are refused as atoms, since a reader would take them for those
combinators; `--allow-bird-atoms` accepts them.

## 3. Two strategies

Copy mode, `--strategy=copy`, is the reference host's algorithm.  Its
counts are the ones the papers publish, and Avon reproduces them exactly.
Share mode, the default, is graph reduction: a redex that copying would
duplicate is contracted once, so it counts less.

```console
$ echo 'S I I (K a b)' | build/avon reduce --strategy=copy
NORMAL 5
a a
$ echo 'S I I (K a b)' | build/avon reduce
NORMAL 4
a a
```

The repository carries the self-interpreter paper's three targets.  In copy
mode, to weak head normal form, they take 340, 91,556 and 504,930
contractions, and `tests/fixtures/t0.whnf` holds the result Avon must give:

```sh
build/avon reduce --strategy=copy --whnf tests/fixtures/t0.ski | cmp - tests/fixtures/t0.whnf
build/avon reduce --strategy=copy --whnf tests/fixtures/t2.ski     # WHNF 504930
build/avon reduce --whnf tests/fixtures/t2.ski                     # WHNF 314309, share mode
```

## 4. Many terms: `batch`

`batch` reduces each line of stdin and prints a line per term:

```console
$ printf 'S K K x\nK a b\nS I I (S I I)\n' | build/avon batch --fuel=10
NORMAL 2 x
NORMAL 1 a
FUEL 10 I (S I I) (I (I (S I I)))
```

## 5. The binary form: `jam`, `cue`, `prefix`

SKIT is a binary container for terms, the one SKIjack writes.  `jam`
writes it and `cue` reads it back; `prefix` prints a closed term in prefix
form, a backquote before each application:

```console
$ T=$(mktemp -d)
$ echo 'S K K' | build/avon jam > $T/t.skit
$ build/avon cue $T/t.skit
S K K
$ build/avon prefix $T/t.skit
``SKK
```

Every command that reads a term reads all three forms.

## 6. Jets

`--jets` loads a dictionary of jets; the conformance dictionary, exported
from SKIjack's corpus, registers 139.  These are residual jets: they leave every
copy-mode count as the unjetted run has it.  `--jet-check=1` checks every
fire against the term it stands for:

```console
$ build/avon reduce --strategy=copy --whnf --jets=tests/conformance/dictionary.tsv --jet-check=1 tests/fixtures/t2.ski
jets: 139 registered (0 constructors found), 12801 fired (0 interpreter)
WHNF 504930
...
```

The interpreter jet runs a generated interpreter's fuel loop natively.  It
changes counts, so it is off unless asked for.  T2 is the self-interpreter
interpreting T0, which is itself the self-interpreter on `I K`; with the
jet, T2 takes 342 contractions in place of 504,930:

```console
$ build/avon reduce --strategy=copy --whnf --jets=tests/conformance/dictionary.tsv \
    --interp=tests/conformance/interpreters.tsv tests/fixtures/t2.ski
jets: 139 registered (0 constructors found), 1 fired (1 interpreter)
WHNF 342
...
```

Jet reports go to stderr, the result to stdout.

## 7. Templates and data jets

Share mode can run a program's functions as templates, instantiated in one
step, and hold numerals as machine numbers (`--data`).  `tests/data/nats`
is a small program with its templates; it reduces to the atom `Ff`:

```sh
D=tests/data/nats
build/avon reduce --whnf $D/main.txt                                  # WHNF 58360
build/avon reduce --whnf --templates=$D $D/main.txt                   # WHNF 7840
build/avon reduce --whnf --templates=$D --data $D/main.txt            # WHNF 5986
build/avon reduce --whnf --templates=$D --data --fix $D/main.txt      # WHNF 4201
build/avon reduce --whnf --discover $D/main.txt                       # WHNF 8205
```

The templates come from the compiler, which knew the program's functions.
`--discover` needs no file: it finds them in the term by inverting
bracket abstraction, and checks each as a loaded one is checked
(`SKA.md` §6).

Each option prints a report line on stderr.  None of them runs in copy
mode, which keeps its counts.

## 8. A kernel on a pier

A pill is a term that, applied to a subject, gives a kernel: a term with
state that events update and paths read.  A pier is the directory that
holds a kernel's event log and snapshots.  Events and paths are SKIT files:

```console
$ P=$(mktemp -d)/pier
$ build/avon boot --pier=$P tests/kernel/pill.skit
booted a kernel in /var/folders/.../pier
$ build/avon poke --pier=$P tests/kernel/events.tick.skit tests/kernel/events.poke5.skit
event 1, 52 contractions; effects: K
event 2, 86 contractions; effects: K (S (S I (K (S I (K (K (S I (K K))))))) (K K))
$ build/avon peek --pier=$P tests/kernel/events.zero.skit
130 contractions: K (S I (K (K (S I (K (K (S I (K (K (S I (K (K (S I (K (K (S I (K K)))))))))))))))))
```

The pier now holds `events.log` and the snapshot `snap-0` with its
checksum, all readable by you alone.  A pier takes one boot; boot into a
fresh directory each time.  `boot --pma` keeps the kernel's arena in a
mapped file instead, and `boot --entropy` lets the kernel ask for random
bits (`RUNTIME.md`, "Kernels").

A kernel can also run as a program, with no pier.  `run --kernel` takes
the kernel itself, not a pill, and performs the cards it emits: writes,
reads of standard input, environment variables, step counts and an exit.
`tests/drivers/echo.skit` greets and copies its input; `show.skit` writes
its name and `$HOME`, with no newline after it, then exits 7:

```console
$ printf 'hello, world\n' | build/avon run --kernel -- tests/drivers/echo.skit
hi
hello, world
$ build/avon run --kernel -- tests/drivers/show.skit; echo " status $?"
tests/drivers/show.skit
/Users/you status 7
```

`boot --drivers --pier=DIR` runs it in a pier instead, each answer
logged before it is applied; `boot --drivers --pier=DIR` without the file
reopens the run, replaying it, after a crash or after it ended.

Plain `run FILE`, without `--kernel`, is `reduce FILE` (`RUNTIME.md`,
"Programs").

## 9. Scry

A scry is a read-only lookup by path that a program makes; a program that
asks for a fact not yet known blocks, and runs again when the fact
arrives.  `scry` runs the corpus's namespace programs and checks each
against the reference:

```console
$ build/avon scry tests/conformance/namespaces.tsv
scry-block.no-scry: RValN
  rounds 1; attempts (fuel:status:contractions) 10:WHNF:556
  facts 0
scry-block.one-block: BLOCK on K|RValN
...
```

## 10. Frame traces

`--trace-frame` reports, before each step of a pure-S term's head run, the
facts the pure-S paper's census reads: the frame's length, where the
passenger atom `X` sits, and the event.  `enum` lists the closed S-terms of
a size:

```console
$ build/avon enum 4
S (S (S S))
S (S S S)
S S (S S)
S (S S) S
S S S S
$ echo 'S (S S) (S S) S X' | build/avon reduce --trace-frame --fuel=600
> 1
0 4 1 0 0 - 1
1 4 1 0 0 - 0
2 3 1 0 0 z 2
3 4 2 1 0 z 0
4 3 3 2 0 o 0
. WHNF 5 OPEN
$
```

`RUNTIME.md`, "Frame traces", explains each field.

## 11. A witness

`witness` writes the table the lean-ski prover proves for a run, and its
size on stderr:

```console
$ build/avon witness tests/fixtures/t0.ski > $(mktemp -d)/t0.witness
contractions 340 rows 831 cells 2369 loaded 1366 insts 0
```

Checking and proving it needs [lean-ski](https://github.com/sigilante/lean-ski).

## Next

- `RUNTIME.md`: every command, option, file and exit status.
- `ARCHITECTURE.md`: where each of these lives in the source.
- `TESTING.md`: the checks, and what they need.
- `DESIGN.md`: why Avon is built this way.
