# Avon

![](./img/hero.jpg)

Avon is a solid-state $SKI$ interpreter runtime with accelerated supercombinator support.  It is particularly designed to evaluate [SKIjack](https://github.com/sigilante/SKIjack) and [SKIlark](https://github.com/sigilante/SKIlark) programs.

Avon supports a "solid-state" event loop, by which we mean that it has a kernel with a persistent state that can be queried and updated, using a poke and peek operation respectively.

Avon was inspired by [Urbit](https://urbit.org), [NockApp](https://github.com/nockchain/nockchain/tree/master/crates/nockapp), and [PLAN](https://github.com/sol-plunder/reaver).  The underlying $SKI$ work was originally inspired by Stephen Wolfram's [_Combinators:  A Centennial View_](https://writings.stephenwolfram.com/2020/12/combinators-a-centennial-view/).


## Building

Avon is C11 with no dependencies. It needs clang and GNU Make 3.81 or later.

```sh
make                    # build/avon, optimized
make check              # unit tests under ASan and UBSan; also build/dbg/avon
build/avon reduce --strategy=copy --whnf tests/fixtures/t0.ski
```

`avon reduce` reads a term in the printed form of `aviary_kernel.terms.pretty`
and prints the status, the contraction count, and the term reached.
`--strategy=copy` reproduces the reference host's contraction counts, and
`--strategy=share` (the default) reduces in place. `docs/DESIGN.md` is the
design and the build plan.

`--jets=tests/conformance/dictionary.tsv` loads skijack's dictionary as jets
(`docs/DESIGN.md` §6): residual jets, which leave every `copy`-mode count
exactly as it is without them. `--jet-check=1` checks every fire against the
unjetted run. `--interp=tests/conformance/interpreters.tsv` (with `--jets`)
adds the interpreter jet (`docs/DESIGN.md` §7), which runs a generated
interpreter's fuel loop natively: T2 falls from 504,930 contractions to 342.
It changes counts, so it is off unless asked for.

`tests/diff_aviary.py` checks `copy` mode against `aviary_kernel` on random
terms, and `tests/fixtures/export.py` regenerates the paper's targets. Both
need `aviary-kernel` installed. `make witness-check` proves the corpus's
witnesses with lean-ski's checker and prover (`docs/DESIGN.md` §17). The
conformance corpus under `tests/conformance/` is written by skijack's
`python3 -m skijack.export`.
