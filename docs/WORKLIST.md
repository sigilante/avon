# Worklist

What remains, in the order we mean to take it. `DESIGN.md` §11.1 records what is built;
this file records what is next. Each item names its decision state and where its
design lives. Last revised 2026-10-05.

## Done since the last revision

- **Pins tolerate documentation** (2026-10-11). `pin_check` accepts a checkout past its
  pin when every commit since, and every tracked change, touches only `*.md` files, so
  a WORKLIST commit in lean-ski or skijack no longer stops the checks. The pin must be
  an ancestor of the checkout; a rename counts on both sides.

- **lean-ski at master, past `paper-v4`** (2026-10-11). `tests/pins.sh` moves to
  `5614cb4`: `paper-v4` (`3e30892`), the lean-ski the Zero-knowledge SKI paper
  describes, and one WORKLIST change (#25). Its release script stops unless each of
  Avon's four jetted witness tables is ski-air's, byte for byte (lean-ski #22, #23). No
  Lean source changed since `paper-v2`; the five checks the pin serves pass at both
  `3e30892` and `5614cb4`. The checks default to `~/Code/ski/lean-ski`.

- **lean-ski at `paper-v2`** (2026-10-11; `ZK-JETS.md` §1 and §9). lean-ski's jet table
  no longer licenses a template that compiles to a bare `S`, `K` or `I`. `tests/pins.sh`
  moves to that commit, `79c7026`, and the five checks it serves pass there. Avon writes
  every jetted witness table byte for byte as ski-air does, and lean-ski #22 remakes its
  release from Avon's tables. `zk_jet_witness_check.sh` takes the too-small POP budget
  from the run's pops, and requires Avon's refusal to name the budget. It had taken the
  statement's budget less one, which `split8`'s 7,154 pops now fit.

- **The Poseidon2 jet, end to end** (2026-10-03 and 04; `ZK-JETS.md` §8, `DESIGN.md`
  §6.12). `avon witness` writes `p2pre` and `p2commit` tables byte for byte ski-air's
  (#8, #9); share mode runs lean-ski's `P` natively with `--p2` (#10); and the C is
  printed from a Lean proof that it computes the specification on every `uint32_t`
  state (`lean/P2Prog.lean`, `AvonP2.permuteC`, #11).

- **Chained Poseidon2 calls** (2026-10-04; `DESIGN.md` §6.12). `P (P x)` fires both
  calls natively, innermost first, in one walk down the chain: two steps and 0.03 s for
  test vector 1, against 981 million steps and 11 s when the outer call declined. A
  decline now checks the jet node's term too; before, a node made after the bind ran
  `P`'s registered term in place of its own over anything but a state.
- **Entropy for kernels** (2026-10-04; `DESIGN.md` §9.1, SKIjack SPEC §4.1). Per
  request: a pier booted with `--entropy` answers each `[0 id]` in a poke's effects
  list with the event `[0 [id bits]]`, 128 Scott Booleans, logged first, and boot's own
  request with the first event; `--entropy=FILE` for tests. Per request rather than with
  every event because a proved poke carries its whole event as private witness, and
  most events need no bits. lean-ski proves a poke of a reply with the bits private
  (2026-10-05, `Ski/Entropy.lean`).

- **`--memory`** (2026-10-05, #18; `DESIGN.md` §6.11, "Shared"). One `Y g` per
  generator, never written, and one shared unfolding: peak memory of a few MB where
  `--fix` holds hundreds, at about `--fix`'s time. Safe cycles parked on their measured
  ceiling (item 4). Integer literals proposed to SKIjack (issue #7).

## Next, in this order (agreed 2026-10-05)

1. **CI**: done 2026-10-05 (#19). `make check` on Linux for every pull request, and
   macOS too on master. The checks that need lean-ski or skijack checkouts stay manual.
2. **Check entropy against §9.1**: done 2026-10-05 (#20).
3. **Stage 8** (item 3) through M4: done 2026-10-05. Every corpus program compiles to
   Python's terms, hash for hash. The checkers, M5 and M6, follow the audit.
4. **A codebase audit**: done 2026-10-05 (`AUDIT.md`), by reviewers in parallel: failure paths, documentation
   against code, the build and its gates, the security edges, the shape of
   `reduce.c` and `main.c`. Slated into it: plain SKI's residual 1.9 to 3.9% since
   deferred roots (code generation), and deferral's 8 to 39 MB of extra peak memory with
   the same live set (the allocator).
5. **Fixes and hygiene refactors** from the audit's findings: done 2026-10-11 (#24 to
   #44), each its own pull request, in `AUDIT.md`'s order. Every item is closed: 25
   fixed, and the two measured (25, 26) closed with deferral retained.

## In progress

### 0. The papers' measurements (outline: the "Avon paper outlines" page)

Collected 2026-10-04: proof sizes and verify times (`ZK-JETS.md` §1), Poseidon2 on
all three vectors, and the interpreter jet's wall clock (`BENCHMARK.md`, "The
interpreter jet's wall clock"). Measuring the last found `av_equal` allocating on
every call; keeping its first stack and set on the C stack took T2 with the jet
from 0.95 ms to 0.41 ms. Open, with lean-ski:
- a statement with several jet calls;
- ski-air timing the proof's check apart from Lean's statement checks, since jets
  make verification slower (`split8` 23.0 s against 12.6) and the split is not
  measured.

### 1. Strictness: measured; the levers it found (`BENCHMARK.md`, "What becomes of an instance's cells")

Measured 2026-10-02 with `make stats` on the five Reduceron ports and the front end:

- **Primitive-redex speculation:** dropped. No numeral operation has both numerals
  held when its cell is written; the operands are thunks.
- **Head strictness:** not now. Thunks are 8 to 20% of cells, 50 to 91% are forced,
  and update in place already writes a forced value over its cell, so eager evaluation
  would save a revisit, not a node.
- **Case of a known value: built** (2026-10-02, `DESIGN.md` §6.10, "A case joined to
  its instance"). It is exact: every count and state is unchanged. It runs 0 to 9%
  faster (`BENCHMARK.md`, "A case joined to its instance"), but retires more
  instructions where most attempts fail. A cheaper test for "the formal is
  unevaluated" would recover them. Not yet tried on top of deferred roots, which changed
  the same instance path.
- **Spine cells: built** (2026-10-04, `DESIGN.md` §6.13, "Deferred roots"). An
  instance leaves its root and spine in the stack, written only when something else
  could read them. Every count and state is the same, and the five Reduceron ports
  run 5.8 to 14.5% faster (`BENCHMARK.md`, "Deferred roots"). Measured first: 55 to 95%
  of spine cells sit under a head that steps at once.

## Later

### 3. Stage 8: the full language's front end (`DESIGN.md` §20.3)

SKIjack-0's front end compiles itself in Avon. What remains runs in Python: cores,
macros, signatures, quotation, scries, namespace literals and the type checker. Most
of the work is SKIjack programs in skijack's repository; Avon runs them and checks them
on the corpus, hash for hash. It is the one unfinished stage. Next in order (step 3).

Scoped 2026-10-05, against skijack `6a870ac`. The SKIjack-0 front end
(`selfhost/front0.ascii.ski`) is 406 lines; Python's front end about 7,100. Sizes
are estimates, in lines of SKIjack:

| milestone | adds | size (estimated at scoping) | corpus programs matching (estimated) |
|---|---|---:|---:|
| M1 | wider lexer and parser, plain cores, hygienic macros, signatures parsed and dropped, the birds `B`, `C`, `W`, `Y`, the numeral operations | 150–250 | 5 of 17 |
| M2 | interpreter generation (`generate.py`): step and loop equations, names built at run time | 150–250 | 10 |
| M3 | quotation and level-1 runs: object leaves, encoding, `\|-`, fuel | 100–160 | 13 |
| M4 | scries, path literals, namespace literals | 60–110 | all 17 |
| M5 | Stage A (`check.py`): refusal parity, errors with a class | 250–400 | — |
| M6 | Stage B (`typecheck.py`): Hindley–Milner over an explicit store, equirecursive unification | 400–700 | — |

**M1 to M4, built 2026-10-05** (skijack `front1.ascii.ski`, `run1.py`; `make
front1-check`; `DESIGN.md` §20.3). Every corpus program agrees, hash for hash, and the
fixed point covers 1,009 names. Of 303 edge programs, aviary's environment decides 12,
not SKIjack's rules. Those are binders named as defined names or built-ins, a binder
twice, a recursion's name rebound, and a binder named as a later definition, which
aviary reads as the definition. front1 takes each binder as a binder; parity there is
M5's. Left for the audit: front1's term grew from 265,145 nodes to 635,173, so Python
compiles it in 48 seconds.

Checking never changes the terms, so M1 to M4 are each checked against
`skijack.compile(..., check=False)` on the corpus as they land, with `run0.py`'s
random and edge programs extended. The front end stays a separate program from
`front0`, whose fixed point stays as it is; the reader `avon front0` serves both while
the result's shape is kept. Hard parts, from the scoping: no parametric types, so
every table is its own trie (generate them, as `tables.py` does); names built at run
time need the intern table kept past lexing; Python's output order (compare as a
map, or reproduce it).

### 4. Safe cycles for Y: parked 2026-10-05 (`DESIGN.md` §6.11)

Measured first (`BENCHMARK.md`, "Y shared (`--memory`)" and "The ceiling for a
true cycle"):
- Nearly all of a port's live set is Y's unfoldings. `--memory` (one shared `Y g`
  per generator, acyclic) cuts peak memory to 4 to 8 MB, at `--fix`'s time.
- A true cycle, grafted onto today's code, would take 1.12 times less time than
  `--fix` by geometric mean (1.00 to 1.25), with `--memory`'s memory.

Parked on that: 12% does not pay for what a safe cycle needs.
- indirection writes checked never to close a loop (`av_res` and the collector
  spin on one);
- re-entry of a knot under evaluation turned into fuel, as SKI runs forever;
- a normal-form pass that refuses infinite terms;
- no cycle leaving a reduction: every exit, kernel pokes included, breaking each
  knot's back-edges, or every walk and snapshot learning cycles;
- copy mode and the witness without cycles; for proofs, a lean-ski heap semantics.

If taken up: cycles inside `reduce` and `batch` only, broken at every exit, kernels
refusing the flag; measure the cost of breaking them before going further.

## Handed to lean-ski

### 5. The proof gaps (`DESIGN.md` §11.1, "Open")

- Witnesses for terms with atoms (§17.3).
- Scry beyond a resume loop's final run.
- Witness rows for the numeral and constructor jets and the one-step Y, with the
  `Tr` simulation theorem (§6.11). Poseidon2 has them (`ZK-JETS.md` §8).
- The Poseidon2 tables' constraints (`Sat`): the honest tables are proved to balance
  and to carry clear flags, but not to satisfy each AIR.
- Fiat–Shamir and ChaCha20's pseudorandomness, both assumed (`ZK-JETS.md` §7).

When lean-ski changes a table format or the prover's inputs, Avon matches it and
reruns `make zk-jet-witness-check`.

## Small items

### 6. From the reviews of avon PR #3

None of these changes a result.

- **Probed 2026-10-04:**
  - `enum --base` with an empty file prints nothing and says so; a malformed
    line now names its file and line, and no longer adds a false "out of memory".
  - `dag` input of 1.2 million nodes, right-deep, left-spined and an exponential
    tree shared as a DAG, under ASan in both strategies: clean, under 0.6 s each.
  - `--records` near `SIZE_MAX` wrapped `n + CONF` and confirmed every record;
    fixed (`trace.c`, `confirmed`), with a test of four windows past the horizon.
- **Noted, left as they are:**
  - the reservation `assert`s in `jets.h` vanish in release builds;
  - `word_admit`'s 10,000,000-step cap counts a slow operation as refused;
  - SKIjack's inliner falls back silently when it hits its budget or depth.

## Parked

- **SKIjack PR #2, the Rust port.** Out of scope for the SKIjack repository; parked
  2026-10-02. Its manifest is 19 commits behind master.
