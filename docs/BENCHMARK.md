# Benchmarks

What was measured, at which commits, and how to measure it again. The
design each measurement informed is in `docs/DESIGN.md`; the commands are
in `docs/RUNTIME.md`.

**Counts are exact, times are not.** A contraction count depends only on
the term, the strategy and the jets, and reproduces exactly at the same
commits. Times were taken on one machine, often under load, and are given
as the method says (best of five, interleaved, user CPU) where that method
was used; a single wall-clock figure is marked as one.

**The machine.** Apple M4 Max, 16 cores, 48 GB, macOS 26.6.2, Apple clang
21.0.0 (Command Line Tools), `make` (`-O2`). Load averages during runs
ranged from about 5 to 12, mostly a browser.

## The SKIjack-0 front end compiling itself

The headline workload: skijack's front end, a SKIjack program compiled to
one term, run in Avon's `share` mode on its own source, reaching every
name's term hash for hash with Python's (§20.3). Each row changed one
thing; the source grew along the way, so the names column is the program's
size.

| # | avon | skijack | change | names | contractions | time |
|---|---|---|---|---:|---:|---|
| 1 | `52093bc` | `a333629` | the first fixed point | 375 | 2,176,424,461 | about 40 s wall, renderer included |
| 2 | `a3b36ff` | `8b861ee` | linear recursion analysis; search trees for rules, memo, names | 433 | 1,262,327,332 | 16 s wall, Avon alone |
| 3 | `8d80314` | `711d6c4` | identifiers interned; tries keyed by their bits | 492 | 740,558,347 | 10.5 s wall, Avon alone |
| 4 | `eb054d8` | `e706d6e` | the result read by probing (`avon front0`), no renderer | 492 | 306,991,371 | 8.0 s wall; 4.38 s user, best of 5, at `a0fba14` without templates |
| 5 | `a0fba14` | `5f81687` | supercombinator templates (§6.9) | 492 | 21,238,890 | 0.97 s user, best of 5 |
| 6 | `f414272` | `8b34529` | data jets (§6.10): constructors dispatched, fused into the branch | 492 | 17,389,998 | 0.92 s user, best of 5, against row 5's 0.96 s run beside it |

- Rows 1–3 wrote the result out through a renderer (`render0.ascii.ski`)
  as a tree of marker atoms for `avon reduce` to print; its contractions
  are in their counts. The profile put the renderer at 13.8% of row 1,
  32.7% of row 2 and 29.3% of row 3.
- Row 5's 21,238,890 includes 18,930,884 template instantiations, one step
  each. Of its 0.97 s, 0.39 s loads and checks the templates (6 MB of
  printed terms); the compile itself took about 0.58 s against row 4's
  4.38 s.
- Avon's commit is the binary each row ran. `b984542` changed only
  DESIGN.md, so row 2 is the same at either. At `a0fba14` without
  `--templates`, row 4's workload takes the same 306,991,371 contractions
  it took at `eb054d8`.
- Row 6's 17,389,998 includes 6,554,787 instantiations and 8,527,205
  dispatches, 3,848,892 of them fused into the branch's template. The
  front end names no numeral operation; 9 closed numerals became words.
  Both row 5 and row 6 load templates for about 0.39 s, so the compile
  itself went from about 0.57 s to 0.53 s.
- Every row's output is the same set of terms, checked by hash against
  Python's; rows 4, 5 and 6 also agree with each other byte for byte.

**Reproduce.** At the listed commits, from skijack's `python/`:

```sh
PYTHONPATH=. python3 -m skijack.selfhost.run0 --avon ~/avon/build/avon            # rows 1-4
PYTHONPATH=. python3 -m skijack.selfhost.run0 --avon ~/avon/build/avon --templates  # row 5
PYTHONPATH=. python3 -m skijack.selfhost.run0 --avon ~/avon/build/avon --templates --data  # row 6
```

The fixed-point line reports the contractions.

### Where row 1's time went, and what rows 2–4 changed

The profile (`avon reduce --profile`, §6.7, avon `a3b36ff`) charges each
contraction to the named code it runs. On row 1:

| | share |
|---|---:|
| name comparison (`eqCode`, `eqName`, `eqBit`, `andB`, `notB`) | 39.5% |
| built at run time (S, K, I: Scott dispatch the cases read) | 32.2% |
| the renderer | 13.8% |
| everything else | 14.5% |

Split by call site, the recursion analysis's quadratic comparisons were
24.5% and the memo's linear scans 4.7%. Rows 2 and 3 removed them. After
row 2, name comparison was 11.4% of the run.

## Jets on the front end

Measured at avon `7e6ff17`, skijack `e706d6e` (row 4's front end), each
output checked identical to the unjetted run. *Work* is contractions
stepped plus fires, since a fire in `share` mode is charged its copy cost.

| jets | work | user time, best of 5 |
|---|---:|---:|
| none | 306,991,371 | 5.31 s |
| birds (`jets/birds.tsv`) | 271,732,988 (−11%) | 5.31 s |
| constructors (`--ctors`) | 228,890,634 (−25%) | 5.12 s |
| census top 40 and birds | 317,361,509 (+3%) | 7.58 s |
| its own rules, 5–64 atoms | 353,526,862 (+15%) | 7.20 s |
| all of these | 251,033,829 (−18%) | 7.41 s |

These timings ran under a load average near 12, which is why "none" is
5.31 s here and 4.38 s in row 4.

- Residual jets for all 747 of the front end's rules of eight atoms or
  more had not finished after 13.5 minutes. A separate run of the 587
  rules over 64 atoms, capped at 30 million contractions, never missed and
  demoted four times: the cost was the fires, each instantiating a large
  residual, not demotion.
- A first constructor-jet run did not finish in 20 minutes: the constructor
  scan sized each subterm with its own walk. Avon `8d80314` sizes every
  node in one pass, and the scan takes seconds.

Templates (row 5) are the jet mechanism that pays here: they instantiate
the compiler's own supercombinators without copying what sharing reduces
once.

## Jets on the corpora, together and alone

`avon jetstat` (avon `7e6ff17`) on skijack's conformance corpus and
SKIlark's workloads, 84 runs that halt (`--halting` leaves out two
fuel-bounded loops, 800,000 of the 2.66 million contractions). The jets:
`census --top=40 --emit` (201 rows with their layers) and the 153 bird
encodings, 348 registered.

| | copy | share |
|---|---:|---:|
| contractions, no jets | 1,858,830 | 1,169,837 |
| absorbed by the jets together | 1,313,452 | 1,228,237 |
| fires | 109,793 | 90,848 |
| contractions stepped, with jets | 545,378 | 202,448 |
| each jet alone, summed | 11,329,207 | 10,886,105 |

- Together the jets absorb 88% less than their alone figures summed:
  small patterns are eaten by the supercombinators around them.
  `S (K (S (K K)))` absorbs 216,345 alone and 28,250 together; T 147,292
  and 6,136; Cons 188,005 and 39,235.
- Every nested fire came from another jet's residual (Y fires L 14,792
  times, L fires KM 16,567); none from a term entered after a miss. There
  were 61 misses in all.
- Every `copy` count, with jets on, equals the manifest's.

## Templates on the corpus

Avon `a0fba14`, skijack `5f81687`: the 43 conformance runs that halt, in
`share` mode, with the corpus's templates (`templates.tsv` from
`skijack.export`), fuel ten times the manifest's.

| | steps |
|---|---:|
| SKI | 640,853 |
| with templates | 63,774 (36,616 instantiations) |

Every run reaches the same normal form. Of the corpus's 240 templates,
110 are used: 128 are the constructors of a 128-way character type, past
the 32 arguments a template takes, and 2 are duplicates or bare leaves.

## Against the Reduceron

The Reduceron is Naylor and Runciman's template-instantiation machine on
an FPGA ("The Reduceron reconfigured and re-evaluated", JFP 22(4–5), 2012).
Its benchmarks are small lazy programs in F-lite, a subset of Haskell. Five
of them are ported to SKIjack in `tests/workloads/reduceron/`: OrdList
and Queens2, which the paper calls purely symbolic; Clausify, almost so;
and Taut and PermSort, whose integers are small. Avon runs each at `0c7682b`, compiled by
skijack `bbb2ff4`, in `share` mode, as SKI and with templates (§6.9).

### The published numbers

From the paper: Table 6 (the Reduceron on a Virtex-5 at 96 MHz), Table 5
(GHC 7.0.3 `-O2` on a 3 GHz Core 2 Duo) and Table 7 (hand-reductions per
clock cycle). A hand-reduction is a function or primitive application,
counting the functions case compilation introduces and excluding
constructor reduction, updating and unwinding.

| program | Reduceron, s | GHC, s | hand-reductions per cycle |
|---|---:|---:|---:|
| Adjoxo | 0.39 | 0.07 | 0.65 |
| Braun | 0.74 | 0.27 | 0.46 |
| Cichelli | 0.41 | 0.06 | 0.52 |
| Clausify | 0.73 | 0.20 | 0.54 |
| CountDown | 0.19 | 0.05 | 0.62 |
| Fib | 2.52 | 0.28 | 0.90 |
| KnuthBendix | 0.19 | 0.05 | 0.47 |
| Mate | 6.74 | 0.66 | 0.52 |
| MSS | 0.69 | 0.13 | 0.65 |
| OrdList | 0.98 | 0.61 | 0.43 |
| PermSort | 1.62 | 0.51 | 0.43 |
| Queens | 1.00 | 0.11 | 0.72 |
| Queens2 | 1.29 | 0.47 | 0.40 |
| SumPuz | 3.82 | 0.80 | 0.46 |
| Taut | 0.57 | 0.16 | 0.46 |
| While | 0.36 | 0.08 | 0.49 |

The paper puts the Reduceron at 4–5 times slower than GHC on the PC and
at 6.4 times fewer cycles than its 2007 design.

### The ports

Each port keeps the original's algorithm, inputs and evaluation order.
SKIjack has no integers and no polymorphic data, so four things change:

- integers become Scott numerals (PermSort's 1–10, Taut's counts,
  Clausify's symbols, all 0) and Taut's variable names become five-bit
  codes;
- each list type is declared once per element type, with its own `map`
  and `append`;
- a type may have one binary self-referential constructor, so Taut's
  `And` and `Implies` and Clausify's `Con` and `Dis` hold a pair;
- every `main` checks its answer and returns a boolean: OrdList's and
  Taut's are the original's; Queens2 checks 2,680 solutions, PermSort the
  list 1..10, Clausify the one clause `([0], [])` that
  `clausify_ref.py`, a transliteration of the original, computes.

Every run returns True. Changing each expected answer (93 queens for 92 on
eight, a non-tautology, `([], [0])`, the list 0..10) makes it return False.
PermSort is the port that differs most: its `<=` walks two numerals, up to
ten steps where the Reduceron takes one.

### Results

Avon at `0c7682b`; user CPU, best of five, interleaved; load average 3.3
to 4.7.

| program | SKI steps | SKI, s | template steps | instantiations | templates, s | Reduceron, s | templates ÷ Reduceron |
|---|---:|---:|---:|---:|---:|---:|---:|
| OrdList | 1,030,065,841 | 23.12 | 111,124,752 | 92,915,213 | 2.74 | 0.98 | 2.8 |
| Queens2 | 979,383,271 | 10.49 | 103,498,308 | 92,891,133 | 2.54 | 1.29 | 2.0 |
| Taut | 1,047,965,671 | 21.91 | 85,212,816 | 68,331,304 | 2.01 | 0.57 | 3.5 |
| Clausify | 943,064,451 | 10.37 | 100,493,557 | 88,121,044 | 2.70 | 0.73 | 3.7 |
| PermSort | 2,741,630,882 | 29.94 | 307,482,207 | 244,002,158 | 7.76 | 1.62 | 4.8 |

- **Time.** With templates Avon takes 2.0 to 4.8 times the Reduceron's
  time, 3.2 by geometric mean; as SKI, 18 times. Against the paper's GHC
  it takes 4.5 to 15 times, 9.1 by geometric mean, on a machine a decade
  newer than GHC's.
- **Work.** Counting the Reduceron's hand-reductions as rate × time × 96
  MHz (40.5 million for OrdList, 49.5 Queens2, 25.2 Taut, 37.8 Clausify,
  66.9 PermSort), Avon instantiates 1.9 to 2.7 templates per
  hand-reduction, and PermSort 3.6. A template instantiation counts what a
  hand-reduction excludes: a constructor applied to its case's
  alternatives is one. SKI takes 20 to 42 contractions per hand-reduction.
- **Rate.** Avon spends 24 to 27 ns per step with templates. The
  Reduceron spends 19 to 26 ns per hand-reduction on these five: a
  10.4 ns cycle at 0.40 to 0.54 per cycle. As SKI Avon steps 91 to 93 million contractions a second on
  Queens2, Clausify and PermSort and 45 to 48 million on OrdList and Taut;
  why those two run at half the rate was not investigated.
- Templates cut steps 8.9 to 12.3 times and time 3.8 to 10.9 times.

**Reproduce** at `1e2f24f`, where the ports are as above:

```sh
python3 tests/workloads/reduceron/run.py --avon build/avon --skijack ~/skijack
```

It prints each port's steps, instantiations and best user time, and fails
if an answer is not True.

### With data jets

Data jets (§6.10) run on the same ports with one change to three of them:
`eqNat`, `leNat`, `add` and `mul` in Clausify, PermSort and Queens2 now
call the prelude's numeral operations (`eqNat m n = natIfEq m n True
False`), as the originals call integer primitives. That changes their SKI:
the prelude's operations are `Y`-tied, and cost more as pure SKI than the
hand-written recursions did. The table above keeps the ports as they were
at `0c7682b`; this one is avon `f414272`, skijack
`8b34529`, every mode run beside the others, user CPU,
best of five, load average about 2.5.

| program | SKI, s | templates: steps | s | data: steps | instantiations | dispatches (fused) | numeral operations | s | Reduceron, s | data ÷ Reduceron |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| OrdList | 22.32 | 111,124,752 | 2.76 | 86,769,589 | 37,791,738 | 30,768,312 (24,355,163) | 0 | 2.49 | 0.98 | 2.5 |
| Queens2 | 10.30 | 103,498,309 | 2.61 | 79,407,036 | 34,024,582 | 34,778,139 (24,089,377) | 4 | 2.31 | 1.29 | 1.8 |
| Taut | 21.41 | 85,212,816 | 2.05 | 69,679,137 | 25,590,624 | 27,207,001 (15,533,679) | 0 | 1.86 | 0.57 | 3.3 |
| Clausify | 12.00 | 104,257,799 | 2.88 | 68,204,552 | 25,887,702 | 33,708,614 (28,524,686) | 3,764,243 | 2.43 | 0.73 | 3.3 |
| PermSort | 43.28 | 313,717,527 | 9.20 | 132,810,527 | 52,797,028 | 42,114,724 (39,508,198) | 6,235,320 | 4.34 | 1.62 | 2.7 |

- **Time.** Data jets take 1.10 to 1.19 times less time than templates on
  OrdList, Queens2, Taut and Clausify, and 2.12 times less on PermSort,
  whose comparisons of list elements run on words; 1.28 by geometric
  mean. Clausify's 3.8 million numeral operations gain little: its
  symbols are all 0, and comparing 0 with 0 was a step or two as a term,
  where PermSort's elements run to 10. Against the Reduceron, 1.8 to 3.3 times its time, 2.7 by
  geometric mean, where templates on these ports take 3.4.
- **Where the gain comes from.** Fusion takes a `case` from three steps
  to two -- the function, then constructor and branch in one -- but a
  fused step still builds the branch's instance, so time falls by about a
  tenth, as the estimate from the sampling profile below had it. The numeral operations fire only on
  operands already words: 6.2 million times in PermSort, 3.8 million in
  Clausify, 4 times in Queens2, whose counts are built lazily.
- **Counts.** A dispatch and a numeral operation are one step each, and
  appear in their own columns; the steps column is contractions plus
  instantiations plus these.

**Before building: where a templated step's time goes.** A sampling
profile (`sample`, 1 s, Queens2 with templates at `0c7682b`): `whnf_share`
47% of samples, `av_app` 23%, `tmpl_instance` 21%, `try_interp` 5%, the
collector 3%. No constructor template missed its continuations on any of
the five ports, which is why the plan's constructor-value nodes were
dropped (§6.10).

**Reproduce.**

```sh
python3 tests/workloads/reduceron/run.py --avon build/avon --skijack ~/skijack
```

It runs each port as SKI, with templates and with data jets, prints every
count and the best user time, and fails if an answer is not True.

### Other machines

- **NORMA** (Scheevel, 1986), a Turner-combinator machine, did about
  250,000 reductions a second at 5 MHz, 0.125 per cycle (the Reduceron
  paper, §6.10). Avon's SKI mode does 45 to 93 million.
- **Heron** (Ramsay and Stewart, IFL 2023) reimplements the Reduceron on
  an Alveo U280 at 193 MHz. Its per-benchmark results are plots, not
  tables. It reports its runtime at 48% of the Reduceron's, 1.88% of
  the device against the Reduceron's 90%, and GHC 8.6.5 on an i7-1250U
  doing 22% of its hand-reductions per cycle, on an i3-4030U 15%. It beats
  GHC on the i3 on 5 of 16 benchmarks; desktop and server CPUs beat it by
  about 2.5 times. At 48%, Avon's templates would trail Heron by about 6.7
  times on these five; this is an estimate, not a measurement.
- **SKIM** (Clarke, Gladstone, MacLean and Norman, LISP 1980): its
  figures were not obtained. The paper is a scanned PDF behind the ACM
  library.

### What the comparison does not say

- The ports are not the originals. Scott numerals and pair constructors
  add work the Reduceron's integers and wide constructors avoid; PermSort
  pays most.
- The Reduceron's times include its garbage collector (0.9% to 4.4% of
  them on these five) and ran on 2012 hardware; Avon's include loading
  and checking templates.
- Eleven benchmarks are not ported. Fib, Queens, Braun and the rest do
  integer arithmetic (Braun compares the numbers 0 to 255 six thousand
  times over), which Scott numerals would turn into a different benchmark.

## Data jets on the corpus

Avon `f414272`, the corpus export used for "Templates on
the corpus": the 43 halting conformance runs, `share` mode, to weak head
normal form, fuel ten times the manifest's. With templates they take
43,348 steps; with data jets 33,244, of them 13,627 dispatches, 10,104
fused. Every weak head normal form is templates', and every normal form
is SKI's.

## Earlier measurements

Recorded in `docs/DESIGN.md` with their dates:

- residual jets on T2 in `copy` mode: 2.03 ms without, 1.41 ms with, the
  same 504,930 contractions (§6.5);
- the interpreter jet on T2: 504,930 contractions to 342 (§7);
- the census of both corpora: 1,730,432 and 928,398 contractions (§6.7);
- the compiler core: 87 abstractions of its own compilation in 12,214,849
  contractions, the corpus's 8,636 in 523,815,334 (§20.3);
- the persistent arena: a 32 MB kernel reopens in 0.3 ms, against 160 ms
  from a snapshot (§19.1).
