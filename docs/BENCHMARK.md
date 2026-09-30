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
- Every row's output is the same set of terms, checked by hash against
  Python's; rows 4 and 5 also agree with each other byte for byte.

**Reproduce.** At the listed commits, from skijack's `python/`:

```sh
PYTHONPATH=. python3 -m skijack.selfhost.run0 --avon ~/avon/build/avon            # rows 1-4
PYTHONPATH=. python3 -m skijack.selfhost.run0 --avon ~/avon/build/avon --templates  # row 5
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
