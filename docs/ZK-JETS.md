# Jets under hiding

> **Status (2026-09-30).** Being built: milestones 1–8 of §9 are done.
> The circuit exists as data in Lean and in Rust, the two agree constraint
> for constraint, its honest proofs verify under hiding, and its soundness
> (`compJExport_sound`), completeness (`compJ_complete_log`) and zero
> knowledge (`compJ_transcript`) are proved. Avon writes the witness
> tables, byte for byte ski-air's (milestone 8). The release (milestone
> 9) remains. It joins two circuits that lean-ski has proved separately, the
> composed statement in zero knowledge and the supercombinator jet
> circuit, into one circuit whose proofs hide the witness and instantiate
> licensed templates. Each claim below about
> what exists names its file; each claim about what will exist is marked
> as a design decision or an obligation. Where this note and lean-ski's
> sources differ, the sources are authoritative. `DESIGN.md` §17.3 and §18
> point here.

## 1. Why

**Hidden computation costs every contraction as a row.** lean-ski proves
statements in zero knowledge only without jets, so a verifier runs as
plain SKI reduction:

| statement (lean-ski `release/skilark`) | rows | memory cells | heights | prove |
|---|---:|---:|---|---:|
| `split8`: 16 literal bits, `a + b = 200` | 129,965 | 215,400 | `2^17`, `2^18` | 13 s |
| `csplit8`: 24 bits, plus a knapsack commitment | 471,888 | 672,985 | `2^19`, `2^20` | 42 s |

A zero-knowledge proof pays for its fixed heights on every run, and the
heights are capped at `2^20`. The commitment step (lean-ski `PLAN.md`)
stopped at toy parameters for this reason: a native SKIjack full adder
costs 450 to 640 host contractions a bit, and the largest circuit affords
about 800 of them.

**Jets cut the rows, and the verifier's code is where they apply.** In
the clear, supercombinator jets (`DESIGN.md` §18.1) bring the compiled
corpus rows to 28–34% of the plain run's. A SKIlark verifier is compiled
SKIjack, the same kind of code: its hot functions (`seq`, `applyU`,
`wIfz`, the Scott constructors) are equations and constructors, each a
template the jet table licenses.

**Measured (milestone 1, 2026-09-29), in the clear.** `split8`'s verifier,
applied to its public `x` and the bits, runs in **11,483 rows jetted
against 129,957 plain: 8.8%**, and 74,116 memory cells against 215,393
(lean-ski `bench/plonky3/README.md`). The table comes from the SKIjack
source's own templates: 178 templates, 130 jets, 21,049 licensed roots.
Lean accepts the jetted table (`jets check-src`, `Air.checkJA_sound`).
Dropping the 104 roots that reach the bits, as §4's closure rule does,
leaves 11,571 rows. The padded CPU falls from `2^17` to `2^14` rows, with
POP and INSTW at `2^14` each.

**Measured on the composed heap (milestone 3, 2026-09-30).** Over the
statement's blank heap with the closure rule, run over the filled heap
(`lake exe skilark cjets-measure`), `split8` takes 11,598 CPU rows
against 129,964 plain, 8.9%, and `csplit8` 157,680 against 471,887,
33.4%. Both halt at `K` over the nil, and `checkJA` accepts both from the
filled machine.

**The goal.** A proof, in zero knowledge, that a public verifier accepts
hidden literal bits (lean-ski's predicate statement, `Ski/Predicate.lean`)
or a hidden term (a formula's atom), in which the verifier's run
instantiates licensed templates at public roots. Probes and data jets
under hiding come later (§8).

**Not the goal.** Jetting hidden code. A root is an address in the public
heap (`DESIGN.md` §18.1); the hidden region's cells are not roots, and a
hidden term runs unjetted.

## 2. The two circuits

**The composed circuit** (lean-ski `Ski/Circuit/CompAir.lean`,
`bench/plonky3/src/composed.rs`) hides the witness. Its five tables:

- CPU, with a restart kind for segments and two blinding messages;
- memory, with one blinding message;
- program, preprocessed from the blank heap;
- witness, fixed at `2^8` rows, whose bit mode constrains each bit cell
  to `K` or `K I` and whose region cells are well formed;
- segments, whose multiplicities are fixed by the statement
  (`segs_honest`).

Its heights are the statement's (`log R M`, each in `[8, 20]`). It is
proved:
- sound, `compExportG_sound`, and complete, `comp_completeG_log`, for
  any evaluation statement;
- zero knowledge, `transcript_zk` (`Ski/ZK/TranscriptN.lean`): a simulator
  fixed by the statement matches the real transcript on every event
  within `P^2/P^4 + M/P^4 + ε/NR` of the draws, over a PCS assumed
  statistically hiding.

**The jet circuit** (`Ski/Circuit/JetAir.lean`, `bench/plonky3/src/jets.rs`)
instantiates templates. Its eight tables:

- CPU, with the `INST` kind;
- memory and program;
- ROOTS, HDR and TMPL, preprocessed from the public jet table, each with
  a prover-written multiplicity column;
- POP, one row per popped argument;
- INSTW, one row per written cell.

POP and INSTW are keyed by `clk` through the `popch` and `wch` chains, and
the `arg` bus joins them. It is sound, `jetExport_sound` (an accepted
proof is a run of `AcceptsJ`), and complete, `jet_complete` (heights up to
`2^21`). It hides nothing.

## 3. What the jet circuit reveals today

Measured against its source (`jets.rs`, `main.rs`):

1. **Nothing is hidden.** It proves with the plain PCS (`make_config`), not
   `HidingFriPcs`, and loads the whole term in the program table.
2. **The prover chooses the heights of CPU, memory, POP and INSTW.** Each is
   the next power of two above the run's size; the verifier pins only the
   preprocessed tables and bounds the rest by `2^21` (`verify_j`). So the
   heights give away the run's length, the cells written, `Σ k_g` and
   `Σ n_g` over the firings, to within a power of two.
3. **The provider multiplicities are a histogram of the run.** ROOTS, HDR
   and TMPL have public rows and prover-written counts (`counts`): how often
   each root, each jet and each template cell was used.
4. **Every table's LogUp terminal is published unblinded.** No table carries
   a blinding message (`blind: false` in `airs`).

The composed circuit already answers (1), (2) for CPU and memory, and (4)
for three tables. The design extends those answers to the five jet tables.

## 4. The circuit: composed with jets

*Design decision.* One circuit, `compJ`, with ten tables:

| table | rows | public | private |
|---|---|---|---|
| CPU | `2^R` | the AIR | every column; restart and `INST` kinds, blinding |
| memory | `2^M` | | every column |
| program | from the blank heap | rows, multiplicity | |
| witness | `2^8` | rows (addresses, bit mode) | cells, blinding |
| segments | from the roots | rows; multiplicities (`segs_honest`) | |
| ROOTS, HDR, TMPL | from the jet table | rows | multiplicities, blinding |
| POP | `2^Lp` | | every column |
| INSTW | `2^Li` | | every column |

**The CPU** carries both extensions: the composed CPU's restart kind, `RS`,
`CNT` and `ROOT` columns and blinding blocks (`CompAir.lean`), and the jet
CPU's `INST` kind and `clk` and jet columns (`JetAir.lean`). The two add
disjoint columns and disjoint interactions (`segs` against `roots`, `hdr`,
`popch`, `wch`, `arg`). The kind numbering does collide: the composed kind
function numbers a restart 11 (`kindCf`, `CompTable.lean`), and 11 is
`INST`'s selector (`SEL + 11`). *Obligation:* `kind_ofCJ`, the kind
analysis of the union, with the restart renumbered.

*Built (milestone 4):* the CPU is 149 columns. The corpus CPU's 121, the
jet columns at 121–130 (`JetAir.lean`'s indices, so the jet soundness
proofs read the same columns), the three blinding blocks `a`, `b`, `c` at
131–145, and the restart columns `RS`, `CNT`, `ROOT` at 146–148. The
restart selector is its own column outside the fourteen kinds, so in the
data `INST` and the restart are distinct; the collision is only in the
kind numbering of the proofs, where the restart can be numbered 14, its
place in the one-hot sum (`Ski/Circuit/CompJAir.lean`, `cpuAirCJ`).

**The statement** is lean-ski's `CStmt` (a formula or a predicate), the
region size, the heights, and the jet table:

- `log R M Lp Li`: CPU, memory, POP and INSTW heights, each in `[8, 20]`.
  POP and INSTW heights are public budgets, like the others (`DESIGN.md`
  §17.2): chosen before the run, never from it.
- The jet table, in the file format `jets emit` writes and `jets
  statement` checks: roots, jets and template cells. The verifier's Lean
  check recomputes it from the verifier's source and the blank heap, as
  `lake exe jets statement` does for a corpus term.

**Roots and globals read only public cells.** *Design decision.* The jet
check reads whole terms: `RootsOK` (lean-ski `Ski/AirJet.lean`) reads the
term under each root and under every global, and `jetTable`
(`Ski/JetTable.lean`) points each global at `firstAt`, the first heap cell
whose term matches. In the composed heap that is not safe by address
alone:

- the blank region is `S` cells, so the first `S` in the blank heap is the
  first region cell. In `split8` that is address 19, the hidden witness
  itself, and an `S` global would land on it;
- the bits' encoding (`pairO`, `Ski/Composed.lean`) is public cells that
  point at the bit slots: a cell `K ⬝ b₀` reads `K (K I)` in the blank heap,
  so a template's closed subterm `K (K I)` could take it as its global and
  compute `K b₀` once the heap is filled.

In both cases `rootsOKB` passes over the blank heap and `RootsOK` fails
over the filled one, and a prover who chooses the bits or the region
changes what a licensed jet computes. So the rule is on closures, not
addresses: every cell `termAt` visits from a root or from a global lies
outside the private addresses `[3, 3 + N + W)`, and `firstAt` skips any
cell whose closure reaches one. *Obligations:* `publicB`, a decided check
that the closure of every root and every global avoids the private
addresses, with its soundness lemma, run by the verifier's statement check
beside `rootsOKB` (not only by `jets emit`); and `termAt_public`, that the
blank and the filled heap read the same term at such a cell, so that
`rootsOKB` and `publicB` over the blank heap give `RootsOK` over every
filled one. *Built (milestone 3):* `publicB`, `publicB_sound`,
`termAt_public`, `rootsOK_filled`, and the check `jetStmtC`
(`jetStmtC_sound`), in lean-ski's `Ski/JetPublic.lean`. An
instantiation's arguments may still point anywhere, into the bits or the
region included: they are pointers on the stack, private values in
private columns, and `inst_sound_g` substitutes them as arguments.

**Padding.** Each padding row is inert:

- **CPU:** repeat the halted row, as the composed circuit does (`rowP`).
  A halted row is not `INST`, and `clk` counts every row.
- **Memory:** `Nil` cells.
- **POP and INSTW:** all-zero rows. With `act = 0`, `popCons` forces
  `uses = 0` and `instwCons` forces every operand flag to 0, so a zero row
  sends nothing on any bus (`JetAir.lean`, `popCons`, `instwCons`).
- **The provider tables:** copies of the first row with multiplicity 0,
  as today (`pad_copies`), but to at least `2^8` rows rather than `2^4`,
  as the hiding PCS commits no table shorter (`padCopies8`). A copy is a
  genuine row, so a multiplicity on it provides only a genuine tuple.

**Height bound.** `HeightsOK` weighs each table's rows by its
interactions and requires the sum below `P` (`Air.lean`). The jet CPU
weighs 15 a row (`JetComplete.lean`); the union adds the segment lookup
and three blinding messages, 19. POP and INSTW weigh 3 and 6 today and 5
and 8 with two blocks each: with CPU, POP and INSTW at `2^20`, about
`33 · 2^20 ≈ 2^25`. The provider tables are bounded by `2^27` rows each, as
`jet_complete` assumes, and weigh 1 or 2 a row with their blocks; at that
worst case the sum is about `2^29.6`, still below `P ≈ 2^30.9`.

## 5. Hiding the terminals: a blinding tree

**Eight tables have private terminals:** witness, CPU, memory, ROOTS,
HDR, TMPL, POP and INSTW. The program and segment tables have public ones,
the simulator's `tp` (`transcript_zk`). The provider multiplicities cannot
be made public the way the segment table's were, because they are the
run's histogram; they have to be hidden with the rest.

**A spanning tree of blinding messages hides them.** Each edge of the tree
is a bus of its own carrying one uniform 4-tuple: `+u` from one end and
`−u` from the other, written at row 0 with a flag (`Table.setBlind`,
`terminal_setBlind`, lean-ski `Ski/ZK/Terminal.lean`). For a generic
challenge `β`, a tuple's LogUp term is a bijection onto the extension
field (`blindTerm_pre`, `blindPre_term`). Peel the tree at a leaf: its
terminal is its unblinded one plus an independent uniform term, and its
neighbour absorbs the negation. By induction, the eight published
terminals are uniform subject to their sum, which balance fixes at minus
the public terminals. That is `chain_hides` generalized from a path of
three to any tree.

*Design decision, the tree.* Any spanning tree hides the terminals. This
one keeps the composed circuit's edges and hangs the jet tables off the
CPU through POP, so the CPU carries three blocks:

```
WIT —a— CPU —b— MEM
         |
         c
         |
        POP —d— INSTW —e— TMPL —f— HDR —g— ROOTS
```

The CPU gains one block over the composed CPU (three: `a`, `b`, `c`),
five columns. POP, INSTW, TMPL and HDR carry two blocks each; ROOTS,
memory and the witness table one each. Each block is five columns: the
tuple and a flag. A star at the CPU would work mathematically too, but it
puts seven blocks on the widest, tallest table.

**The simulator** draws the seven tuples, and publishes the tree's view
of a public reference vector: zero for seven tables, minus the public
terminals for the eighth. The PCS assumption and the challenge model are
`transcript_zk`'s, unchanged. The error terms are:

- `P^2/P^4` for a non-generic `β`, unchanged;
- `M/P^4` for the aborts, with `M` now counting every table's messages
  (`abort_count` takes any tables);
- `ε/NR` for the PCS.

## 6. Soundness and completeness: what changes

**The meaning of an accepted proof does not change.** The composed
statement asks each term to evaluate to `K` on the bits and the witness
(`EvalRel`). A jetted run proves evaluation only up to weak reduction of
the value, keeping its head and arity (`jet_run_shape`, lean-ski
`Ski/SmallLemma.lean`: `∃ v', Eval t v' ∧ chead v' = chead v`). A segment
that halts at `K` over the empty stack has value `K`, of arity 0, so the
unjetted value has head `K` and arity 0 and is `K`. *Obligation:*
`chead_K`: `chead v' = chead K → Whnf v' → v' = K` (proved, milestone 5,
without the `Whnf` hypothesis).

*Obligations, soundness:*
- `jet_run_shape` is stated for runs from `load t`; the composed machine
  (`cMachine`) loads slot cells, a region, an encoding and several terms.
  Carry `Mach.inst_sound_g` (instantiation over public addresses) to the
  composed machine: `composedJ_sound`, the analogue of `composed_sound`
  with `JSteps`.
- The table-level soundness joins `CompOK` (the composed buses) and
  `JetOK` (the jet buses) over one CPU: `compJExport_sound`, concluding
  `EvalRel (Ps, SameShape shp)` of the memory's bits and witness, as
  `compExportG_sound` does.
- Roots and globals whose closures avoid the private addresses, licensed
  over the blank heap: `rootsOKB` and `publicB` of the statement's jet
  table, and `termAt_public` (§4) to carry them to the filled heap
  (proved, milestone 3: `rootsOK_filled`, `jetStmtC_sound`; the circuit
  feeds `RootsOK` of the filled `m0.heap` to `AcceptsJ.reach`, or cites
  `rootsOK_public`, which needs no bit mode).

*Obligations, completeness:* `compJ_complete_log`. Every run of the
composed machine with instantiations at licensed roots, within
`2^R` rows, `2^M` cells, and `Σ k_g ≤ 2^Lp`, `Σ n_g ≤ 2^Li`, has honest
tables at those heights, the padding rows inert, and the program and
segment tables the public ones (as `comp_completeG_log` returns them). It
carries `jet_complete`'s hypotheses on the jet table too: nonempty, and
each provider table at most `2^27` rows (proved, milestone 6).

*Obligation, the table check:* `checkCJ` and its soundness, the jetted
composed checker. `lake exe composed check` decides `AcceptsC`, which has
no `INST` step, so it refuses a jetted table; the new checker is to the
composed one what `checkJA` is to `checkA`.

*Obligations, zero knowledge:*
- `tree_hides` (proved, milestone 2): the blinding tree's terminals are uniform subject to
  their sum, for a generic `β`. It generalizes `chain_hides`
  (`Ski/ZK/Chain.lean`), whose view is three terminals and whose count is
  over two tuples (`count2`), to a tree of `n` tables and `n − 1` tuples.
  The per-tuple shift lemmas (`shift_term`, `unshift_shift`) carry over.
- `transcript_zkN` (proved, milestone 2): `transcript_zk` over `n`
  terminals, with the `n − 1`-fold count.
- `compJ_transcript`: the instance (proved, milestone 7).

## 7. The prover's side, and Avon's

**ski-air** gains a composed-jets prover (`compJ.rs`). It reads the
statement and the witness, runs the machine with instantiations, derives
the POP and INSTW chains and the provider multiplicities, pads to the
statement's heights, and writes the seven blinding tuples before proving.
It proves under `HidingFriPcs` with the composed prover's configuration.
Its verifier:
- pins every height to the statement's. *Built (milestones 4 and 7):*
  all four free heights come from the statement's `log R M Lp Li`, each in
  `[8, 20]` (lean-ski's `ComposedText.statementOfTextJ`, `lake exe composed
  statement-jets`; `composed budget` writes it from a composed statement).
  A composed statement and one with jets are each refused by the other's
  check. Soundness does not depend on the budgets (Plonky3 bounds the
  LogUp multiplicities by the real heights). Zero knowledge does: the
  verifier fixes the statement, budgets included, and the templates'
  source before the witness, or a prover who chose them would publish the
  sizes of its run;
- runs the Lean statement check, which compares the jet table with the
  one Lean recomputes and checks the roots;
- compares its AIRs with Lean's `compJAirs`.

**Avon** writes the witness table, as it does for jetted runs
(`avon witness --jet-table`, `src/witness.c`): the CPU rows and the
memory, from which ski-air derives the rest (`DESIGN.md` §18.1). Three
changes, *built (milestone 8)* as `avon witness --statement=PUBLIC
--jet-table=JETS WITNESS`:

1. **Public budgets.** Pad to the statement's heights, not to the next
   power of two above the run (`pow2_at_least`, which pads every Avon
   witness table, plain or jetted). Avon already refuses a run over its
   `--rows` budget. This is `DESIGN.md` §17.2's rule.
2. **The composed machine.** Load the statement's blank heap with the
   witness's bits and region filled in, which is lean-ski's `cHeap`. Run
   one segment per term, restarting at each root over the public nil,
   with an instantiation at each licensed root.
3. **No randomness.** Avon's table has no blinding columns. ski-air adds
   them, with the flags clear (lean-ski's `Unblinded`), and draws the
   tuples when it proves.

*Check:* `make zk-jet-witness-check` compares Avon's table with ski-air's
own, byte for byte, as `jet-witness-check` does (`tests/jet_witness_check.sh`),
and runs the jetted composed checker (`checkCJ`, §6) on it. ski-air then
proves Avon's table under hiding (`ski-air compj-prove-table`, which reads
the instantiation rows from the table as `jet-prove` does) and verifies the
proof from the public files alone.

## 8. Later: probes and data jets under hiding

**Probes** bind a public output of a hidden computation.
- The plan is public (PLAN, preprocessed). Honestly each plan row is used
  a fixed number of times, so its multiplicities are the statement's, as
  the segment table's are. *Obligation:* the analogue of `segs_honest`.
- PW's rows follow the public plan, but the addresses it writes depend on
  the counter, so PW is private and joins the tree.

**Data jets** (`DESIGN.md` §18.2) are what a real commitment needs: a word
cell `W n`, and a table per function joined to the CPU by a bus, licensed
by a Lean theorem per jet. The first is a hash precompile, Poseidon2 over
BabyBear with a Lean specification, which closes lean-ski's commitment
step at real parameters. Each data-jet table has private rows and joins
the tree; its height is a public budget like POP's.

## 9. Milestones

1. **Measure.** *Done, 2026-09-29* (§1): 11,483 rows jetted against
   129,957 plain, from the source's own templates (`lake exe skilark
   jets`, `ski-air jets-measure`, `lake exe jets check-src`). §4–§7 pay.
2. **The tree lemma.** *Done, 2026-09-29:* `tree_hides`
   (`Ski/ZK/Tree.lean`) and `transcript_zkN` (`Ski/ZK/TranscriptN.lean`)
   in lean-ski, axiom-clean (`propext`, `Quot.sound`). `transcript_zk` is
   now proved as the tree of three (`chain_viewT`, `tsum_tsumN`), so
   `comp_transcript`, with its statement unchanged, is the three-table
   instance.
3. **Public closures.** *Done, 2026-09-30,* in lean-ski's
   `Ski/JetPublic.lean`, axiom-clean. `jetTable` skips private closures
   for roots and globals alike (`priv`, `pubCells`; `jetTableC` for a
   composed statement). The verifier's check `jetStmtC` holds the
   recomputed table, `rootsOKB` and `publicB`, and `jetStmtC_sound`
   licenses its roots over every filled heap, through `termAt_public`
   and `rootsOK_filled` (`skilark cjets`, `cjets-statement`,
   `cjets-measure`). The hazard is real: without the rule, `split8`'s
   table licenses 47 roots and 3 globals that reach a private cell, and
   fails `rootsOKB` over the honest filled heap.
4. **The circuit as data.** *Done, 2026-09-30.* `compJAirs` in
   lean-ski's `Ski/Circuit/CompJAir.lean` and `bench/plonky3/src/compj.rs`,
   the ten tables of §4 with the tree of §5. `lake exe circuit compare-compJ
   SRC -` checks the statement, the jet table (`Air.jetStmtC`) and the ten
   AIRs, constraint for constraint and preprocessed row for row, on every
   verification. Proved and verified under hiding (`ski-air compj-prove`,
   `compj-verify`): `split8` in 11,599 CPU rows, 8,614 POP and 12,363
   INSTW at heights `2^17 2^18 2^14 2^14`, in 11 s; `csplit8` at
   `2^18 2^19 2^17 2^17`, where without jets it needs `2^19 2^20`, in 26 s
   against 42; and the three-segment `and` and `or`, whose segments restart
   between instantiations. Wrong, clear, non-Boolean and forged witnesses,
   a wrong budget and an unbalanced blinding tree are refused. For
   milestone 5, `compJAirs_composed` (memory, program, witness and segments
   are the composed circuit's) and `withBlocks_cons` (a blinded table keeps
   its own constraints and messages first).
5. **Soundness.** *Done, 2026-09-30,* in lean-ski's `Ski/ComposedJ.lean`
   and `Ski/Circuit/CompJ*.lean`, axiom-clean. `kind_ofCJ` numbers the
   kinds `0`–`10`, `INST` `11` and the restart `12`. `composedJ_sound`
   runs each segment as jetted steps; `chead_K` needs no `Whnf`
   hypothesis (an application has arity at least 1). The jet circuit's
   instantiation argument carries over whole (`CJOK.core : JetCore`, so
   `JetCore.inst`). `compJExport_sound`: for a jet table `jetStmtC`
   accepts and whose numbers fit, an accepted proof's memory holds bits
   and a region whose witness makes every term evaluate to `K`, exactly
   `compExportG_sound`'s conclusion; `predJExport_sound` for a predicate.
   The checker `checkCJ` (`checkCJ_sound`, `lake exe composed check-cj`)
   accepts the honest tables of `split8`, `and` and `or` and rejects
   tampered ones.
6. **Completeness.** *Done, 2026-09-30,* in lean-ski's
   `Ski/Circuit/CompJComplete.lean`, axiom-clean. The honest tables of a
   jetted run (`CRun`) are the jet circuit's CPU columns, with the restart
   rows' selectors cleared and the segment counter and next root added.
   The CPU satisfies its AIR (`cpuCJ_sat`) and sends as the jet circuit's
   CPU off the memory, segment and blinding buses (`cpuCJ_jetSends`).
   Every blinded table's flags are clear, so it sends as its base
   (`sends_withBlocks_quiet`), and the ten tables balance bus by bus on
   the jet circuit's lemmas (`balancedCJ`). `compJ_complete_log`: a run
   within `2^R` rows, `2^Lm` cells and `2^Lp`, `2^Li` POP and INSTW rows,
   all at most `2^20`, with roots licensed over the filled heap, gives
   tables `compJAirs` accepts at those heights, with the public program
   and segment tables, decoding back to the memory and the run;
   `compJStmt_complete_log` takes `jetStmtC` in place of the license.
7. **Zero knowledge.** *Done, 2026-09-30,* in lean-ski's
   `Ski/ZK/CompJ.lean`, axiom-clean. `compJ_transcript` is
   `transcript_zkN` for the tree of eight private tables and seven tuples
   that `compj.rs` blinds (`jetPar`, `jetBus`, `jetSg`). Each blinded
   table's terminal is computed (`terminal_wb2`, `terminal_cpuCJ`), the
   published terminals are the tree's view of the unblinded ones
   (`compJ_chain`), and those sum to minus the public program and segment
   tables' (`compJ_sum`). `CRun.honest_zk`: milestone 6's honest tables
   meet the hypotheses. The statement carries POP's and INSTW's budgets
   (`log R M Lp Li`), and `compj-prove`, `-verify` and `-tamper` read them
   from it. The model is honest-verifier zero knowledge over uniform
   challenges, with the simulator fixed by the statement; Fiat–Shamir is
   the random-oracle step, and `PCSCloseN` carries the committed traces'
   hiding.
8. **Avon.** *Done, 2026-09-30.* `avon witness --statement=PUBLIC
   --jet-table=JETS WITNESS` (`av_cstmt_read`, `av_witness_run_composed`,
   `av_composed_table`): the statement's heap with the witness's bits and
   region, one jetted segment per root over the public nil, each to `K`
   over the nil, padded to the statement's heights; a run over any of the
   four budgets is refused. `make zk-jet-witness-check` on lean-ski's
   `and`, `or` and `split8`, with `split8`'s templates: each table
   byte-identical to ski-air's, accepted by `check-cj`, proved under
   hiding by `ski-air compj-prove-table` and verified alone. The wrong,
   clear and non-Boolean witnesses are refused by both, the forged
   region's table is rejected by `check-cj` and does not prove, and a POP
   budget below the run's is refused by both. `split8`: 11,599 rows,
   2,250 instantiations, 8,614 pops, 12,363 written cells.
9. **Release.** `split8` and `csplit8` proved with jets under hiding, in
   lean-ski's `release/skilark`, checked by `release/verify.sh`.

## 10. Risks

- **The saving was the risk, and it is measured:** 8.8% of the rows on
  `split8`, far below the compiled corpus's 28–34%, since the kernel's
  small equations fire thousands of times. Other predicates will differ;
  the measurement is one statement.
- **Eight blinded tables take seven tuples,** five more than the composed
  circuit's two, and ten more blocks, 50 columns. They are small beside
  POP and INSTW themselves.
- **The CPU union is wide:** 149 columns, the jet CPU's 131 with three
  blinding blocks and the restart columns. Width costs commitment time,
  not rows.
- **The composed facts move.** The restart columns sit at 146–148, not the
  composed CPU's 131–133, so the composed CPU's row lemmas (`CompRow`,
  `CompKind`) must be restated for the union, or generalized over the
  restart's base column, in milestone 5. The jet columns keep their
  indices, so `JetCore` applies as it is.
- **The closure rule narrows the jets.** A template whose closed subterm
  occurs only in cells that reach private addresses gets no global, and a
  root whose term reaches them is not licensed. On `split8` in the clear
  it drops 104 of 21,049 roots and no global, and the run grows from
  11,483 rows to 11,571. On the composed heap it drops 47 of 21,043 roots
  on `split8` (11,489 CPU rows in the clear to 11,598) and 71 of 57,245
  on `csplit8` (157,513 to 157,680).
- **The jet table grows the statement.** Its check is Lean's recomputation,
  as for the corpus, from the SKIjack source's templates
  (`JetTable.fileTemplates`, as `jets check-src` uses them).
- **Probes and data jets are not in this design's circuit.** A hidden
  computation with a public output, or a real commitment, waits for §8.
