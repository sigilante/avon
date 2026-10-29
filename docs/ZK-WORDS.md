# Word cells under proof

This note designs the witness rows that would let Avon's numeral operations
run inside a lean-ski proof, as `ZK-JETS.md` designed them for templates.
Nothing here is built. Each claim about what exists names its file; each
claim about what will exist is marked as a design decision or an
obligation. Where this note and lean-ski's sources differ, the sources are
authoritative. Figures are from 2026-10-29, Avon `6751ee0`, lean-ski's
split sources as committed at `fb65141`.

## 1. What word cells would buy, measured

**On the two shipped statements, nothing: no numeral operation fires.**
`tests/zkwords/measure.py` builds the term each verifier runs on an honest
witness, encoded as lean-ski's `bench/Skilark.lean` encodes it, and runs it
in share mode. Its output, as contractions:

| statement | plain | templates | templates + words | operations fired |
|---|---:|---:|---:|---:|
| split8 | 33,079 | 1,575 | 1,232 | 0 |
| csplit8, weights below 64 (shipped) | 97,759 | 4,903 | 4,081 | 1 |
| csplit8, weights below 512 | 266,444 | 35,884 | 34,012 | 1 |
| csplit8, weights below 4,096 | 991,666 | 170,942 | 160,292 | 1 |

The 17–22% that `--data` saves on the shipped statements is constructor
dispatch and fusion, which a witness does not have; it is not word
arithmetic.

**split8 has no arithmetic to speed up.** Its public `x` and its witness
are bits, so every numeral it builds is 0 or 1.

**csplit8 does, and the operations still decline.** Its knapsack sums
public weights, and a run's length grows with their size: 4,903
contractions with weights below 64, 170,942 below 4,096. At 4,096 the
plain run's profile (`--profile`) charges 18.6% to `eqN`, 15.6% to `add`
and 14.0% to `Suc` and the quotation constructors. Yet one operation
fires, for two reasons:

- **The sum is a chain of pending additions.** `wAdd` pushes
  `Num (add m n)` unevaluated, so the next `add` meets an operand that is
  an application, not a word, and Avon fires an operation only when both
  operands are words already (`DESIGN.md` §6.10). The final comparison
  forces the chain, and each `add` runs its term, one successor at a time.
- **The comparison is not a pinned operation.** csplit8's `eqN` returns a
  Boolean; skijack's `natIfEq` selects one of two arguments, and only
  `natIfEq` is pinned and proved (`lean/Words.lean`, `ifeq_spec`). The
  `add` and `mul` that SKIlark's sources define are skijack's terms node
  for node (both hash to the pinned `0af93ffd…` and `15d2f6f4…`).

**So word cells pay only with two more pieces.** One evaluates pending
arithmetic over words (§4, `VAL`). The other is SKIlark compiling its
comparison to `natIfEq`. With both, csplit8's arithmetic would be one row
per operation whatever the weights' size; that is a prediction, which
milestone 2 tests. Without them, the jetted run grows linearly with the
weights: about 41 contractions per unit of the bound between 64 and 4,096,
so weights of `2^16` would need some 2.7 million, past the `2^20` height
cap. That last figure is extrapolated, not run.

**A private word is the second payoff.** Today a hidden number is `k` bit
cells, constrained `K` or `K I`, and the verifier spends rows decoding
them. A word witness cell would hold up to 27 bits in one cell, checked by
a range table.

## 2. The word cell

*Design decision.* A memory cell `W n` with a new tag, its payload `n` in
the cell's first field (memory cells are `addr tag a b`,
`Ski/Circuit/Base.lean`).

- **Meaning.** `⟦W n⟧ = encNat n`, the Scott numeral `SUC (… (SUC K))`
  with skijack's `SUC = S (K K) (S (K (S I)) K)`, as Avon's share-mode word
  is (`DESIGN.md` §6.10). Every reader of the heap (`termAt`) sees through
  a word cell to its numeral.
- **Range.** `1 ≤ n < 2^27`. Zero stays `K`, as in Avon, so a word cell
  is never zero and the dispatch on zero is the existing `K` rule. `2^27`
  is Avon's `AV_WORD_MAX`; with BabyBear's `P = 2^31 − 2^27 + 1`, any sum
  of two words lies below `2^28 < P`, so additions do not wrap.
- **Range check.** Three 9-bit limbs, each looked up in a preprocessed
  `RANGE` table of `2^9` rows. That is the minimum height the hiding PCS
  commits (`padCopiesMin`), so the table costs nothing in height.
  Non-zero is checked by an inverse column.

**Where words come from.**

1. **Public numerals.** The verifier's statement check builds the blank
   heap with each closed public numeral as a word cell. The check is
   deterministic and recomputed from the source, as `jetStmtC` recomputes
   the jet table, so the public heap stays a function of the statement.
2. **Private words** (milestone 6). The witness table gains a word mode
   beside its bit mode: a cell `W n` or `K`, range-checked.
3. **Results** of the operations (§4).
4. **`SUC` of a word.** A row `WSUC` applies the public `SUC` to a word
   cell or `K` and writes `W (n+1)`. Its licence is the meaning itself.

## 3. Dispatch: the `WCASE` row

A word cell at the head with its two continuations, `W n z s`, reduces to
`s ⟦W (n−1)⟧`. *Design decision:* one CPU kind, `WCASE`.

- It pops `z` and `s`, writes `W (n−1)` (or `K` when `n = 1`), and writes
  `App(s, ·)` as the new head.
- It is two cells and one row, where the plain run spends a head `S`
  chain over `SUC`'s term.

*Obligation:* `wcase_sound`, that `⟦W n⟧ ⬝ z ⬝ s` weakly reduces to
`s ⬝ ⟦W (n−1)⟧`. This is `SUC`'s reduction, three steps.

## 4. Operations: `WOP`, the `VAL` bus, and the arithmetic table

**The operations are public roots.** *Design decision.* A preprocessed
table `WOPS` lists, per operation, the heap address of its term.
- **The check.** The verifier's statement check confirms that the term at
  each address is the pinned term: node for node, as Avon's `words.c` pins
  them and as `src/word_pins.h` prints them from `lean/Words.lean`. It also
  confirms that the term's closure avoids the private addresses, by
  `ZK-JETS.md` §4's rule (`publicB`).
- **The operations.** Seven, the numeral operations `lean/Words.lean`
  proves: `add`, `sub` (truncated), `mul`, `div` and `rem` (by zero: 0 and
  `m`), `ifeq` and `ifle`.
- **Later.** The list and bit-string operations need list cells and wait
  for them.

**The `WOP` row.**
- **The read.** The head is a `WOPS` root with its operands on the stack.
  Each operand is a word cell, `K`, or a cell whose value the `VAL` bus
  provides.
- **The bus.** The row sends `(op, a, b, c, g)` on a `wop` bus to the
  `WARITH` table: the operands' values, the result, and a selector.
- **The write.** It writes the result: `W c`, or `K` when `c = 0`. For
  `ifeq` and `ifle` it writes nothing: it continues with the argument `g`
  selects, a pointer, as Avon does.

**The `VAL` bus evaluates pending arithmetic.** *Design decision, required
by §1.* A row of the `VAL` table asserts that the cell at address `x`
means the numeral `v`.

- **A word cell's value** is its payload, and `K`'s is 0.
- **A pending operation's value.** For a cell `App(App(r, y), z)` with `r`
  a `WOPS` root, the value is the operation on `VAL(y)` and `VAL(z)`,
  checked through `WARITH`. The row requires `y < x` and `z < x` by range
  checks, so the values are well founded although `termAt` alone does not
  forbid cycles.
- **Memoized.** LogUp multiplicities let any number of consumers look up
  one value. This gives what share mode's update in place gives, in a
  memory that is written once.

Evaluating an operand first is still weak reduction: `WStep` has the
right congruence (`Ski/Weak.lean`). It cannot change termination either,
because each operation is total on numerals. *Obligation:* `val_sound`,
that a `VAL` row's cell weakly reduces to `encNat v`, by induction on the
address, from `add_spec` … `rem_spec`.

Avon's share mode gets the same rule (milestone 1): an operation fires
when each operand is a word, or a pending operation over such operands,
evaluated first and updated in place.

**The `WARITH` table** checks each operation over the integers, with no
reduction mod `P`.

| op | constraint | range checks |
|---|---|---|
| `add` | `c = a + b` | `c < 2^27` |
| `sub` | `g = [a ≥ b]`; `c = g·(a − b)` | `g·(a − b)` and `(1−g)·(b − a − 1)` below `2^27` |
| `mul` | 9-bit limbs: `s₀ = a₀b₀`, `s₁ = a₀b₁ + a₁b₀`, `s₂ = a₀b₂ + a₁b₁ + a₂b₀`, `a₁b₂ + a₂b₁ = 0`, `a₂b₂ = 0`; `c = s₀ + 2^9 s₁ + 2^18 s₂` | `s₂ < 2^9`, `c < 2^27` |
| `div`, `rem` | `b = 0`: `q = 0`, `r = a`; else `a = q·b + r` (the `mul` gadget for `q·b`) | `b − r − 1 < 2^27` when `b ≠ 0` |
| `ifeq` | `g = [a = b]` by an inverse of `a − b` | |
| `ifle` | `g = [a ≤ b]` | `g·(b − a)` and `(1−g)·(a − b − 1)` below `2^27` |

The table has no wrap-around:
- each partial product of two 9-bit limbs is below `2^18`;
- each of `s₀`, `s₁` and `s₂` is below `3·2^18`;
- with `s₂ < 2^9`, the sum for `c` is below `2^30 < P`;
- a field zero of products this small is an integer zero.

A product above `2^27 − 1` has no row, so the prover runs the term
instead, as Avon declines it today. *Obligations:* `warith_sound` per row
(the integer relation from the field equations) and `range_sound` for the
limbs.

## 5. Soundness: what changes

lean-ski's soundness theorems read an accepted proof as a run of the
machine over `termAt` (`compJExport_sound`). With words that reading
becomes `termAt` composed with `⟦·⟧`, and each new row must be a weak
reduction of what it reads.

- **The licences.** `lean/Words.lean` proves them over lean-ski's
  `Term`, `add_spec` … `rem_spec`, `ifeq_spec` and `ifle_spec`, and they
  move to lean-ski as they are. lean-ski already has a `Ski/Words.lean`
  (Joy's words), so the module needs another name, for example
  `Ski/WordCell.lean`.
- *Obligations:*
  - `termAtW` and `termAtW_blank`: the meaning of a heap with word cells,
    and that the blank heap's word cells are its closed numerals;
  - `wcase_sound`, `wsuc_sound`, `wop_sound` and `val_sound`;
  - `kind_ofCJW`: the kind analysis of the CPU with `WCASE`, `WSUC` and
    `WOP`;
  - a completeness theorem for honest runs, as `compJ_complete_log` is
    for the jet circuit.
- **What stays trusted.** Avon's share-mode glue around a fire stays
  trusted, as a Vere jet's is. Under proof nothing is trusted but the
  AIR: a word row is accepted only through `WARITH` and the range table.

## 6. Hiding

The new private tables, `WARITH`, `VAL` and the range table's
multiplicities, carry blinding blocks and join the blinding tree
(`ZK-JETS.md` §5). Their heights are public budgets fixed before the run,
like POP's. `WOPS` is preprocessed and public, like ROOTS.

*Obligation:* the zero-knowledge theorem for the extended circuit,
`compJ_transcript`'s analogue over the larger tree (`transcript_zkN`,
`tree_hides`). It is honest-verifier until lean-ski carries the jet
circuit through Fiat–Shamir, which is separate work.

## 7. Avon's side

- **Share mode** (milestone 1): fire on pending operations over words
  (§4). This changes counts in `tests/` where an operand was pending, so
  every changed count is re-pinned with a note of why.
- **The witness** (milestone 4): `avon witness --statement` writes the
  word cells and the `WCASE`, `WSUC`, `WOP` and `VAL` rows, byte for byte
  ski-air's, as it does today for the jet tables
  (`tests/zk_jet_witness_check.sh`).
- **Word pins.** `src/word_pins.h` is printed from `lean/Words.lean` and
  stays the source of the terms both sides match.

## 8. Milestones

1. **Measure.** *Done, 2026-10-29* (§1, `tests/zkwords/measure.py`).
2. **Avon: evaluate pending arithmetic in share mode.** Re-run §1. The
   prediction to test: csplit8's run stops growing with the weights.
3. **SKIlark: compile the comparison to `natIfEq`.** That changes
   SKIlark's `skilark.zk` and the statements lean-ski ships, so it is
   SKIlark's and lean-ski's change, coordinated through Avon's pins.
4. **lean-ski, in the clear:**
   - the word cell, `termAtW`, `WCASE`, `WSUC`, `WOP`, `VAL`, `WARITH`
     and the range table;
   - soundness (§5) and completeness;
   - the Rust AIR and its comparison with the Lean data.
5. **Avon writes the witness, byte for byte ski-air's.**
6. **Private word witnesses:** the witness table's word mode, and a
   statement that uses it, for example a range proof over a 24-bit hidden
   value.
7. **Hiding:** blinding blocks, the tree, and the transcript theorem.

## 9. Risks

- **The payoff is per statement.** The shipped split statements gain
  nothing until milestones 2 and 3. Only statements whose values grow,
  such as knapsacks with real weights, counters and range proofs, gain in
  rows.
- **27 bits.** A value at or above `2^27` stays a unary numeral, as in
  Avon. Wider words would need limbs throughout.
- **`VAL` ordering.** Rows read children at lower addresses. A heap
  writer that ever allocates a parent before its children breaks
  completeness, not soundness: the prover could not evaluate that cell.
- **Two counts.** Evaluating pending arithmetic first changes Avon's
  share-mode counts. It never changes a normal form, since every
  operation is total on numerals.
