# Lean proofs for Avon's C jets: a plan

Written 2026-10-29. Steps 1 and 2 are done (§4, §5; 2026-10-29). A jet is native code that stands for a term (`DESIGN.md` §6);
today most of Avon's jets are licensed by testing. This note plans their proofs in
Lean, jet by jet, and records what each proof covers and what stays trusted.

## 1. Three things a proof can cover

Each C jet carries three obligations.

1. **The term computes the function.** A Lean theorem that the jet's pinned term,
   applied to the encodings of its arguments, weakly reduces to the encoding of
   the result. lean-ski states this shape as `Implements` (`Ski/DataJet.lean`), and
   `DESIGN.md` §18.2 lists one as owed per operation.
2. **The C computes the function.** Avon has done this once: `lean/P2Prog.lean`
   proves a program equal to Poseidon2's specification under C's `uint64_t`
   arithmetic and prints `src/p2_prog.h`, which a check compares byte for byte.
   What stays trusted is the printer and C11's unsigned arithmetic.
3. **The reducer's glue.** The code that matches the pinned term, reads operands
   out of word nodes, applies the bounds (`AV_WORD_MAX`, `WORD_BUILD_MAX`) and
   writes the result back. Proving it takes a semantics for `reduce.c`'s graph
   reduction, larger than every jet together. It stays trusted and tested:
   `--jet-check`, `tests/test_data.c`'s parity at every fuel, and the corpus.

**A proof needs only the first.** In the `witness` strategy the verifier checks
the table, so no C in Avon is trusted; a jet there needs its theorem and a
circuit table (§18.2's word cells). The second and third matter for trusting a
`share`-mode run.

**A jet's theorem licenses its value, not its count.** Every jet below skips
contractions (§6.5), so none of these theorems says anything about steps.

## 2. The jets

| jet | the term computes the function | the C computes the function | left |
|---|---|---|---|
| supercombinator templates (`tmpl.c`) | done for all at once: `absN_beta_close`, `inst_sound_g` | trusted | Lean, not C, checks the loaded table (`rootOKB`) |
| Scott constructors (§6.8) | done: they compile through `ctorO` | trusted | as templates |
| Poseidon2 (`--p2`, §6.12) | done: `poseidon2_respects`, P proved in lean-ski | done: `AvonP2.permuteC` | nothing |
| numeral words: `add` `sub` `mul` `ifeq` `ifle` `div` `rem` (§6.10) | done: `add_spec` .. `rem_spec` | done: `fireC_num`, `fireC_arg` | nothing; a witness still needs word cells |
| list words: `len` `at` `app` `take` `drop` | done: `len_spec` .. `drop_spec` | done: `listFireC_sound`; the cell walks are glue | nothing |
| bit strings: `beq` `bget` `ideq` | done: `beq_spec`, `bget_spec`, `ideq_spec` | done: `beq_fire`, `bget_fire`, `ideq_fire`, over a view of `ctor_at` | nothing |
| Y in one step (`--fix`, §6.11) | owed, and not a reduction (below) | trivial | step 4 |
| the interpreter jet (§7) | owed: the tower's adequacy theorem | a copy-mode loop | step 5 |

**Y is not a weak reduction.** Curry's Y does not reduce `Y g` to `g (Y g)`: it
reduces to `X X`, with `X = S (S (K S) K) (K (S I I)) g`, and `X X` reduces to
`g (X X)`. `Y g` and `g (Y g)` are convertible, not one a reduct of the other, so
`--fix`'s rewrite needs the simulation theorem up to lean-ski's `Tr` that §6.11
and §18.4 name as owed, not an `Implements` lemma.

## 3. Order

1. **Numeral words**, by `P2Prog.lean`'s pattern (§4).
2. **List words, then bit strings**, on the same scaffolding (§5).
3. **Templates checked by Lean** at load, with lean-ski's `rootOKB`, replacing
   the check in C.
4. **Y's simulation theorem.**
5. **The interpreter jet's adequacy theorem.**

`reduce.c`'s glue stays trusted unless a verified reducer becomes a goal of its
own.

## 4. Step 1: the numeral words

**Lean owns the pins.** A jet fires only on a term equal, node for node, to its
pinned text (`PINNED` in `src/words.c`). A theorem about a Lean term says nothing
about that text unless the two are the same term, so Lean prints the text.
`lean/Words.lean` defines the seven terms, proves them, and prints
`src/word_pins.h`, which `words.c` includes; a check compares Lean's output with
the committed header byte for byte, as `p2-witness-check` does for
`src/p2_prog.h`. The terms stay skijack's prelude's, which the existing pin
checks hold.

**The theorems.** With `encNat` lean-ski's Scott numeral (`Zero = K`,
`Suc = S (K K) (S (K (S I)) K)`, Avon's `SUC_TEXT`), for every `m`, `n`, `a`, `b`:

| op | statement |
|---|---|
| `add` | `add ⬝ ⌜m⌝ ⬝ ⌜n⌝ ↠ ⌜m + n⌝` |
| `sub` | `sub ⬝ ⌜m⌝ ⬝ ⌜n⌝ ↠ ⌜m - n⌝`, truncated at 0 |
| `mul` | `mul ⬝ ⌜m⌝ ⬝ ⌜n⌝ ↠ ⌜m · n⌝` |
| `div` | `div ⬝ ⌜m⌝ ⬝ ⌜n⌝ ↠ ⌜m / n⌝`, 0 when `n = 0` |
| `rem` | `rem ⬝ ⌜m⌝ ⬝ ⌜n⌝ ↠ ⌜m % n⌝`, `m` when `n = 0` |
| `ifeq` | `ifeq ⬝ ⌜m⌝ ⬝ ⌜n⌝ ⬝ a ⬝ b ↠ (m = n ? a : b)` |
| `ifle` | `ifle ⬝ ⌜m⌝ ⬝ ⌜n⌝ ⬝ a ⬝ b ↠ (m ≤ n ? a : b)` |

`↠` is lean-ski's `WSteps`; Lean's `/` and `%` already give 0 and `m` at zero,
as skijack does. The result is `encNat`, the term a word node stands for, so the
jet's output is itself the reduct.

**The method** is `Ski/BitArith.lean`'s. Each pin is `Ycomb ⬝ G`. One lemma, for
every `G`, unrolls Curry's knot: `Ycomb ⬝ G ↠ R` and `R ↠ G ⬝ R`. Each case of
`G` is then a symbolic run that the kernel checks (`wnf`, `run`), with the knot,
the operands' predecessors and `a`, `b` as variables. Two refinements keep the
runs exact:

- the `Suc` that `G` builds is a variable during the run and closed afterward,
  so the run stops at `Suc ⬝ (R ⬝ m ⬝ p)` rather than reducing the numeral past
  `encNat`;
- an operation that inlines another, as `mul` inlines `add` and `div` inlines
  `ifle` and `sub`, has that pin as a variable too, and its proved theorem
  finishes the step.

Induction on the recursed operand closes the variables; `div` and `rem` take
strong induction on `m`.

**The C.** `word_fire` computes `m + n`, `m · n`, `m / n` and `m % n` in
`uint64_t` from two 28-bit word values and declines any result over
`AV_WORD_MAX`; `sub` walks predecessors, and the comparisons choose an operand.
A Lean model of that arithmetic, over `UInt64` and `UInt32`, is proved to agree
with the specification wherever the C fires, as `sboxC` models `av_p2_sbox`. The
loops that build the result word are glue.

**Done when** `make words-lean-check` elaborates `lean/Words.lean` against
lean-ski's pin, every theorem checked by the kernel, and finds
`src/word_pins.h` byte-identical to Lean's output; `make check` passes with
`words.c` reading the printed header.

**Done, 2026-10-29.** `lean/Words.lean` proves the seven operations' terms
(`add_spec` .. `rem_spec`) and `word_fire`'s arithmetic (`fireC_num`,
`fireC_arg`), each on lean-ski's axioms only (`propext`, `Quot.sound`), and
elaborates in about 2 s. Lean's print equals the pins `words.c` held, byte for
byte, so no term changed. The files it imports are unchanged since lean-ski's
pin. What the proofs found:

- every generator is one plain recursion: `sub` takes the predecessor as
  `m K I`, `mul` calls `add`, and `div` and `rem` case `n` and call `ifle`
  and `sub`;
- Curry's Y unrolls through the knot `X X`, `X = S (S (K S) K) (K (S I I)) G`,
  by one lemma for every operation (`knot_unroll`);
- the C needs no wrap argument past the operands' 32 bits: `m · n` of two
  `uint32_t` values fits `uint64_t`.

What stays trusted: that `fireC` reads as `word_fire` does, the printer, and
the glue of §1.

## 5. Step 2: lists and bit strings

**Done, 2026-10-29.** `lean/Words.lean` grows from the numerals to all fifteen word
operations, by the same method, and prints every pin `words.c` holds: the fifteen
operations' terms and the nine constructors it reads. Lean's print equals the old
pins byte for byte.

- **Lists.** `len`, `at`, `app`, `take` and `drop` compute `length`, `getD`, `++`,
  `take` and `drop` on Scott lists whose elements are any terms (`len_spec` ..
  `drop_spec`). `listFireC`, `list_fire`'s result line for line, is a reduct of the
  redex whenever it fires (`listFireC_sound`).
- **Bit strings.** `beq` decides equality, `bget` looks a key up in a trie, `No`
  where it holds nothing, and `ideq` compares two names' bits (`beq_spec`,
  `bget_spec`, `ideq_spec`). The C's walk is modelled over a `View`, what `ctor_at`
  reads of a node, and proved sound level by level (`beq_fire`, `bget_fire`,
  `ideq_fire`).
- **The constructors.** Each term `ctor_at` stands for is lean-ski's compiled
  constructor of the shape it reads (`ctors_compiled`): `Bz` is `ctorO 1 1 3`, `Nd0`
  is `K`, `No` is `K I`, and so on.

**What the proofs found.** When `bits_walk` meets a field not yet a value, it leaves
the operation applied to the fields it reached (`BITS_AGAIN`). `DESIGN.md` and
`reduce.c` called that a weak reduct of the redex. It is not. The redex reduces
through `Ycomb ⬝ G` to the knot over those fields, and so does the term the fire
leaves, but Curry's Y reaches its knot only one way: the two are convertible, with a
common reduct. That is enough: by lean-ski's `church_rosser` they share every normal
form. Both comments now say so.

**What stays trusted.** The models (`listFireC` and the walks) as readings of the C;
`View.OK`, that `ctor_at` reads a constructor template's node over its fields, or `K`
and `K I`, as that constructor; and the glue of §1, which builds and reads the cells.
