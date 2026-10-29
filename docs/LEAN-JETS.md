# Lean proofs for Avon's C jets: a plan

Written 2026-10-29. Every step is done (§4 to §8; 2026-10-29). A jet is native code that stands for a term (`DESIGN.md` §6);
today most of Avon's jets are licensed by testing. This note plans their proofs in
Lean, jet by jet, and records what each proof covers and what stays trusted.

## 1. Three things a proof can cover

Each C jet carries three obligations.

1. **The term computes the function.** A Lean theorem that the jet's pinned term,
   applied to the encodings of its arguments, weakly reduces to the encoding of
   the result. lean-ski states this shape as `Implements` (`Ski/DataJet.lean`);
   Avon's theorems have that shape, without building `Implements` values.
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

**Each jet is proved alone.** No theorem states a share-mode run with several
jets firing. That such a run stays convertible with the plain run follows from
the pieces, each rewrite convertible, and by lean-ski's `church_rosser` their
normal forms agree; Lean does not state the composite.

## 2. The jets

Every entry in the third column is a Lean model of the C, read against it by
inspection; only Poseidon2's is printed into the C. The last column leaves out
the glue of §1 and each step's "What stays trusted".

| jet | the term computes the function | the C computes the function | left |
|---|---|---|---|
| supercombinator templates (`tmpl.c`) | done for all at once: lean-ski's `absN_beta_subst` | done: the load check (`absC_eq`, `loadC_accept`) and the instance (`template_fire`), modelled; the replay compares the load counts with the loader's | nothing |
| Scott constructors (§6.8) | done: they compile through `ctorO` | done as templates; the dispatch that fires them is glue | nothing |
| Poseidon2 (`--p2`, §6.12) | done: lean-ski's `P_specN`, P on every state of sixteen values below 2^31 | done: `AvonP2.permuteC`, printed into `src/p2_prog.h`; reading and building the state is glue | nothing |
| numeral words: `add` `sub` `mul` `ifeq` `ifle` `div` `rem` (§6.10) | done: `add_spec` .. `rem_spec` | done: `fireC_num`, `fireC_arg` | nothing; a witness still needs word cells |
| list words: `len` `at` `app` `take` `drop` | done: `len_spec` .. `drop_spec` | done: `listFireC_sound`; the cell walks are glue | nothing |
| bit strings: `beq` `bget` `ideq` | done: `beq_spec`, `bget_spec`, `ideq_spec` | done: `beq_fire`, `bget_fire`, `ideq_fire`, over a view of `ctor_at` (`View.OK`, trusted) | nothing |
| Y in one step (`--fix`, §6.11) | done, not a reduction (below): convertible for every term (`fix_join`), and Y's simulation up to `Tr`, Y a jet (`fix_simulation`) | one node written; `--memory`'s memo is trusted | the simulation for Avon's Y, marked by tree identity, beyond `sum` and `loop` (§7); a witness row is not built |
| the interpreter jet (§7) | done for `whnfF`: the paper's fuel adequacy (`whnfF_adequate`) | a copy-mode loop: trusted as `evalF`, tested | the cores `wf5Abs`, `wf5Omg`, `wfQ`, `wfN` |
| the unquoter (`install_fire`), the compiler jet (`compile_fire`), residual jets (§6.5), data-jet dispatch and deferral | not covered | tested | both columns |

**Y is not a weak reduction.** Curry's Y does not reduce `Y g` to `g (Y g)`: it
reduces to `X X`, with `X = S (S (K S) K) (K (S I I)) g`, and `X X` reduces to
`g (X X)`. `Y g` and `g (Y g)` are convertible (`fix_join`), and in general neither
is a reduct of the other, a standard fact Lean does not restate, so
`--fix`'s rewrite needs the simulation theorem up to lean-ski's `Tr` that §6.11
and §18.4 name as owed, not an `Implements` lemma (§7).

## 3. Order

1. **Numeral words**, by `P2Prog.lean`'s pattern (§4).
2. **List words, then bit strings**, on the same scaffolding (§5).
3. **Templates**: the load check and the instance (§6).
4. **Y's simulation theorem** (§7).
5. **The interpreter jet's adequacy theorem** (§8).

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
`uint64_t` from two word values, each at most `AV_WORD_MAX = 2^27 - 1`, and
declines any result over `AV_WORD_MAX` or one that would build more than
`WORD_BUILD_MAX` nodes; `sub` walks predecessors, and the comparisons choose an
operand.
A Lean model of that arithmetic, over `UInt64` and `UInt32`, is proved to agree
with the specification wherever the C fires, as `sboxC` models `av_p2_sbox`. The
loops that build the result word are glue.

**Done when** `make words-lean-check` elaborates `lean/Words.lean` against
lean-ski's pin, every theorem checked by the kernel, and finds
`src/word_pins.h` byte-identical to Lean's output; `make check` passes with
`words.c` reading the printed header.

**Done, 2026-10-29.** `lean/Words.lean` proves the seven operations' terms
(`add_spec` .. `rem_spec`) and `word_fire`'s arithmetic (`fireC_num`,
`fireC_arg`), each on lean-ski's axioms only (`propext`, `Quot.sound`). Lean's
print equals the pins `words.c` held, byte for byte, so no term changed. The files it imports are unchanged since lean-ski's
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
`reduce.c` called that a weak reduct of the redex. The proof shows only that the
two are convertible: the redex reduces through `Ycomb ⬝ G` to the knot over those
fields, and so does the term the fire leaves, so they share a reduct. Whether the
term is also a reduct of the redex is not proved. Convertible is enough: by
lean-ski's `church_rosser` the two share every normal form. Both comments now say
convertible.

**What stays trusted.** The models (`listFireC` and the walks) as readings of the C;
`View.OK`, that `ctor_at` reads a constructor template's node over its fields, or `K`
and `K I`, as that constructor, which rests on the loader's shape tag naming the
template's term (`ctors_compiled` ties the shape to the term, not the tag to the
template); and the glue of §1, which builds and reads the cells.

## 6. Step 3: templates

**Done, 2026-10-29.** `lean/Templates.lean` proves the check `src/tmpl.c` makes
before it uses a template, and the fire that follows.

- **The check computes lean-ski's abstraction.** `absC`, `hc_abstract` line for
  line, is lean-ski's `abs` (`absC_eq`), and `load_one`'s loop over the formals is
  `absN` (`keyC_eq`). A template `load_one` accepts has key `absN xs body`
  (`loadC_accept`).
- **The fire is a reduct.** `compile` is `load_one`'s compile into instructions,
  constants and arguments; `instC` is `tmpl_instance`'s run of them. For an accepted
  template whose referenced terms hold no formal, and exactly as many arguments as
  formals, the key applied to them weakly reduces to what `tmpl_instance` builds
  (`template_fire`, from lean-ski's `absN_beta_subst`). The
  proof covers every producer, since Python's files, front1's and discovery's
  templates all pass the same `load_one`.
- **The replay.** `Replay.replay` runs `av_templates_load`'s loop with the model of
  the check, the file's digests (SHA-256, written in Lean) and the duplicate check.
  `make templates-lean-check` requires its counts, accepted, refused and skipped, to
  be Avon's on the five sets the tests ship (137 accepted, 56 skipped) and on eight
  copies, each changed to reach one refusal path. It compares totals, not template
  by template, and runs neither `compile` nor `instC`, which are read against
  `tmpl_instance` by inspection. No copy reaches a digest collision
  (`jet_collision`). The η copy's body, `K K` applied to its formal, is skipped as
  an η-template and refused without that check, so the replay tells them apart.

**The plan changed.** §3 said Lean would check the loaded table "replacing the
check in C", with lean-ski's `rootOKB`. That was the wrong design. Avon cannot run
Lean at load; discovery makes templates at run time, with no file for Lean to
read; and `rootOKB` licenses a witness heap's roots, not a share-mode table. The
check stays in C and is now proved, and the replay checks the model against the C. The
change was approved on 2026-10-29: this, not a check in Lean replacing the C, is
step 3.

**What the proofs settled.**

- *Repeated formals.* `load_one` binds a formal to its last occurrence (`argix`),
  and lean-ski's `override` does the same, so a template like `λ x x. x` is sound
  as Avon loads it (`override_lastIdx`).
- *Referenced terms hold no formal.* `hc_abstract` reads a formal's marker leaf
  anywhere, inside a referenced term too, while the compile treats that term as a
  constant. Both parsers refuse a leaf name beginning `@`, the markers' prefix, so
  a referenced term cannot hold one; `template_fire` takes it as a hypothesis.

**What stays trusted.** The models as readings of the C (the replay tests the
check's by its counts); `hc_canon`, that a canonical node is the term it stands
for; the globals, each a jet node standing for its constant; the parsers' refusal
of `@` names, which gives `template_fire`'s hypothesis; and the reducer's other
paths for a template, which act as the instance would and are tested, not proved:
a constructor's dispatch, a case's join, a successor built as a word (`sucop`), a
deferred root (`tmpl_defer`) and the root written in place.

## 7. Step 4: Y in one step

**Done, 2026-10-29.** `lean/Fix.lean` proves what `--fix`'s rewrite, `Y g` to
`g (Y g)`, keeps. It has two parts, both approved before they were built.

- **A. Any term.** A run that mixes weak steps with the rewrite, at any position
  and in any order, stays convertible with the plain run: whatever it reaches has a
  common reduct with its start (`fix_join`, from lean-ski's `church_rosser`). So a
  normal form `--fix` reaches is the one SKI's reduction reaches (`fix_normal`).
  DESIGN §6.11 had claimed this "by Church-Rosser"; now it is proved. A licenses
  `--fix` in share mode.
- **B. Y's simulation up to `Tr`, Y a jet.** Here Y is a constant with one rule,
  never looked inside, placed where the compiler ties recursion. `compJ` is
  lean-ski's compiler with each recursive equation's `Ycomb` the jet, and `TrJ` is
  lean-ski's `Tr` over it. Every source step of a compiled program is matched by a
  run with the jet, a recursive call being the jet's one step (`simulationJ`).
  Read back, Y as `Ycomb`, the jet program is lean-ski's compiled program
  (`fixed_of_fixedJ`), and every jet state a compiled form of its source state by
  lean-ski's own `Tr` (`tr_of_trJ`, `fix_simulation`). B is not vacuous: the
  kernel decides the jet program's `FixedJ` for lean-ski's compiled `sum` and
  `loop`, four recursive equations each, with each `Ycomb` of the compiled program
  the jet (`jetify`), and their read-back is lean-ski's own environment
  (`sum_fixedJ`, `loop_fixedJ`); `sum_fix_simulation` is the simulation for `sum`.
- **What B covers of Avon.** Avon marks Y by tree identity, every `Ycomb` in the
  term and the globals (`tmpl.c`), not only where the compiler ties recursion. B
  speaks of Avon's runs where the two markings agree: checked for `sum` and `loop`,
  not for lean-ski's `kernel` or `corpus`, and false for the program below. A
  witness row licensed by B must fire only at the compiler's recursion sites, or
  each program must pass that check; the row is not built. No theorem reads a run
  with the jet back as a run of A's.

**Why B takes Y as a jet.** As first stated, B said the run that always uses the
rewrite and never S-reduces a Y redex matches every source step through `Tr`. That
is false under Avon's tree identity. The closure `λx. S I I (S (K x) (S I I))`
compiles to `Ycomb` exactly (`closure_spells_Y`). Applied to `K`, the source steps
to `S I I (S (K K) (S I I))`, whose only compiled form is that term; a run that
rewrites every `Ycomb` redex and never S-reduces one reaches from `Ycomb ⬝ K` only `K`
wrapped around it. So the statement is false (`first_B_false`). Part A still covers
that program, since the two are convertible. B over a jet was approved on 2026-10-29.

**What stays trusted.** That Avon's rewrite is `FixStep.fix` and `JStep.fix`
(`src/reduce.c` writes the redex root as `App(g, y)`, `y` a fresh `App(Y, g)`);
`--memory`'s memo (`ymemo`), which points a later `Y g` at the node an earlier one
unfolded to, perhaps reduced since, a run A covers but not one rewrite; and the reducer's
strategy, which takes one of the runs these theorems allow. That `--fix` reaches
every normal form the plain run reaches is still shown by tests, not proved.

## 8. Step 5: the interpreter jet

**Done, 2026-10-29, for `whnfF`.** `lean/Interp.lean` proves the tower's adequacy
theorem for the 618-atom self-interpreter the jet serves. The ski-in-ski paper
states it as Lemma `lem:step` and Theorem `thm:fuel` and proves it on paper; now it
is checked by the kernel, for the exact term.

- **Fuel adequacy** (`whnfF_adequate`). Given fuel `k` and an encoded term `M`,
  `whnfF ⟨k⟩ ⟨M⟩` reduces to the encoding of lean-ski's `evalF k M`: `Just` the weak
  head normal form `M` reaches within `k` step-attempts, `Nothing` otherwise. The
  jet fires only on those encodings, read by structure, and is trusted to compute
  `evalF` (below), so its answer is a reduct of the interpreter's.
- **Step adequacy** (`step_spec`). `step ⟨M⟩` reduces to `Nothing` in weak head
  normal form and to `Just ⟨M'⟩` when `M` contracts its head redex to `M'`, as
  lean-ski's `step?` says. Under it are the spine walker (`sp_spec`), the rebuilder
  (`rb_spec`) and the three arms, each by kernel-checked symbolic runs.
- **The pins.** The generators reassemble the dictionary's 618 atoms exactly
  (`whnf_pin`), and the object type's constructors are lean-ski's `quoteT`
  (`pins_compiled`). `make interp-lean-check` requires Lean's print of `whnfF` and
  its constructors to be the conformance dictionary's terms, byte for byte;
  `interpreters.tsv`'s `whnfF` core to be keyed by that term, over those object and
  result constructors; and its `nat` line to be `encNat`'s `Zero` and `Suc`.

**Scope, approved 2026-10-29.** The jet serves five cores; the plan's theorem is
`whnfF`'s. `wf5Abs` and `wf5Omg` add a leaf whose arm errs or diverges, and `wfQ` and
`wfN` a `Scry` leaf answered from a fact store; their adequacy is not proved.

**The audit's finding (2026-10-29).** The jet read its datum by probing, so it
fired on a term that only behaves as an encoding. At fuel 1, `S (K ⟨S⟩) I` probes
as `⟨S⟩`: the interpreter answers `Just` the datum itself, and the jet answered
`Just ⟨S⟩`, a different normal form, which `--jet-check`, decoding both by probing,
missed. The theorem never covered such data. The jet now reads the datum and the
fuel by structure only, and declines anything else; `test_interp` keeps that case.
The corpus pays for it: the conformance run fires the jet 66 times, against 86
before; the other 20 data are not yet constructors by structure, and the
interpreter runs them.

**Why probing was the wrong licence.** A probe applies a datum to fresh marker
atoms and reads which marker comes back. Two terms that agree on fresh atoms are
extensionally equal (Hindley and Seldin, *Lambda-Calculus and Combinators*, 2008,
Chapter 8), not weakly equal, and a jet's licence is weak equality. The look-alike
is `⟨S⟩`'s η-expansion: applied to any term it reduces to `⟨S⟩` applied to that
term (`lookalike_probes_as_S`), so no probe tells them apart. Yet `Just` of each
has a different normal form, so the two answers have no common reduct
(`lookalike_answers_apart`, by `church_rosser`). Probing is sound up to
extensional equality, and reading by structure keeps the jet within weak
equality, the relation `whnfF_adequate` proves. `make interp-lean-check` checks
both theorems.

**What stays trusted.** That the jet's copy-mode run computes `evalF`: `reduce.c`'s
copy mode as lean-ski's `step?`, one fuel unit per step-attempt, which
`tests/test_interp.c` and the conformance fuel cases test; the datum's reading by
structure and the outcome's encoding; and residual jets inside the object run
keeping copy-mode counts (§6.5).
