import Ski.BitArith
import Ski.Words
import Ski.Compile

/-!
# Avon's word operations, proved, and their pins printed

Share mode runs fifteen operations natively on words (`--data`,
`docs/DESIGN.md` §6.10 and §6.14): seven on numerals, five on lists and
three on bit strings, tries and names.  A node whose function is an
operation's pinned term, node for node, applied to values, is replaced by
the result.  This file proves both halves of that replacement and prints
the pins (`docs/LEAN-JETS.md`).

* **The terms compute the operations**, for every input, by weak
  reduction.  `encNat` is lean-ski's Scott numeral, `encList` a Scott list
  of terms, `encBits` a bit string least significant bit first.
  - Numerals (`add_spec` .. `rem_spec`): `op ⬝ ⌜m⌝ ⬝ ⌜n⌝ ↠ ⌜m op n⌝`, `sub`
    truncating at 0, `m / 0 = 0` and `m % 0 = m` as skijack's are;
    `ifeq_spec` and `ifle_spec` choose their third or fourth argument.
  - Lists (`len_spec` .. `drop_spec`): `length`, `getD`, `++`, `take` and
    `drop`, the elements any terms.
  - Bit strings (`beq_spec`, `bget_spec`, `ideq_spec`): equality as a
    Scott Boolean, a trie's lookup, `No` where it holds nothing, and two
    names' equality by their bits.  Each level of `beq` and `bget` is also
    proved over any terms below the first constructor (`beq_step`,
    `bget_step`), which is what the C's walk needs.
* **The C computes them.**
  - `fireC` is `word_fire`'s arithmetic, line for line: `v` and `need` in
    `uint64_t` from two `uint32_t` word values, the declines, and the
    loops that build the result.  Whenever it leaves a word, the term
    reduces to that word's numeral (`fireC_num`, `fireC_arg`).
  - `listFireC` is `list_fire`'s: `m`, `need`, the declines, the walks and
    `list_prefix`.  Whatever it leaves, the term reduces to
    (`listFireC_sound`).
  - `beqWalk`, `bgetWalk` and `ideqWalk` are `bits_walk`'s, over a `View`
    of the reducer's nodes: what `ctor_at` reads of each.  `BITS_TO` and
    `BITS_KI` are reducts of the redex; `BITS_AGAIN`, the operation over
    the fields the walk reached, is convertible with it, not a reduct
    (`beq_fire`, `bget_fire`), and `ideq` never leaves itself on
    (`ideq_fire`).
* **The pins are Lean's.**  `header` prints `src/word_pins.h`: the
  fifteen terms `src/words.c` matches and the constructors it reads, so
  the terms proved are the terms matched.  Each constructor is lean-ski's
  compiled constructor of the shape `ctor_at` reads (`ctors_compiled`).

**The method** is `Ski/BitArith.lean`'s.  Each recursive pin is
`Ycomb ⬝ G`, and `Ycomb ⬝ G` reduces to a knot `R` with `R ↠ G ⬝ R`
(`ycomb_knot`, `knot_unroll`).  One unfolding of `G`, with the knot, the
operands' fields and the other arguments as variables, is a symbolic run
the kernel checks (`wnf`, `run`; `oiter` where the result is the input
itself, as `drop l 0`).  The constructors `G` builds, `Suc` and `cons`, are
variables 20 and 24, and the operations a generator inlines, `add` in
`mul`, `ifle` and `sub` in `div` and `rem`, `beq` in `ideq`, are variables
21 to 23 and 25, so a run stops at them and their own theorems take over.
Induction on the recursed operand closes the variables; `div` and `rem`
take strong induction on `m`.

**What stays trusted:** that `fireC`, `listFireC` and the walks read as
the C does (read them beside `src/reduce.c`); that the `View` is right
(`View.OK`: `ctor_at` reads a constructor template's node over its
fields, or `K`, `K I`, as that constructor); the printer `pr`; and the
reducer's glue: the match, the reading of words and list words, the
cells it builds, and the write of the result.  The theorems are about
values; a jet's count is not the term's (`docs/DESIGN.md` §6.5).

Run from lean-ski, which supplies `Ski.BitArith`:

    cd ~/Code/ski/lean-ski && lake env lean --run ~/avon/lean/Words.lean OUT.h

The kernel checks the theorems as the file elaborates; `main` then writes
the header to `OUT.h`.  `tests/words_lean_check.sh` compares it with
`src/word_pins.h`, byte for byte.
-/

open Term BitArith

namespace AvonWords

-- ---------------------------------------------------------------------------
-- The generators
-- ---------------------------------------------------------------------------

/-- `add`'s generator: `add self m 0 = m`; `add self m (n+1) = Suc (self m n)`. -/
def addG : OTerm :=
  .S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ .I)) ⬝ₒ .K)))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.var 20))))))

/-- `sub`'s generator: `sub self m 0 = m`; `sub self m (n+1) = self (m K I) n`, `m K I` the predecessor. -/
def subG : OTerm :=
  .S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ .I)) ⬝ₒ .K)))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K))) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ .K) ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ .K)) ⬝ₒ (.K ⬝ₒ .I)))))

/-- `mul`'s generator: `mul self m 0 = 0`; `mul self m (n+1) = add m (self m n)`. -/
def mulG : OTerm :=
  .S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ .K)))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K))) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.var 21)))))

/-- `ifeq`'s generator: `ifeq self m n a b`: `a` at `0 0`, `b` at `0 (n+1)` and `(m+1) 0`, `self m n a b` at `(m+1) (n+1)`. -/
def ifeqG : OTerm :=
  .S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))))) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ .K))))) ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K)))) ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ .K)))))))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K)))))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))))) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))))) ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ .K)))))))) ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ .K)))))))

/-- `ifle`'s generator: `ifle self m n a b`: `a` at `0 n`, `b` at `(m+1) 0`, `self m n a b` at `(m+1) (n+1)`. -/
def ifleG : OTerm :=
  .S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K)))))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K)))))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))))) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))))) ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ .K)))))))) ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ .K)))))))

/-- `div`'s generator: `div self m n = n 0 (K (ifle n m (Suc (self (sub m n) n)) 0))`. -/
def divG : OTerm :=
  .S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ .K)))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K))))) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.var 23))) ⬝ₒ .K)))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.var 20)))))) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ .K))) ⬝ₒ (.K ⬝ₒ (.var 22))))) ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ .I))))))) ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ .K)))))

/-- `rem`'s generator: `rem self m n = n m (K (ifle n m (self (sub m n) n) m))`. -/
def remG : OTerm :=
  .S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ .I)) ⬝ₒ .K)))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K))))) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.var 23))) ⬝ₒ .K)))) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ .K))) ⬝ₒ (.K ⬝ₒ (.var 22))))) ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ .I)))))) ⬝ₒ (.K ⬝ₒ .K)))

/-- `len`'s generator: `len self l`: `0` at `[]`, `Suc (self r)` at `x :: r`. -/
def lenG : OTerm :=
  .S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ .K)))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.var 20)))))

/-- `at`'s generator: `at self l i d`: `d` at `[]`, `x` at `x :: r` and `0`, `self r q d` at `x :: r` and `q+1`. -/
def atG : OTerm :=
  .S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ .S)))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K)))))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K))) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))))) ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ .K)))))) ⬝ₒ (.K ⬝ₒ .K))))))

/-- `app`'s generator: `app self l m`: `m` at `[]`, `cons x (self r m)` at `x :: r`. -/
def appG : OTerm :=
  .S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ .S)) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.var 24))))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K))) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ .S)) ⬝ₒ (.K ⬝ₒ .K)))))

/-- `take`'s generator: `take self l i`: `[]` at `[]` or `0`, `cons x (self r q)` at `x :: r` and `q+1`. -/
def takeG : OTerm :=
  .S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ .K)))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ .K)))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.var 24))))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K))) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ .S)) ⬝ₒ (.K ⬝ₒ .K)))))))

/-- `drop`'s generator: `drop self l i`: `[]` at `[]`, `l` at `0`, `self r q` at `x :: r` and `q+1`. -/
def dropG : OTerm :=
  .S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ .I)) ⬝ₒ .K)))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ .K)))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K))) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ .S)) ⬝ₒ (.K ⬝ₒ .K))))))

/-- `beq`'s generator: `beq self a b`: `Yes` at `Bn Bn`, `self r s` at `Bz r, Bz s` and `Bo r, Bo s`, `No` otherwise. -/
def beqG : OTerm :=
  .S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ .K) ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ .K)) ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ .I)))) ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ .I))))))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ .I))))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ .I)))) ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ .I)))))))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ .I))) ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ .I)))))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ .I)))

/-- `bget`'s generator: `bget self k t`: `No` at `Nd0`; at `NdT (NdB v z o)`, `v` at `Bn`, `self r z` at `Bz r`, `self r o` at `Bo r`. -/
def bgetG : OTerm :=
  .S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ .I))))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ .I)))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K))) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K))))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K)))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ .S)) ⬝ₒ (.K ⬝ₒ .K)))))))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ .S)) ⬝ₒ (.K ⬝ₒ .K)))))))))

/-- `ideq x y = beq (bits x) (bits y)`, a name's bits `Bn` for `IdRaw`: not recursive itself. -/
def ideqO : OTerm :=
  .S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.var 25)) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ .K)))) ⬝ₒ (.K ⬝ₒ .I))))) ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ .K)))) ⬝ₒ (.K ⬝ₒ .I)))

/-- Scott's constructors as skijack compiles them: lists' `cons`; bit strings' `Bn`, `Bz` and
    `Bo`; tries' `NdT` and `NdB`; names' `IdRaw` and `Id`.  (`Nd0`, `[]` and `0` are `K`.) -/
def consT : Term := S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)))) ⬝ (K ⬝ K))
def bnT : Term := S ⬝ (K ⬝ K) ⬝ K
def bzT : Term := S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K))
def boT : Term := S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K))
def ndtT : Term := S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)
def ndbT : Term := S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ S))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ S))) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)))) ⬝ (K ⬝ K)))))) ⬝ (K ⬝ (K ⬝ K))
def idrawT : Term := S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)
def idT : Term := S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)

/-- The environment of the generators' named subterms: `Suc` and `cons`. -/
def env0 : Nat → Term := fun i => if i = 20 then Scott.Suc else if i = 24 then consT else K

def addT : Term := Ycomb ⬝ addG.close env0
def subT : Term := Ycomb ⬝ subG.close env0
def ifleT : Term := Ycomb ⬝ ifleG.close env0
def lenT : Term := Ycomb ⬝ lenG.close env0
def atT : Term := Ycomb ⬝ atG.close env0
def appT : Term := Ycomb ⬝ appG.close env0
def takeT : Term := Ycomb ⬝ takeG.close env0
def dropT : Term := Ycomb ⬝ dropG.close env0
def beqT : Term := Ycomb ⬝ beqG.close env0
def bgetT : Term := Ycomb ⬝ bgetG.close env0

/-- The environment with the operations other generators inline. -/
def env : Nat → Term := fun i =>
  if i = 20 then Scott.Suc else if i = 21 then addT else if i = 22 then subT
  else if i = 23 then ifleT else if i = 24 then consT else if i = 25 then beqT else K

def mulT : Term := Ycomb ⬝ mulG.close env
def ifeqT : Term := Ycomb ⬝ ifeqG.close env
def divT : Term := Ycomb ⬝ divG.close env
def remT : Term := Ycomb ⬝ remG.close env
def ideqT : Term := ideqO.close env

/-- Variables `0 .. xs.length - 1` closed to `xs`, the rest by `env`. -/
def sig (xs : List Term) (i : Nat) : Term := xs.getD i (env i)

-- ---------------------------------------------------------------------------
-- Curry's knot
-- ---------------------------------------------------------------------------

/-- `Bterm ⬝ G`, and the knot `X ⬝ X` that `Ycomb ⬝ G` unrolls through. -/
def knotX (G : Term) : Term := S ⬝ (S ⬝ (K ⬝ S) ⬝ K) ⬝ (K ⬝ (S ⬝ I ⬝ I)) ⬝ G
def knot (G : Term) : Term := knotX G ⬝ knotX G

def knotXO : OTerm := .S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ .K) ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ .I ⬝ₒ .I)) ⬝ₒ .var 0

theorem ycomb_knot (G : Term) : WSteps (Ycomb ⬝ G) (knot G) := by
  have h1 := ((oiter_sound (k := 4) (t := Ycomb.toO ⬝ₒ .var 0)
    (u := knotXO ⬝ₒ (.I ⬝ₒ knotXO)) rfl).weak).close (fun _ => G)
  have h2 : WSteps (knotX G ⬝ (I ⬝ knotX G)) (knot G) := WSteps.right _ (.single (.I _))
  exact h1.trans h2

theorem knot_unroll (G : Term) : WSteps (knot G) (G ⬝ knot G) := by
  have h1 := ((oiter_sound (k := 5) (t := knotXO ⬝ₒ knotXO)
    (u := .var 0 ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ .I ⬝ₒ .I) ⬝ₒ .var 0 ⬝ₒ knotXO)) rfl).weak).close (fun _ => G)
  have h2 := ((oiter_sound (k := 3) (t := .K ⬝ₒ (.S ⬝ₒ .I ⬝ₒ .I) ⬝ₒ .var 0 ⬝ₒ knotXO)
    (u := knotXO ⬝ₒ (.I ⬝ₒ knotXO)) rfl).weak).close (fun _ => G)
  have h3 : WSteps (knotX G ⬝ (I ⬝ knotX G)) (knot G) := WSteps.right _ (.single (.I _))
  exact h1.trans (WSteps.right G (h2.trans h3))


/-- A recursive call of two arguments: the knot unrolled once under them. -/
theorem knot_call2 (G a b : Term) : WSteps (knot G ⬝ a ⬝ b) (G ⬝ knot G ⬝ a ⬝ b) :=
  ((knot_unroll G).left a).left b

/-- A recursive call of four arguments. -/
theorem knot_call4 (G a b c d : Term) :
    WSteps (knot G ⬝ a ⬝ b ⬝ c ⬝ d) (G ⬝ knot G ⬝ a ⬝ b ⬝ c ⬝ d) :=
  ((knot_call2 G a b).left c).left d

-- ---------------------------------------------------------------------------
-- Numerals
-- ---------------------------------------------------------------------------

/-- `⌜m⌝ ⬝ K ⬝ I`, the predecessor `sub` takes. -/
theorem pred_spec : ∀ m : Nat, WSteps (encNat m ⬝ K ⬝ I) (encNat (m - 1))
  | 0 => .single (.K _ _)
  | m + 1 => by
    have h := run (n := 10) (t := Scott.Suc.toO ⬝ₒ .var 0 ⬝ₒ .K ⬝ₒ .I) (u := .var 0) (by decide)
      (sig [encNat m])
    simpa [OTerm.close, close_toO, sig, encNat] using h

-- ---------------------------------------------------------------------------
-- add
-- ---------------------------------------------------------------------------

theorem add_knot (m : Nat) : ∀ n : Nat,
    WSteps (knot (addG.close env0) ⬝ encNat m ⬝ encNat n) (encNat (m + n))
  | 0 => by
    have h := run (n := 50) (t := addG ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ Scott.Zero.toO) (u := .var 1)
      (by decide) (sig [knot (addG.close env0), encNat m])
    exact (knot_call2 _ (encNat m) (encNat 0)).trans h
  | n + 1 => by
    have h := run (n := 50) (t := addG ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ (Scott.Suc.toO ⬝ₒ .var 2))
      (u := .var 20 ⬝ₒ (.var 0 ⬝ₒ .var 1 ⬝ₒ .var 2))
      (by decide) (sig [knot (addG.close env0), encNat m, encNat n])
    exact (knot_call2 _ (encNat m) (encNat (n + 1))).trans (h.trans (WSteps.right _ (add_knot m n)))

theorem add_spec (m n : Nat) : WSteps (addT ⬝ encNat m ⬝ encNat n) (encNat (m + n)) :=
  (((ycomb_knot _).left _).left _).trans (add_knot m n)

-- ---------------------------------------------------------------------------
-- sub
-- ---------------------------------------------------------------------------

theorem sub_knot : ∀ (n m : Nat),
    WSteps (knot (subG.close env0) ⬝ encNat m ⬝ encNat n) (encNat (m - n))
  | 0, m => by
    have h := run (n := 50) (t := subG ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ Scott.Zero.toO) (u := .var 1)
      (by decide) (sig [knot (subG.close env0), encNat m])
    exact (knot_call2 _ (encNat m) (encNat 0)).trans h
  | n + 1, m => by
    have h := run (n := 50) (t := subG ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ (Scott.Suc.toO ⬝ₒ .var 2))
      (u := .var 0 ⬝ₒ (.var 1 ⬝ₒ .K ⬝ₒ .I) ⬝ₒ .var 2)
      (by decide) (sig [knot (subG.close env0), encNat m, encNat n])
    have e : m - (n + 1) = m - 1 - n := by omega
    rw [e]
    exact (knot_call2 _ (encNat m) (encNat (n + 1))).trans
      (h.trans ((WSteps.right _ (pred_spec m)).left _ |>.trans (sub_knot n (m - 1))))

theorem sub_spec (m n : Nat) : WSteps (subT ⬝ encNat m ⬝ encNat n) (encNat (m - n)) :=
  (((ycomb_knot _).left _).left _).trans (sub_knot n m)


/-- A numeral as its own eliminator: `⌜n+1⌝ ⬝ z ⬝ s ↠ s ⬝ ⌜n⌝`. -/
theorem suc_elim (n : Nat) (z s : Term) : WSteps (encNat (n + 1) ⬝ z ⬝ s) (s ⬝ encNat n) :=
  run (n := 10) (t := Scott.Suc.toO ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2) (u := .var 2 ⬝ₒ .var 0)
    (by decide) (sig [encNat n, z, s])

theorem zero_elim (z s : Term) : WSteps (encNat 0 ⬝ z ⬝ s) z := .single (.K _ _)

-- ---------------------------------------------------------------------------
-- mul
-- ---------------------------------------------------------------------------

theorem mul_knot (m : Nat) : ∀ n : Nat,
    WSteps (knot (mulG.close env) ⬝ encNat m ⬝ encNat n) (encNat (m * n))
  | 0 => by
    have h := run (n := 80) (t := mulG ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ Scott.Zero.toO) (u := .K)
      (by decide) (sig [knot (mulG.close env), encNat m])
    exact (knot_call2 _ _ _).trans h
  | n + 1 => by
    have h := run (n := 80) (t := mulG ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ (Scott.Suc.toO ⬝ₒ .var 2))
      (u := .var 21 ⬝ₒ .var 1 ⬝ₒ (.var 0 ⬝ₒ .var 1 ⬝ₒ .var 2))
      (by decide) (sig [knot (mulG.close env), encNat m, encNat n])
    have e : m * (n + 1) = m + m * n := by rw [Nat.mul_succ, Nat.add_comm]
    rw [e]
    exact (knot_call2 _ _ _).trans
      (h.trans ((WSteps.right _ (mul_knot m n)).trans (add_spec m (m * n))))

theorem mul_spec (m n : Nat) : WSteps (mulT ⬝ encNat m ⬝ encNat n) (encNat (m * n)) :=
  (((ycomb_knot _).left _).left _).trans (mul_knot m n)

-- ---------------------------------------------------------------------------
-- ifeq and ifle
-- ---------------------------------------------------------------------------

theorem ifeq_knot (a b : Term) : ∀ m n : Nat,
    WSteps (knot (ifeqG.close env) ⬝ encNat m ⬝ encNat n ⬝ a ⬝ b) (if m = n then a else b)
  | 0, 0 => by
    have h := run (n := 80)
      (t := ifeqG ⬝ₒ .var 0 ⬝ₒ Scott.Zero.toO ⬝ₒ Scott.Zero.toO ⬝ₒ .var 5 ⬝ₒ .var 6) (u := .var 5)
      (by decide) (sig [knot (ifeqG.close env), K, K, K, K, a, b])
    rw [if_pos rfl]; exact (knot_call4 _ _ _ _ _).trans h
  | 0, n + 1 => by
    have h := run (n := 80)
      (t := ifeqG ⬝ₒ .var 0 ⬝ₒ Scott.Zero.toO ⬝ₒ (Scott.Suc.toO ⬝ₒ .var 2) ⬝ₒ .var 5 ⬝ₒ .var 6)
      (u := .var 6) (by decide) (sig [knot (ifeqG.close env), K, encNat n, K, K, a, b])
    rw [if_neg (by omega)]; exact (knot_call4 _ _ _ _ _).trans h
  | m + 1, 0 => by
    have h := run (n := 80)
      (t := ifeqG ⬝ₒ .var 0 ⬝ₒ (Scott.Suc.toO ⬝ₒ .var 1) ⬝ₒ Scott.Zero.toO ⬝ₒ .var 5 ⬝ₒ .var 6)
      (u := .var 6) (by decide) (sig [knot (ifeqG.close env), encNat m, K, K, K, a, b])
    rw [if_neg (by omega)]; exact (knot_call4 _ _ _ _ _).trans h
  | m + 1, n + 1 => by
    have h := run (n := 80)
      (t := ifeqG ⬝ₒ .var 0 ⬝ₒ (Scott.Suc.toO ⬝ₒ .var 1) ⬝ₒ (Scott.Suc.toO ⬝ₒ .var 2)
        ⬝ₒ .var 5 ⬝ₒ .var 6)
      (u := .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2 ⬝ₒ .var 5 ⬝ₒ .var 6)
      (by decide) (sig [knot (ifeqG.close env), encNat m, encNat n, K, K, a, b])
    have e : (if m + 1 = n + 1 then a else b) = if m = n then a else b := by simp
    rw [e]; exact (knot_call4 _ _ _ _ _).trans (h.trans (ifeq_knot a b m n))

theorem ifeq_spec (m n : Nat) (a b : Term) :
    WSteps (ifeqT ⬝ encNat m ⬝ encNat n ⬝ a ⬝ b) (if m = n then a else b) :=
  (((((ycomb_knot _).left _).left _).left _).left _).trans (ifeq_knot a b m n)

theorem ifle_knot (a b : Term) : ∀ m n : Nat,
    WSteps (knot (ifleG.close env0) ⬝ encNat m ⬝ encNat n ⬝ a ⬝ b) (if m ≤ n then a else b)
  | 0, 0 => by
    have h := run (n := 80)
      (t := ifleG ⬝ₒ .var 0 ⬝ₒ Scott.Zero.toO ⬝ₒ Scott.Zero.toO ⬝ₒ .var 5 ⬝ₒ .var 6) (u := .var 5)
      (by decide) (sig [knot (ifleG.close env0), K, K, K, K, a, b])
    rw [if_pos (by omega)]; exact (knot_call4 _ _ _ _ _).trans h
  | 0, n + 1 => by
    have h := run (n := 80)
      (t := ifleG ⬝ₒ .var 0 ⬝ₒ Scott.Zero.toO ⬝ₒ (Scott.Suc.toO ⬝ₒ .var 2) ⬝ₒ .var 5 ⬝ₒ .var 6)
      (u := .var 5) (by decide) (sig [knot (ifleG.close env0), K, encNat n, K, K, a, b])
    rw [if_pos (by omega)]; exact (knot_call4 _ _ _ _ _).trans h
  | m + 1, 0 => by
    have h := run (n := 80)
      (t := ifleG ⬝ₒ .var 0 ⬝ₒ (Scott.Suc.toO ⬝ₒ .var 1) ⬝ₒ Scott.Zero.toO ⬝ₒ .var 5 ⬝ₒ .var 6)
      (u := .var 6) (by decide) (sig [knot (ifleG.close env0), encNat m, K, K, K, a, b])
    rw [if_neg (by omega)]; exact (knot_call4 _ _ _ _ _).trans h
  | m + 1, n + 1 => by
    have h := run (n := 80)
      (t := ifleG ⬝ₒ .var 0 ⬝ₒ (Scott.Suc.toO ⬝ₒ .var 1) ⬝ₒ (Scott.Suc.toO ⬝ₒ .var 2)
        ⬝ₒ .var 5 ⬝ₒ .var 6)
      (u := .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2 ⬝ₒ .var 5 ⬝ₒ .var 6)
      (by decide) (sig [knot (ifleG.close env0), encNat m, encNat n, K, K, a, b])
    have e : (if m + 1 ≤ n + 1 then a else b) = if m ≤ n then a else b := by simp
    rw [e]; exact (knot_call4 _ _ _ _ _).trans (h.trans (ifle_knot a b m n))

theorem ifle_spec (m n : Nat) (a b : Term) :
    WSteps (ifleT ⬝ encNat m ⬝ encNat n ⬝ a ⬝ b) (if m ≤ n then a else b) :=
  (((((ycomb_knot _).left _).left _).left _).left _).trans (ifle_knot a b m n)

-- ---------------------------------------------------------------------------
-- div and rem
-- ---------------------------------------------------------------------------

/-- `div`'s body after its knot: `n` cased, then `ifle n m`. -/
theorem div_unfold (m n : Nat) :
    WSteps (knot (divG.close env) ⬝ encNat m ⬝ encNat n)
      (encNat n ⬝ K ⬝ (K ⬝ (ifleT ⬝ encNat n ⬝ encNat m
        ⬝ (Scott.Suc ⬝ (knot (divG.close env) ⬝ (subT ⬝ encNat m ⬝ encNat n) ⬝ encNat n)) ⬝ K))) :=
  (knot_call2 _ _ _).trans (run (n := 80) (t := divG ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2)
    (u := .var 2 ⬝ₒ .K ⬝ₒ (.K ⬝ₒ (.var 23 ⬝ₒ .var 2 ⬝ₒ .var 1
      ⬝ₒ (.var 20 ⬝ₒ (.var 0 ⬝ₒ (.var 22 ⬝ₒ .var 1 ⬝ₒ .var 2) ⬝ₒ .var 2)) ⬝ₒ .K)))
    (by decide) (sig [knot (divG.close env), encNat m, encNat n]))

theorem div_knot (n : Nat) : ∀ m : Nat,
    WSteps (knot (divG.close env) ⬝ encNat m ⬝ encNat n) (encNat (m / n)) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    refine (div_unfold m n).trans ?_
    cases n with
    | zero => rw [Nat.div_zero]; exact zero_elim K _
    | succ q =>
      refine (suc_elim q _ _).trans (WSteps.single (.K _ _) |>.trans ((ifle_spec _ _ _ _).trans ?_))
      by_cases hle : q + 1 ≤ m
      · rw [if_pos hle, Nat.div_eq_sub_div (by omega) hle]
        exact WSteps.right _ ((((WSteps.right _ (sub_spec m (q + 1))).left _)).trans
          (ih (m - (q + 1)) (by omega)))
      · rw [if_neg hle, Nat.div_eq_of_lt (by omega)]
        exact .refl _

theorem div_spec (m n : Nat) : WSteps (divT ⬝ encNat m ⬝ encNat n) (encNat (m / n)) :=
  (((ycomb_knot _).left _).left _).trans (div_knot n m)

/-- `rem`'s body after its knot. -/
theorem rem_unfold (m n : Nat) :
    WSteps (knot (remG.close env) ⬝ encNat m ⬝ encNat n)
      (encNat n ⬝ encNat m ⬝ (K ⬝ (ifleT ⬝ encNat n ⬝ encNat m
        ⬝ (knot (remG.close env) ⬝ (subT ⬝ encNat m ⬝ encNat n) ⬝ encNat n) ⬝ encNat m))) :=
  (knot_call2 _ _ _).trans (run (n := 80) (t := remG ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2)
    (u := .var 2 ⬝ₒ .var 1 ⬝ₒ (.K ⬝ₒ (.var 23 ⬝ₒ .var 2 ⬝ₒ .var 1
      ⬝ₒ (.var 0 ⬝ₒ (.var 22 ⬝ₒ .var 1 ⬝ₒ .var 2) ⬝ₒ .var 2) ⬝ₒ .var 1)))
    (by decide) (sig [knot (remG.close env), encNat m, encNat n]))

theorem rem_knot (n : Nat) : ∀ m : Nat,
    WSteps (knot (remG.close env) ⬝ encNat m ⬝ encNat n) (encNat (m % n)) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    refine (rem_unfold m n).trans ?_
    cases n with
    | zero => rw [Nat.mod_zero]; exact zero_elim (encNat m) _
    | succ q =>
      refine (suc_elim q _ _).trans (WSteps.single (.K _ _) |>.trans ((ifle_spec _ _ _ _).trans ?_))
      by_cases hle : q + 1 ≤ m
      · rw [if_pos hle, Nat.mod_eq_sub_mod hle]
        exact ((WSteps.right _ (sub_spec m (q + 1))).left _).trans (ih (m - (q + 1)) (by omega))
      · rw [if_neg hle, Nat.mod_eq_of_lt (by omega)]
        exact .refl _

theorem rem_spec (m n : Nat) : WSteps (remT ⬝ encNat m ⬝ encNat n) (encNat (m % n)) :=
  (((ycomb_knot _).left _).left _).trans (rem_knot n m)

-- ---------------------------------------------------------------------------
-- Lists
-- ---------------------------------------------------------------------------

/-- A Scott list of terms: `[]` is `K`, `x :: r` is `cons x r`. -/
def encList : List Term → Term
  | [] => K
  | x :: r => consT ⬝ x ⬝ encList r

/-- A recursive call of one argument, and of three. -/
theorem knot_call1 (G a : Term) : WSteps (knot G ⬝ a) (G ⬝ knot G ⬝ a) := (knot_unroll G).left a

theorem knot_call3 (G a b c : Term) :
    WSteps (knot G ⬝ a ⬝ b ⬝ c) (G ⬝ knot G ⬝ a ⬝ b ⬝ c) := (knot_call2 G a b).left c

theorem len_knot : ∀ xs : List Term,
    WSteps (knot (lenG.close env0) ⬝ encList xs) (encNat xs.length)
  | [] => (knot_call1 _ _).trans (run (n := 80) (t := lenG ⬝ₒ .var 0 ⬝ₒ .K) (u := .K)
      (by decide) (sig [knot (lenG.close env0)]))
  | x :: r => (knot_call1 _ _).trans ((run (n := 80)
      (t := lenG ⬝ₒ .var 0 ⬝ₒ (consT.toO ⬝ₒ .var 1 ⬝ₒ .var 2)) (u := .var 20 ⬝ₒ (.var 0 ⬝ₒ .var 2))
      (by decide) (sig [knot (lenG.close env0), x, encList r])).trans (WSteps.right _ (len_knot r)))

theorem len_spec (xs : List Term) : WSteps (lenT ⬝ encList xs) (encNat xs.length) :=
  ((ycomb_knot _).left _).trans (len_knot xs)

theorem at_knot (d : Term) : ∀ (xs : List Term) (i : Nat),
    WSteps (knot (atG.close env0) ⬝ encList xs ⬝ encNat i ⬝ d) (xs.getD i d)
  | [], i => (knot_call3 _ _ _ _).trans (run (n := 80)
      (t := atG ⬝ₒ .var 0 ⬝ₒ .K ⬝ₒ .var 3 ⬝ₒ .var 4) (u := .var 4)
      (by decide) (sig [knot (atG.close env0), K, K, encNat i, d]))
  | x :: r, 0 => (knot_call3 _ _ _ _).trans (run (n := 80)
      (t := atG ⬝ₒ .var 0 ⬝ₒ (consT.toO ⬝ₒ .var 1 ⬝ₒ .var 2) ⬝ₒ Scott.Zero.toO ⬝ₒ .var 4)
      (u := .var 1) (by decide) (sig [knot (atG.close env0), x, encList r, K, d]))
  | x :: r, q + 1 => (knot_call3 _ _ _ _).trans ((run (n := 80)
      (t := atG ⬝ₒ .var 0 ⬝ₒ (consT.toO ⬝ₒ .var 1 ⬝ₒ .var 2) ⬝ₒ (Scott.Suc.toO ⬝ₒ .var 3)
        ⬝ₒ .var 4)
      (u := .var 0 ⬝ₒ .var 2 ⬝ₒ .var 3 ⬝ₒ .var 4) (by decide)
      (sig [knot (atG.close env0), x, encList r, encNat q, d])).trans (at_knot d r q))

theorem at_spec (xs : List Term) (i : Nat) (d : Term) :
    WSteps (atT ⬝ encList xs ⬝ encNat i ⬝ d) (xs.getD i d) :=
  ((((ycomb_knot _).left _).left _).left _).trans (at_knot d xs i)

theorem app_knot (ys : List Term) : ∀ xs : List Term,
    WSteps (knot (appG.close env0) ⬝ encList xs ⬝ encList ys) (encList (xs ++ ys))
  | [] => (knot_call2 _ _ _).trans (run (n := 80)
      (t := appG ⬝ₒ .var 0 ⬝ₒ .K ⬝ₒ .var 3) (u := .var 3)
      (by decide) (sig [knot (appG.close env0), K, K, encList ys]))
  | x :: r => (knot_call2 _ _ _).trans ((run (n := 80)
      (t := appG ⬝ₒ .var 0 ⬝ₒ (consT.toO ⬝ₒ .var 1 ⬝ₒ .var 2) ⬝ₒ .var 3)
      (u := .var 24 ⬝ₒ .var 1 ⬝ₒ (.var 0 ⬝ₒ .var 2 ⬝ₒ .var 3)) (by decide)
      (sig [knot (appG.close env0), x, encList r, encList ys])).trans
        (WSteps.right _ (app_knot ys r)))

theorem app_spec (xs ys : List Term) : WSteps (appT ⬝ encList xs ⬝ encList ys) (encList (xs ++ ys)) :=
  (((ycomb_knot _).left _).left _).trans (app_knot ys xs)

theorem take_knot : ∀ (xs : List Term) (i : Nat),
    WSteps (knot (takeG.close env0) ⬝ encList xs ⬝ encNat i) (encList (xs.take i))
  | [], 0 => (knot_call2 _ _ _).trans (run (n := 80)
      (t := takeG ⬝ₒ .var 0 ⬝ₒ .K ⬝ₒ Scott.Zero.toO) (u := .K)
      (by decide) (sig [knot (takeG.close env0)]))
  | [], q + 1 => (knot_call2 _ _ _).trans (run (n := 80)
      (t := takeG ⬝ₒ .var 0 ⬝ₒ .K ⬝ₒ (Scott.Suc.toO ⬝ₒ .var 3)) (u := .K)
      (by decide) (sig [knot (takeG.close env0), K, K, encNat q]))
  | x :: r, 0 => (knot_call2 _ _ _).trans (run (n := 80)
      (t := takeG ⬝ₒ .var 0 ⬝ₒ (consT.toO ⬝ₒ .var 1 ⬝ₒ .var 2) ⬝ₒ Scott.Zero.toO) (u := .K)
      (by decide) (sig [knot (takeG.close env0), x, encList r]))
  | x :: r, q + 1 => (knot_call2 _ _ _).trans ((run (n := 80)
      (t := takeG ⬝ₒ .var 0 ⬝ₒ (consT.toO ⬝ₒ .var 1 ⬝ₒ .var 2) ⬝ₒ (Scott.Suc.toO ⬝ₒ .var 3))
      (u := .var 24 ⬝ₒ .var 1 ⬝ₒ (.var 0 ⬝ₒ .var 2 ⬝ₒ .var 3)) (by decide)
      (sig [knot (takeG.close env0), x, encList r, encNat q])).trans
        (WSteps.right _ (take_knot r q)))

theorem take_spec (xs : List Term) (i : Nat) :
    WSteps (takeT ⬝ encList xs ⬝ encNat i) (encList (xs.take i)) :=
  (((ycomb_knot _).left _).left _).trans (take_knot xs i)

theorem drop_knot : ∀ (xs : List Term) (i : Nat),
    WSteps (knot (dropG.close env0) ⬝ encList xs ⬝ encNat i) (encList (xs.drop i))
  | [], 0 => (knot_call2 _ _ _).trans (run (n := 80)
      (t := dropG ⬝ₒ .var 0 ⬝ₒ .K ⬝ₒ Scott.Zero.toO) (u := .K)
      (by decide) (sig [knot (dropG.close env0)]))
  | [], q + 1 => (knot_call2 _ _ _).trans (run (n := 80)
      (t := dropG ⬝ₒ .var 0 ⬝ₒ .K ⬝ₒ (Scott.Suc.toO ⬝ₒ .var 3)) (u := .K)
      (by decide) (sig [knot (dropG.close env0), K, K, encNat q]))
  | x :: r, 0 => (knot_call2 _ _ _).trans
      (((oiter_sound (k := 12)
        (t := dropG ⬝ₒ .var 0 ⬝ₒ (consT.toO ⬝ₒ .var 1 ⬝ₒ .var 2) ⬝ₒ Scott.Zero.toO)
        (u := consT.toO ⬝ₒ .var 1 ⬝ₒ .var 2) (by decide)).weak).close
          (sig [knot (dropG.close env0), x, encList r]))
  | x :: r, q + 1 => (knot_call2 _ _ _).trans ((run (n := 80)
      (t := dropG ⬝ₒ .var 0 ⬝ₒ (consT.toO ⬝ₒ .var 1 ⬝ₒ .var 2) ⬝ₒ (Scott.Suc.toO ⬝ₒ .var 3))
      (u := .var 0 ⬝ₒ .var 2 ⬝ₒ .var 3) (by decide)
      (sig [knot (dropG.close env0), x, encList r, encNat q])).trans (drop_knot r q))

theorem drop_spec (xs : List Term) (i : Nat) :
    WSteps (dropT ⬝ encList xs ⬝ encNat i) (encList (xs.drop i)) :=
  (((ycomb_knot _).left _).left _).trans (drop_knot xs i)

-- ---------------------------------------------------------------------------
-- Bit strings, tries and names
-- ---------------------------------------------------------------------------

/-- Each constructor is lean-ski's compiled constructor of its shape
    (`ctorO fields index count`), the shape `ctor_at` reads in
    `src/reduce.c`. -/
theorem ctors_compiled :
    toTerm (ctorO 0 0 3) = bnT ∧ toTerm (ctorO 1 1 3) = bzT ∧ toTerm (ctorO 1 2 3) = boT ∧
    toTerm (ctorO 1 1 2) = ndtT ∧ toTerm (ctorO 3 0 1) = ndbT ∧ toTerm (ctorO 1 0 2) = idrawT ∧
    toTerm (ctorO 1 1 2) = idT ∧ toTerm (ctorO 2 1 2) = consT ∧ toTerm (ctorO 1 1 2) = Scott.Suc ∧
    toTerm (ctorO 0 0 2) = K ∧ toTerm (ctorO 0 1 2) = K ⬝ I := by decide

/-- A bit-string value one level deep: `Bn`, or `Bz` or `Bo` over any term. -/
inductive BV | n | z (r : Term) | o (r : Term)

def BV.term : BV → Term
  | .n => bnT | .z r => bzT ⬝ r | .o r => boT ⬝ r

/-- What `beq` makes of two such values: `Yes`, `No`, or itself on the rests. -/
def beqOut (R : Term) : BV → BV → Term
  | .n, .n => K
  | .z r, .z s => R ⬝ r ⬝ s
  | .o r, .o s => R ⬝ r ⬝ s
  | _, _ => K ⬝ I

/-- One level of `beq`, over any terms below the first constructor. -/
theorem beq_step (a b : BV) :
    WSteps (knot (beqG.close env0) ⬝ a.term ⬝ b.term) (beqOut (knot (beqG.close env0)) a b) := by
  refine (knot_call2 _ _ _).trans ?_
  cases a <;> cases b
  all_goals first
    | exact run (n := 80) (t := beqG ⬝ₒ .var 0 ⬝ₒ bnT.toO ⬝ₒ bnT.toO) (u := .K) (by decide)
        (sig [knot (beqG.close env0)])
    | exact run (n := 80) (t := beqG ⬝ₒ .var 0 ⬝ₒ (bzT.toO ⬝ₒ .var 1) ⬝ₒ (bzT.toO ⬝ₒ .var 2))
        (u := .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2) (by decide) (sig [knot (beqG.close env0), _, _])
    | exact run (n := 80) (t := beqG ⬝ₒ .var 0 ⬝ₒ (boT.toO ⬝ₒ .var 1) ⬝ₒ (boT.toO ⬝ₒ .var 2))
        (u := .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2) (by decide) (sig [knot (beqG.close env0), _, _])
    | exact run (n := 80) (t := beqG ⬝ₒ .var 0 ⬝ₒ bnT.toO ⬝ₒ (bzT.toO ⬝ₒ .var 2))
        (u := .K ⬝ₒ .I) (by decide) (sig [knot (beqG.close env0), K, _])
    | exact run (n := 80) (t := beqG ⬝ₒ .var 0 ⬝ₒ bnT.toO ⬝ₒ (boT.toO ⬝ₒ .var 2))
        (u := .K ⬝ₒ .I) (by decide) (sig [knot (beqG.close env0), K, _])
    | exact run (n := 80) (t := beqG ⬝ₒ .var 0 ⬝ₒ (bzT.toO ⬝ₒ .var 1) ⬝ₒ bnT.toO)
        (u := .K ⬝ₒ .I) (by decide) (sig [knot (beqG.close env0), _])
    | exact run (n := 80) (t := beqG ⬝ₒ .var 0 ⬝ₒ (boT.toO ⬝ₒ .var 1) ⬝ₒ bnT.toO)
        (u := .K ⬝ₒ .I) (by decide) (sig [knot (beqG.close env0), _])
    | exact run (n := 80) (t := beqG ⬝ₒ .var 0 ⬝ₒ (bzT.toO ⬝ₒ .var 1) ⬝ₒ (boT.toO ⬝ₒ .var 2))
        (u := .K ⬝ₒ .I) (by decide) (sig [knot (beqG.close env0), _, _])
    | exact run (n := 80) (t := beqG ⬝ₒ .var 0 ⬝ₒ (boT.toO ⬝ₒ .var 1) ⬝ₒ (bzT.toO ⬝ₒ .var 2))
        (u := .K ⬝ₒ .I) (by decide) (sig [knot (beqG.close env0), _, _])

/-- A bit string, least significant bit first: `false` is `Bz`, `true` is `Bo`. -/
def encBits : List Bool → Term
  | [] => bnT
  | false :: r => bzT ⬝ encBits r
  | true :: r => boT ⬝ encBits r

def BV.ofBits : List Bool → BV
  | [] => .n
  | false :: r => .z (encBits r)
  | true :: r => .o (encBits r)

theorem BV.ofBits_term : ∀ bs, (BV.ofBits bs).term = encBits bs
  | [] => rfl
  | false :: _ => rfl
  | true :: _ => rfl

theorem beq_knot : ∀ a b : List Bool,
    WSteps (knot (beqG.close env0) ⬝ encBits a ⬝ encBits b) (Compose.boolT (a == b)) := by
  intro a b
  have h := beq_step (BV.ofBits a) (BV.ofBits b)
  rw [BV.ofBits_term, BV.ofBits_term] at h
  refine h.trans ?_
  match a, b with
  | [], [] => exact .refl _
  | [], false :: _ => exact .refl _ | [], true :: _ => exact .refl _
  | false :: _, [] => exact .refl _ | true :: _, [] => exact .refl _
  | false :: a, false :: b => simpa [beqOut, BV.ofBits] using beq_knot a b
  | true :: a, true :: b => simpa [beqOut, BV.ofBits] using beq_knot a b
  | false :: _, true :: _ => exact .refl _ | true :: _, false :: _ => exact .refl _

theorem beq_spec (a b : List Bool) : WSteps (beqT ⬝ encBits a ⬝ encBits b) (Compose.boolT (a == b)) :=
  (((ycomb_knot _).left _).left _).trans (beq_knot a b)

/-- A trie one level deep: `Nd0`, or `NdT (NdB v z o)` over any terms. -/
inductive TV | nd0 | node (v z o : Term)

def TV.term : TV → Term
  | .nd0 => K | .node v z o => ndtT ⬝ (ndbT ⬝ v ⬝ z ⬝ o)

/-- What `bget` makes of a key and a trie: `No`, the value, or itself on the
    key's rest and the branch the bit names. -/
def bgetOut (R k : Term) : Option BV → TV → Term
  | _, .nd0 => K ⬝ I
  | some .n, .node v _ _ => v
  | some (.z r), .node _ z _ => R ⬝ r ⬝ z
  | some (.o r), .node _ _ o => R ⬝ r ⬝ o
  | none, .node _ _ _ => R ⬝ k   -- not reached: the key is a value at a node

/-- One level of `bget`: at `Nd0` whatever the key, at a node over a key one
    level deep. -/
theorem bget_nd0 (k : Term) : WSteps (knot (bgetG.close env0) ⬝ k ⬝ K) (K ⬝ I) :=
  (knot_call2 _ _ _).trans (run (n := 80) (t := bgetG ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ .K) (u := .K ⬝ₒ .I)
    (by decide) (sig [knot (bgetG.close env0), k]))

theorem bget_step (a : BV) (v z o : Term) :
    WSteps (knot (bgetG.close env0) ⬝ a.term ⬝ (TV.node v z o).term)
      (bgetOut (knot (bgetG.close env0)) a.term (some a) (.node v z o)) := by
  refine (knot_call2 _ _ _).trans ?_
  cases a
  · exact run (n := 80)
      (t := bgetG ⬝ₒ .var 0 ⬝ₒ bnT.toO ⬝ₒ (ndtT.toO ⬝ₒ (ndbT.toO ⬝ₒ .var 3 ⬝ₒ .var 4 ⬝ₒ .var 5)))
      (u := .var 3) (by decide) (sig [knot (bgetG.close env0), K, K, v, z, o])
  · exact run (n := 80)
      (t := bgetG ⬝ₒ .var 0 ⬝ₒ (bzT.toO ⬝ₒ .var 1)
        ⬝ₒ (ndtT.toO ⬝ₒ (ndbT.toO ⬝ₒ .var 3 ⬝ₒ .var 4 ⬝ₒ .var 5)))
      (u := .var 0 ⬝ₒ .var 1 ⬝ₒ .var 4) (by decide) (sig [knot (bgetG.close env0), _, K, v, z, o])
  · exact run (n := 80)
      (t := bgetG ⬝ₒ .var 0 ⬝ₒ (boT.toO ⬝ₒ .var 1)
        ⬝ₒ (ndtT.toO ⬝ₒ (ndbT.toO ⬝ₒ .var 3 ⬝ₒ .var 4 ⬝ₒ .var 5)))
      (u := .var 0 ⬝ₒ .var 1 ⬝ₒ .var 5) (by decide) (sig [knot (bgetG.close env0), _, K, v, z, o])

/-- A trie keyed by bit strings, its values terms. -/
inductive Trie | nd0 | node (v : Term) (z o : Trie)

def Trie.enc : Trie → Term
  | .nd0 => K
  | .node v z o => ndtT ⬝ (ndbT ⬝ v ⬝ z.enc ⬝ o.enc)

/-- The lookup: the value at the key, or `No` (`K I`). -/
def Trie.get : List Bool → Trie → Term
  | _, .nd0 => K ⬝ I
  | [], .node v _ _ => v
  | false :: k, .node _ z _ => Trie.get k z
  | true :: k, .node _ _ o => Trie.get k o

theorem bget_knot : ∀ (k : List Bool) (t : Trie),
    WSteps (knot (bgetG.close env0) ⬝ encBits k ⬝ t.enc) (t.get k)
  | [], .nd0 => bget_nd0 _
  | false :: _, .nd0 => bget_nd0 _
  | true :: _, .nd0 => bget_nd0 _
  | [], .node v z o => bget_step .n v z.enc o.enc
  | false :: k, .node v z o => (bget_step (.z (encBits k)) v z.enc o.enc).trans (bget_knot k z)
  | true :: k, .node v z o => (bget_step (.o (encBits k)) v z.enc o.enc).trans (bget_knot k o)

theorem bget_spec (k : List Bool) (t : Trie) : WSteps (bgetT ⬝ encBits k ⬝ t.enc) (t.get k) :=
  (((ycomb_knot _).left _).left _).trans (bget_knot k t)

/-- A name: `IdRaw n` over any term, whose bits are `Bn`, or `Id b`. -/
inductive NV | raw (n : Term) | id (b : Term)

def NV.term : NV → Term
  | .raw n => idrawT ⬝ n | .id b => idT ⬝ b

def NV.bits : NV → Term
  | .raw _ => bnT | .id b => b

/-- `ideq` compares the names' bits with `beq`. -/
theorem ideq_step (x y : NV) : WSteps (ideqT ⬝ x.term ⬝ y.term) (beqT ⬝ x.bits ⬝ y.bits) := by
  cases x <;> cases y
  · exact run (n := 80) (t := ideqO ⬝ₒ (idrawT.toO ⬝ₒ .var 1) ⬝ₒ (idrawT.toO ⬝ₒ .var 2))
      (u := .var 25 ⬝ₒ bnT.toO ⬝ₒ bnT.toO) (by decide) (sig [K, _, _])
  · exact run (n := 80) (t := ideqO ⬝ₒ (idrawT.toO ⬝ₒ .var 1) ⬝ₒ (idT.toO ⬝ₒ .var 2))
      (u := .var 25 ⬝ₒ bnT.toO ⬝ₒ .var 2) (by decide) (sig [K, _, _])
  · exact run (n := 80) (t := ideqO ⬝ₒ (idT.toO ⬝ₒ .var 1) ⬝ₒ (idrawT.toO ⬝ₒ .var 2))
      (u := .var 25 ⬝ₒ .var 1 ⬝ₒ bnT.toO) (by decide) (sig [K, _, _])
  · exact run (n := 80) (t := ideqO ⬝ₒ (idT.toO ⬝ₒ .var 1) ⬝ₒ (idT.toO ⬝ₒ .var 2))
      (u := .var 25 ⬝ₒ .var 1 ⬝ₒ .var 2) (by decide) (sig [K, _, _])

/-- Names as data: `IdRaw n`, its bits `[]`, or `Id bs`. -/
inductive Name | raw (n : Term) | id (bs : List Bool)

def Name.view : Name → NV
  | .raw n => .raw n | .id bs => .id (encBits bs)

def Name.bits : Name → List Bool
  | .raw _ => [] | .id bs => bs

theorem ideq_spec (x y : Name) :
    WSteps (ideqT ⬝ x.view.term ⬝ y.view.term) (Compose.boolT (x.bits == y.bits)) := by
  refine (ideq_step _ _).trans ?_
  have hx : x.view.bits = encBits x.bits := by cases x <;> rfl
  have hy : y.view.bits = encBits y.bits := by cases y <;> rfl
  rw [hx, hy]; exact beq_spec _ _

-- ---------------------------------------------------------------------------
-- The C: word_fire's values
-- ---------------------------------------------------------------------------

/-- The numeral operations, in `AV_WOP_*` order. -/
inductive Op | add | sub | mul | ifeq | ifle | div | rem
  deriving DecidableEq, Repr

def Op.term : Op → Term
  | .add => addT | .sub => subT | .mul => mulT | .ifeq => ifeqT | .ifle => ifleT
  | .div => divT | .rem => remT

/-- What `word_fire` leaves: a word of a value, or its third (`true`) or
    fourth operand. -/
inductive Out | num (v : Nat) | arg (third : Bool)

/-- `AV_WORD_MAX` and `WORD_BUILD_MAX`. -/
def wordMax : UInt64 := 2 ^ 27 - 1
def buildMax : UInt64 := 2 ^ 20

/-- `word_fire` (`src/reduce.c`) over its operands' word values `m` and
    `n`, line for line: `v` and `need` in `uint64_t`, the decline when
    either is over its bound, and the loops that build the result as
    `word_succ` and `word_pred` change a word's value, by one.  `none` is
    the decline: the term runs instead. -/
def vneed (op : Op) (m n : UInt32) : UInt64 × UInt64 :=
  match op with
  | .add => (m.toUInt64 + n.toUInt64, 2 * n.toUInt64)
  | .mul => (m.toUInt64 * n.toUInt64, 2 * (m.toUInt64 * n.toUInt64))
  | .div => let v := if n ≠ 0 then m.toUInt64 / n.toUInt64 else 0; (v, 2 * v)
  | .rem => let v := if n ≠ 0 then m.toUInt64 % n.toUInt64 else m.toUInt64; (v, 2 * v)
  | _ => (0, 0)

def build (op : Op) (m n : UInt32) (v : UInt64) : Out :=
  match op with
  | .add => .num (Nat.repeat (· + 1) n.toNat m.toNat)
  | .sub => .num (Nat.repeat (fun x => if x = 0 then 0 else x - 1) n.toNat m.toNat)
  | .mul | .div | .rem => .num (Nat.repeat (· + 1) v.toNat 0)
  | .ifeq => .arg (m == n)
  | .ifle => .arg (m ≤ n)

def fireC (op : Op) (m n : UInt32) : Option Out :=
  if (vneed op m n).1 > wordMax ∨ (vneed op m n).2 > buildMax then none
  else some (build op m n (vneed op m n).1)

theorem repeat_succ (k : Nat) : ∀ x, Nat.repeat (· + 1) k x = x + k := by
  induction k with
  | zero => intro x; rfl
  | succ k ih => intro x; simp only [Nat.repeat, ih]; omega

theorem repeat_pred (k : Nat) : ∀ x, Nat.repeat (fun x => if x = 0 then 0 else x - 1) k x = x - k := by
  induction k with
  | zero => intro x; rfl
  | succ k ih => intro x; simp only [Nat.repeat, ih]; split <;> omega

/-- **The C computes the operation**: when `word_fire` leaves a word, the
    operation's term reduces to that word's numeral. -/
theorem fireC_num {op : Op} {m n : UInt32} {v : Nat} (h : fireC op m n = some (.num v)) :
    WSteps (op.term ⬝ encNat m.toNat ⬝ encNat n.toNat) (encNat v) := by
  have hm := m.toNat_lt
  have hn := n.toNat_lt
  unfold fireC at h
  split at h
  · cases h
  cases op <;> simp only [build, vneed, Option.some.injEq, Out.num.injEq, reduceCtorEq] at h <;> subst h
  · rw [repeat_succ]; exact add_spec _ _
  · rw [repeat_pred]; exact sub_spec _ _
  · have e : (m.toUInt64 * n.toUInt64).toNat = m.toNat * n.toNat := by
      rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
      exact Nat.mod_eq_of_lt (by
        have := Nat.mul_lt_mul'' hm hn
        simpa using this)
    rw [repeat_succ, e, Nat.zero_add]; exact mul_spec _ _
  · by_cases hz : n = 0
    · subst hz; simp only [ne_eq, not_true_eq_false, if_false, repeat_succ]
      simpa [Op.term] using div_spec m.toNat 0
    · rw [if_pos hz, repeat_succ, UInt64.toNat_div, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64,
        Nat.zero_add]
      exact div_spec _ _
  · by_cases hz : n = 0
    · subst hz; simp only [ne_eq, not_true_eq_false, if_false, repeat_succ, Nat.zero_add,
        UInt32.toNat_toUInt64]
      simpa [Op.term] using rem_spec m.toNat 0
    · rw [if_pos hz, repeat_succ, UInt64.toNat_mod, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64,
        Nat.zero_add]
      exact rem_spec _ _

/-- **The C chooses the operand the term does.** -/
theorem fireC_arg {op : Op} {m n : UInt32} {t : Bool} (h : fireC op m n = some (.arg t)) (a b : Term) :
    WSteps (op.term ⬝ encNat m.toNat ⬝ encNat n.toNat ⬝ a ⬝ b) (if t then a else b) := by
  unfold fireC at h
  split at h
  · cases h
  cases op <;> simp only [build, Option.some.injEq, Out.arg.injEq, reduceCtorEq] at h <;> subst h
  · have := ifeq_spec m.toNat n.toNat a b
    simpa [Op.term, UInt32.toNat_inj] using this
  · have := ifle_spec m.toNat n.toNat a b
    simpa [Op.term, UInt32.le_iff_toNat_le] using this

-- ---------------------------------------------------------------------------
-- The C: list_fire's results
-- ---------------------------------------------------------------------------

/-- The list operations, in `AV_WOP_*` order. -/
inductive LOp | len | at | app | take | drop
  deriving DecidableEq, Repr

/-- The redex: the operation over the list `xs` and, as it takes them, the
    index `i` and default `d`, or the second list `ys`. -/
def LOp.redex (xs : List Term) (i : Nat) (ys : List Term) (d : Term) : LOp → Term
  | .len => lenT ⬝ encList xs
  | .at => atT ⬝ encList xs ⬝ encNat i ⬝ d
  | .app => appT ⬝ encList xs ⬝ encList ys
  | .take => takeT ⬝ encList xs ⬝ encNat i
  | .drop => dropT ⬝ encList xs ⬝ encNat i

/-- `list_prefix`: the first `m` cells of `src`, rebuilt before `tail`. -/
def listPrefix : Nat → List Term → List Term → List Term
  | 0, _, tail => tail
  | m + 1, x :: r, tail => x :: listPrefix m r tail
  | _ + 1, [], tail => tail

/-- `list_fire` (`src/reduce.c`) over the list `xs` (its length `n`, the
    word's), the index `i` (a word value), the second list `ys` and the
    default `d`, line for line: `m`, `need`, the declines, then the result
    each operation leaves.  `at` and `drop` walk `m` rests; `take` and `app`
    rebuild a prefix.  Every quantity here is below `2^34`, so the C's
    `uint32_t` and `uint64_t` arithmetic is exact and Lean's `Nat` is it. -/
def listNeed (op : LOp) (xs : List Term) (i : Nat) (ys : List Term) : Nat :=
  let n := xs.length
  let m := if i < n then i else n
  match op with
  | .len => 2 * n
  | .take => if m < n then 3 * m else 0
  | .app => if n ≠ 0 ∧ ys.length ≠ 0 then 3 * n else 0
  | _ => 0

def listResult (op : LOp) (xs : List Term) (i : Nat) (ys : List Term) (d : Term) : Term :=
  let n := xs.length
  let m := if i < n then i else n
  match op with
  | .len => encNat (Nat.repeat (· + 1) n 0)
  | .at => if i < n then (Nat.repeat List.tail m xs).headD d else d
  | .drop => encList (Nat.repeat List.tail m xs)
  | .take => if m = n then encList xs else encList (listPrefix m xs [])
  | .app => if n = 0 then encList ys else if ys.length = 0 then encList xs
            else encList (listPrefix n xs ys)

def listFireC (op : LOp) (xs : List Term) (i : Nat) (ys : List Term) (d : Term) : Option Term :=
  if (op = .app ∧ xs.length + ys.length > 2 ^ 27 - 1) ∨ listNeed op xs i ys > 2 ^ 20 then none
  else some (listResult op xs i ys d)

theorem repeat_tail (xs : List Term) : ∀ m, Nat.repeat List.tail m xs = xs.drop m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => simp only [Nat.repeat, ih, List.tail_drop]

theorem listPrefix_eq : ∀ (m : Nat) (xs tail : List Term), m ≤ xs.length →
    listPrefix m xs tail = xs.take m ++ tail
  | 0, _, _, _ => rfl
  | m + 1, x :: r, tail, h => by
    simp only [listPrefix, List.take_succ_cons, List.cons_append]
    rw [listPrefix_eq m r tail (by simp at h; omega)]
  | _ + 1, [], _, h => by simp at h

/-- **The C computes the list operations**: whatever `list_fire` leaves,
    the operation's term reduces to it. -/
theorem listFireC_sound {op : LOp} {xs : List Term} {i : Nat} {ys : List Term} {d t : Term}
    (h : listFireC op xs i ys d = some t) : WSteps (LOp.redex xs i ys d op) t := by
  unfold listFireC at h
  split at h
  · cases h
  simp only [Option.some.injEq] at h
  subst h
  cases op <;> simp only [listResult]
  · rw [repeat_succ, Nat.zero_add]; exact len_spec xs
  · simp only [LOp.redex]
    refine (at_spec xs i d).trans ?_
    split
    · rename_i hi
      have e : (xs.drop i).headD d = xs.getD i d := by
        simp [List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]
      rw [repeat_tail, e]; exact .refl _
    · rename_i hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; exact .refl _
  · simp only [LOp.redex]
    refine (app_spec xs ys).trans ?_
    split
    · rename_i h0; rw [List.length_eq_zero_iff.mp h0]; exact .refl _
    split
    · rename_i _ h0; rw [List.length_eq_zero_iff.mp h0, List.append_nil]; exact .refl _
    · rw [listPrefix_eq _ _ _ (Nat.le_refl _), List.take_length]; exact .refl _
  · simp only [LOp.redex]
    refine (take_spec xs i).trans ?_
    split
    · rename_i hi
      rw [if_neg (by omega), listPrefix_eq _ _ _ (by omega), List.append_nil]; exact .refl _
    · rename_i hi
      rw [if_pos rfl, List.take_of_length_le (by omega)]; exact .refl _
  · simp only [LOp.redex]
    refine (drop_spec xs i).trans ?_
    rw [repeat_tail]
    split
    · exact .refl _
    · rename_i hi; rw [List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)]
      exact .refl _

-- ---------------------------------------------------------------------------
-- The C: bits_walk
-- ---------------------------------------------------------------------------

/-- What `ctor_at` reads of a node, one level deep: a bit string's
    constructor, a trie's, a name's.  `none` is not a value yet. -/
inductive Bit (α : Type) | n | z (r : α) | o (r : α)
inductive Tri (α : Type) | nd0 | node (v z o : α)
inductive Nam (α : Type) | raw (n : α) | id (b : α)

/-- The reducer's view of its nodes: each node's meaning, and what
    `bit_at`, the trie reading and the name reading make of it. -/
structure View (α : Type) where
  mean : α → Term
  bit : α → Option (Bit α)
  tri : α → Option (Tri α)
  nam : α → Option (Nam α)

/-- The view is right: a node read as a constructor over fields means that
    constructor over the fields' meanings.  This is the glue `ctor_at`
    stands for: a constructor template's node applied to its fields, or
    `K`, `K I`; `ctors_compiled` ties each shape to its term. -/
structure View.OK {α : Type} (V : View α) : Prop where
  bit_n : ∀ x, V.bit x = some .n → V.mean x = bnT
  bit_z : ∀ x r, V.bit x = some (.z r) → V.mean x = bzT ⬝ V.mean r
  bit_o : ∀ x r, V.bit x = some (.o r) → V.mean x = boT ⬝ V.mean r
  tri_0 : ∀ x, V.tri x = some .nd0 → V.mean x = K
  tri_node : ∀ x v z o, V.tri x = some (.node v z o) →
    V.mean x = ndtT ⬝ (ndbT ⬝ V.mean v ⬝ V.mean z ⬝ V.mean o)
  nam_raw : ∀ x n, V.nam x = some (.raw n) → V.mean x = idrawT ⬝ V.mean n
  nam_id : ∀ x b, V.nam x = some (.id b) → V.mean x = idT ⬝ V.mean b

/-- `bits_walk`'s outcomes: `BITS_TO` `K` (`yes`) or a value node,
    `BITS_KI` (`no`), `BITS_AGAIN` on two nodes, `BITS_DECLINE`. -/
inductive BOut (α : Type) | yes | no | val (x : α) | again (p q : α) | decline

/-- `BITS_LEVELS`. -/
def bitsLevels : Nat := 4096

/-- `bits_walk` for `beq`: `k` levels left, `first` at level 0. -/
def beqWalk {α : Type} (V : View α) : Nat → Bool → α → α → BOut α
  | 0, _, p, q => .again p q
  | k + 1, first, p, q =>
    match V.bit p, V.bit q with
    | some .n, some .n => .yes
    | some (.z r), some (.z s) => beqWalk V k false r s
    | some (.o r), some (.o s) => beqWalk V k false r s
    | some _, some _ => .no
    | _, _ => if first then .decline else .again p q

/-- `bits_walk` for `bget`: the trie, then its node, then the key. -/
def bgetWalk {α : Type} (V : View α) : Nat → Bool → α → α → BOut α
  | 0, _, p, q => .again p q
  | k + 1, first, p, q =>
    match V.tri q with
    | some .nd0 => .no
    | some (.node v z o) =>
      match V.bit p with
      | some .n => .val v
      | some (.z r) => bgetWalk V k false r z
      | some (.o r) => bgetWalk V k false r o
      | none => if first then .decline else .again p q
    | none => if first then .decline else .again p q

/-- `ideq`'s reading of a name's bits: `none` is an `IdRaw`'s `Bn`. -/
def readB {α : Type} (V : View α) : Option α → Option (Bit α)
  | none => some .n
  | some b => V.bit b

/-- `bits_walk` for `ideq`'s bits, both names read. -/
def ideqBits {α : Type} (V : View α) : Nat → Option α → Option α → BOut α
  | 0, _, _ => .decline
  | k + 1, bx, by_ =>
    match readB V bx, readB V by_ with
    | some .n, some .n => .yes
    | some (.z r), some (.z s) => ideqBits V k (some r) (some s)
    | some (.o r), some (.o s) => ideqBits V k (some r) (some s)
    | some _, some _ => .no
    | _, _ => .decline

/-- A name's bits as `ideq` reads them. -/
def namBits {α : Type} : Nam α → Option α
  | .raw _ => none
  | .id b => some b

/-- `bits_walk` for `ideq`: both names, then their bits; decided here or
    declined. -/
def ideqWalk {α : Type} (V : View α) (p q : α) : BOut α :=
  match V.nam p, V.nam q with
  | some x, some y => ideqBits V bitsLevels (namBits x) (namBits y)
  | _, _ => .decline

/-- What an outcome claims of a redex `t` over the knot `R`. -/
def BOut.Claim {α : Type} (V : View α) (R t : Term) : BOut α → Prop
  | .yes => WSteps t K
  | .no => WSteps t (K ⬝ I)
  | .val x => WSteps t (V.mean x)
  | .again p q => WSteps t (R ⬝ V.mean p ⬝ V.mean q)
  | .decline => True

theorem BOut.Claim.pre {α : Type} {V : View α} {R t u : Term} {o : BOut α}
    (h : WSteps t u) (c : o.Claim V R u) : o.Claim V R t := by
  cases o <;> simp only [BOut.Claim] at c ⊢ <;> first | trivial | exact h.trans c

/-- A bit one level deep, its fields' meanings. -/
def Bit.bv {α : Type} (V : View α) : Bit α → BV
  | .n => .n | .z r => .z (V.mean r) | .o r => .o (V.mean r)

theorem bit_view {α : Type} {V : View α} (hV : V.OK) {x : α} {b : Bit α} (h : V.bit x = some b) :
    V.mean x = (b.bv V).term := by
  cases b
  · exact hV.bit_n x h
  · exact hV.bit_z x _ h
  · exact hV.bit_o x _ h

/-- One level of the walk over two bits read: `Yes`, `No`, or the knot on. -/
theorem beq_level {α : Type} {V : View α} (a b : Bit α) :
    WSteps (knot (beqG.close env0) ⬝ (a.bv V).term ⬝ (b.bv V).term)
      (beqOut (knot (beqG.close env0)) (a.bv V) (b.bv V)) := beq_step _ _

/-- Every outcome of the `beq` walk holds of its knot. -/
theorem beqWalk_sound {α : Type} {V : View α} (hV : V.OK) : ∀ (k : Nat) (first : Bool) (p q : α),
    (beqWalk V k first p q).Claim V (knot (beqG.close env0))
      (knot (beqG.close env0) ⬝ V.mean p ⬝ V.mean q)
  | 0, _, p, q => .refl _
  | k + 1, first, p, q => by
    cases h1 : V.bit p with
    | none => cases first <;> simp only [beqWalk, h1, BOut.Claim] <;> first | trivial | exact .refl _
    | some a =>
      cases h2 : V.bit q with
      | none => cases first <;> simp only [beqWalk, h1, h2, BOut.Claim] <;> first | trivial | exact .refl _
      | some b =>
        have st := beq_level (V := V) a b
        rw [← bit_view hV h1, ← bit_view hV h2] at st
        cases a <;> cases b <;> simp only [beqWalk, h1, h2, Bit.bv, beqOut, BOut.Claim] at st ⊢
        all_goals first | exact st | exact BOut.Claim.pre st (beqWalk_sound hV k false _ _)

/-- Every outcome of the `bget` walk holds of its knot. -/
theorem bgetWalk_sound {α : Type} {V : View α} (hV : V.OK) : ∀ (k : Nat) (first : Bool) (p q : α),
    (bgetWalk V k first p q).Claim V (knot (bgetG.close env0))
      (knot (bgetG.close env0) ⬝ V.mean p ⬝ V.mean q)
  | 0, _, p, q => .refl _
  | k + 1, first, p, q => by
    cases h1 : V.tri q with
    | none => cases first <;> simp only [bgetWalk, h1, BOut.Claim] <;> first | trivial | exact .refl _
    | some t =>
      cases t with
      | nd0 =>
        simp only [bgetWalk, h1, BOut.Claim]; rw [hV.tri_0 q h1]; exact bget_nd0 _
      | node v z o =>
        cases h2 : V.bit p with
        | none =>
          cases first <;> simp only [bgetWalk, h1, h2, BOut.Claim] <;> first | trivial | exact .refl _
        | some b =>
          have st := bget_step (b.bv V) (V.mean v) (V.mean z) (V.mean o)
          rw [← bit_view hV h2] at st
          simp only [TV.term] at st
          rw [← hV.tri_node q v z o h1] at st
          cases b <;> simp only [bgetWalk, h1, h2, Bit.bv, bgetOut, BOut.Claim] at st ⊢
          all_goals first | exact st | exact BOut.Claim.pre st (bgetWalk_sound hV k false _ _)

/-- The meaning of `ideq`'s bits: `Bn` for an `IdRaw`. -/
def bitsMean {α : Type} (V : View α) : Option α → Term
  | none => bnT
  | some b => V.mean b

theorem readB_view {α : Type} {V : View α} (hV : V.OK) {bx : Option α} {b : Bit α}
    (h : readB V bx = some b) : bitsMean V bx = (b.bv V).term := by
  cases bx with
  | none => simp only [readB, Option.some.injEq] at h; subst h; rfl
  | some x => exact bit_view hV h

theorem ideqBits_sound {α : Type} {V : View α} (hV : V.OK) : ∀ (k : Nat) (bx by_ : Option α),
    (ideqBits V k bx by_).Claim V K
      (knot (beqG.close env0) ⬝ bitsMean V bx ⬝ bitsMean V by_)
  | 0, _, _ => trivial
  | k + 1, bx, by_ => by
    cases h1 : readB V bx with
    | none => simp only [ideqBits, h1, BOut.Claim]
    | some a =>
      cases h2 : readB V by_ with
      | none => simp only [ideqBits, h1, h2, BOut.Claim]
      | some b =>
        have st := beq_level (V := V) a b
        rw [← readB_view hV h1, ← readB_view hV h2] at st
        cases a <;> cases b <;> simp only [ideqBits, h1, h2, Bit.bv, beqOut, BOut.Claim] at st ⊢
        all_goals first
          | exact st
          | exact BOut.Claim.pre st (ideqBits_sound hV k (some _) (some _))

/-- Two terms with a common reduct: convertible, so they share every
    normal form (lean-ski's `church_rosser`). -/
def Join (t u : Term) : Prop := ∃ w, WSteps t w ∧ WSteps u w

/-- What a fire leaves, claimed of the operation's redex `t`: the
    answer's reduct, or, for `BITS_AGAIN`, the operation `op` over the
    nodes reached, convertible with `t`. -/
def BOut.Fire {α : Type} (V : View α) (op t : Term) : BOut α → Prop
  | .yes => WSteps t K
  | .no => WSteps t (K ⬝ I)
  | .val x => WSteps t (V.mean x)
  | .again p q => Join t (op ⬝ V.mean p ⬝ V.mean q)
  | .decline => True

/-- **The C walks the bit-string operations soundly.**  At `beq`'s and
    `bget`'s redexes `BITS_TO` and `BITS_KI` are reducts, and `BITS_AGAIN`,
    the operation over the nodes the walk reached, is convertible with the
    redex: both reduce to the knot over those nodes.  It is not a reduct,
    since `Ycomb ⬝ G` and its knot are convertible only. -/
theorem beq_fire {α : Type} {V : View α} (hV : V.OK) (p q : α) :
    (beqWalk V bitsLevels true p q).Fire V beqT (beqT ⬝ V.mean p ⬝ V.mean q) := by
  have c := BOut.Claim.pre (((ycomb_knot (beqG.close env0)).left (V.mean p)).left (V.mean q))
    (beqWalk_sound hV bitsLevels true p q)
  generalize beqWalk V bitsLevels true p q = w at c ⊢
  cases w <;> simp only [BOut.Claim, BOut.Fire] at c ⊢
  all_goals first | exact c | trivial | exact ⟨_, c, ((ycomb_knot _).left _).left _⟩

theorem bget_fire {α : Type} {V : View α} (hV : V.OK) (p q : α) :
    (bgetWalk V bitsLevels true p q).Fire V bgetT (bgetT ⬝ V.mean p ⬝ V.mean q) := by
  have c := BOut.Claim.pre (((ycomb_knot (bgetG.close env0)).left (V.mean p)).left (V.mean q))
    (bgetWalk_sound hV bitsLevels true p q)
  generalize bgetWalk V bitsLevels true p q = w at c ⊢
  cases w <;> simp only [BOut.Claim, BOut.Fire] at c ⊢
  all_goals first | exact c | trivial | exact ⟨_, c, ((ycomb_knot _).left _).left _⟩

/-- `ideq` is decided or declined: `BITS_TO` `K` and `BITS_KI` are reducts,
    and it never leaves itself on. -/
theorem ideq_fire {α : Type} {V : View α} (hV : V.OK) (p q : α) :
    (ideqWalk V p q).Fire V ideqT (ideqT ⬝ V.mean p ⬝ V.mean q) ∧
      ∀ p' q', ideqWalk V p q ≠ .again p' q' := by
  unfold ideqWalk
  cases hx : V.nam p with
  | none => simp [BOut.Fire]
  | some x =>
    cases hy : V.nam q with
    | none => simp [BOut.Fire]
    | some y =>
      simp only
      have nv : ∀ (z : α) (w : Nam α), V.nam z = some w →
          ∃ v : NV, V.mean z = v.term ∧ v.bits = bitsMean V (namBits w) := by
        intro z w h
        cases w with
        | raw n => exact ⟨.raw (V.mean n), hV.nam_raw z n h, rfl⟩
        | id b => exact ⟨.id (V.mean b), hV.nam_id z b h, rfl⟩
      obtain ⟨vx, ex, bx⟩ := nv p x hx
      obtain ⟨vy, ey, by_⟩ := nv q y hy
      have h0 : WSteps (ideqT ⬝ V.mean p ⬝ V.mean q)
          (knot (beqG.close env0) ⬝ bitsMean V (namBits x) ⬝ bitsMean V (namBits y)) := by
        rw [ex, ey, ← bx, ← by_]; exact (ideq_step vx vy).trans (((ycomb_knot _).left _).left _)
      have c := BOut.Claim.pre h0 (ideqBits_sound hV bitsLevels _ _)
      have na : ∀ k bx by_, ∀ p' q', ideqBits V k bx by_ ≠ .again p' q' := by
        intro k
        induction k with
        | zero => intro _ _ _ _; simp [ideqBits]
        | succ k ih =>
          intro bx by_ p' q'
          simp only [ideqBits]
          split <;> first | exact ih _ _ _ _ | simp
      refine ⟨?_, na _ _ _⟩
      generalize hw : ideqBits V bitsLevels (namBits x) (namBits y) = w at c ⊢
      cases w <;> simp only [BOut.Claim, BOut.Fire] at c ⊢
      all_goals first | exact c | trivial | exact absurd hw (na _ _ _ _ _)

-- ---------------------------------------------------------------------------
-- The printer
-- ---------------------------------------------------------------------------

/-- Avon's printed form: application to the left, an application argument
    in parentheses. -/
def pr : Term → String
  | .S => "S" | .K => "K" | .I => "I"
  | .app f x => pr f ++ " " ++ (match x with | .app _ _ => "(" ++ pr x ++ ")" | _ => pr x)

/-- A C string literal over lines of at most `w` characters. -/
def chunks (w : Nat) (cs : List Char) : List String :=
  match cs with
  | [] => []
  | c :: rest => String.ofList ((c :: rest).take w) :: chunks w (rest.drop (w - 1))
termination_by cs.length
decreasing_by simp; omega

def pin (name : String) (t : Term) : String :=
  s!"#define AV_PIN_{name} \\\n" ++
    String.intercalate " \\\n" ((chunks 72 (pr t).toList).map fun c => s!"    \"{c}\"") ++ "\n\n"

def header : String :=
  "/*  The word operations' pinned terms and the constructors they read,\n" ++
  " *  printed by lean/Words.lean, which proves each operation computes its\n" ++
  " *  function on every input (AvonWords.add_spec .. rem_spec, len_spec ..\n" ++
  " *  drop_spec, beq_spec, bget_spec, ideq_spec) and the C's fires sound\n" ++
  " *  (fireC_num, fireC_arg, listFireC_sound, beq_fire, bget_fire,\n" ++
  " *  ideq_fire).  Generated; do not edit. */\n\n" ++
  pin "ADD" addT ++ pin "SUB" subT ++ pin "MUL" mulT ++ pin "IFEQ" ifeqT ++
  pin "IFLE" ifleT ++ pin "DIV" divT ++ pin "REM" remT ++
  pin "LEN" lenT ++ pin "AT" atT ++ pin "APP" appT ++ pin "TAKE" takeT ++ pin "DROP" dropT ++
  pin "BEQ" beqT ++ pin "BGET" bgetT ++ pin "IDEQ" ideqT ++
  pin "SUC" Scott.Suc ++ pin "CONS" consT ++ pin "BN" bnT ++ pin "BZ" bzT ++ pin "BO" boT ++
  pin "NDT" ndtT ++ pin "NDB" ndbT ++ pin "IDRAW" idrawT ++ pin "ID" idT

end AvonWords

#print axioms AvonWords.fireC_num
#print axioms AvonWords.fireC_arg
#print axioms AvonWords.listFireC_sound
#print axioms AvonWords.beq_fire
#print axioms AvonWords.bget_fire
#print axioms AvonWords.ideq_fire
#print axioms AvonWords.ideq_spec
#print axioms AvonWords.bget_spec
#print axioms AvonWords.ctors_compiled

def main (args : List String) : IO UInt32 := do
  match args with
  | [out] => IO.FS.writeFile out AvonWords.header; return 0
  | _ => IO.eprintln "usage: lake env lean --run Words.lean OUT.h"; return 1
