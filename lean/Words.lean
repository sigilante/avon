import Ski.BitArith
import Ski.Words
import Ski.Compile

/-!
# Avon's numeral words, proved, and their pins printed

Share mode runs seven numeral operations natively on words (`--data`,
`docs/DESIGN.md` §6.10): a node whose function is an operation's pinned
term, node for node, applied to two words, is replaced by the result.
This file proves both halves of that replacement and prints the pins.

* **The terms compute the operations.**  For every `m` and `n`, with
  `encNat` lean-ski's Scott numeral (`Zero = K`, `Suc`, Avon's
  `SUC_TEXT`), `add_spec` .. `rem_spec`: `op ⬝ ⌜m⌝ ⬝ ⌜n⌝ ↠ ⌜m op n⌝` by
  weak reduction, `sub` truncating at 0, `m / 0 = 0` and `m % 0 = m` as
  skijack's are; `ifeq_spec` and `ifle_spec` choose their third or fourth
  argument.
* **The C computes them** (`fireC_num`, `fireC_arg`).  `fireC` is
  `word_fire`'s arithmetic in `src/reduce.c`, line for line: `v` and
  `need` in `uint64_t` from two `uint32_t` word values, the decline over
  `AV_WORD_MAX` or `WORD_BUILD_MAX`, and the loops that build the result,
  each `word_succ` adding one to a word's value and each `word_pred`
  taking one.  Whenever it leaves a word, the term reduces to that word's
  numeral; whenever it leaves an operand, the term reduces to it.
* **The pins are Lean's.**  `header` prints `src/word_pins.h`, the seven
  terms `src/words.c` matches, so the terms proved are the terms matched.

**The method** is `Ski/BitArith.lean`'s.  Each pin is `Ycomb ⬝ G`, and
`Ycomb ⬝ G` reduces to a knot `R` with `R ↠ G ⬝ R` (`ycomb_knot`,
`knot_unroll`).  One unfolding of `G`, with the knot, the operands'
predecessors and the chosen arguments as variables, is a symbolic run the
kernel checks (`wnf`, `run`).  The `Suc` that `G` builds is variable 20,
and the operations a generator inlines, `add` in `mul` and `ifle` and
`sub` in `div` and `rem`, are variables 21 to 23, so a run stops at them
and their own theorems take over.  Induction on the recursed operand
closes the variables; `div` and `rem` take strong induction on `m`.

**What stays trusted:** that `fireC` is `word_fire`'s arithmetic (read it
beside `src/reduce.c`), the printer `pr`, and the reducer's glue: the
match, `av_numeral`'s reading of a word, `word_succ` and `word_pred`, and
the write of the result.  The theorems are about values; a jet's count is
not the term's (`docs/DESIGN.md` §6.5).

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

/-- The environment of the generators' named subterms: `Suc` only. -/
def env0 : Nat → Term := fun i => if i = 20 then Scott.Suc else K

def addT : Term := Ycomb ⬝ addG.close env0
def subT : Term := Ycomb ⬝ subG.close env0
def ifleT : Term := Ycomb ⬝ ifleG.close env0

/-- The environment with the operations other generators inline. -/
def env : Nat → Term := fun i =>
  if i = 20 then Scott.Suc else if i = 21 then addT else if i = 22 then subT
  else if i = 23 then ifleT else K

def mulT : Term := Ycomb ⬝ mulG.close env
def ifeqT : Term := Ycomb ⬝ ifeqG.close env
def divT : Term := Ycomb ⬝ divG.close env
def remT : Term := Ycomb ⬝ remG.close env

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
  "/*  The numeral operations' pinned terms, printed by lean/Words.lean, which\n" ++
  " *  proves each reduces to its operation's numeral on every input\n" ++
  " *  (AvonWords.add_spec .. rem_spec) and word_fire's values those numerals\n" ++
  " *  (AvonWords.fireC_num, fireC_arg).  Generated; do not edit. */\n\n" ++
  pin "ADD" addT ++ pin "SUB" subT ++ pin "MUL" mulT ++ pin "IFEQ" ifeqT ++
  pin "IFLE" ifleT ++ pin "DIV" divT ++ pin "REM" remT

end AvonWords

#print axioms AvonWords.fireC_num
#print axioms AvonWords.fireC_arg

def main (args : List String) : IO UInt32 := do
  match args with
  | [out] => IO.FS.writeFile out AvonWords.header; return 0
  | _ => IO.eprintln "usage: lake env lean --run Words.lean OUT.h"; return 1
