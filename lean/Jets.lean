import Ski.Weak
import Ski.Compile

/-!
# Jets together: a jetted head run is never longer than the plain one

Each of Avon's jets is proved alone (`docs/LEAN-JETS.md` §2): its fire
leaves a term the redex weakly reduces to, or one convertible with it.
This file proves what a run gains or keeps when jets fire in it.

**A jet whose fire is head-first keeps the head run's end, in no more
steps.**  Call a fire head-first if the redex reaches the fire's result by
a head contraction followed by weak steps (`HeadFirst`).  A run of head
steps and head-first fires, from a term that reaches a weak head normal
form in `n` head steps, has at most `n` steps (`jrun_le`): a weak reduct
of a term normalizes in no more head steps than the term, and in strictly
fewer after a head step (lean-ski's `par_step_le`; `StepsN.wtail_lt`, from
lean-ski's `Ski/Converse.lean`, restated here so this file needs only
`Ski.Weak`).  So the jetted run ends, and where it ends in a weak head
normal form, that form is a weak reduct of the plain run's
(`jrun_whnf`).  This is Hindley and Seldin's quasi-leftmost-reduction
theorem (*Lambda-Calculus and Combinators*, 2008, Theorem 3.22), for head
runs, with a bound.

**Which fires are head-first.**  A pin `Ycomb ⬝ G` with its arguments
head-contracts at `Ycomb`'s `S`, and two more steps reach `G`'s knot
(`ycomb_head`), so every theorem proved through the knot, as each word,
list and bit-string operation's in `lean/Words.lean` and `whnfF`'s in
`lean/Interp.lean`, gives a head-first fire (`head_of_knot`); those files
state each.  `--fix`'s rewrite with Curry's Y and a bit-string fire's
`BITS_AGAIN` are not reducts, so not head-first.

Run from lean-ski: `cd ~/Code/ski/lean-ski && lake env lean
~/avon/lean/Jets.lean`.
-/

open Term

namespace AvonJets

-- ---------------------------------------------------------------------------
-- Counted head runs (lean-ski's `Ski/Converse.lean`)
-- ---------------------------------------------------------------------------

inductive StepsN : Nat → Term → Term → Prop
  | refl (t : Term) : StepsN 0 t t
  | step {n : Nat} {t t' u : Term} (h : Step t t') (hs : StepsN n t' u) : StepsN (n + 1) t u

theorem StepsN.steps {n : Nat} {t u : Term} (h : StepsN n t u) : Steps t u := by
  induction h with
  | refl t => exact .refl t
  | step h _ ih => exact .step h ih

theorem StepsN.after_step {t t' w : Term} {n : Nat} (s : Step t t') (hw : StepsN n t w)
    (ww : Whnf w) : ∃ m, n = m + 1 ∧ StepsN m t' w := by
  cases hw with
  | refl _ => exact (ww.no_step s).elim
  | step s' hw' =>
    have e := Step.det s' s
    subst e
    exact ⟨_, rfl, hw'⟩

theorem StepsN.par {t u w : Term} {n : Nat} (hp : Par t u) (hw : StepsN n t w) (ww : Whnf w) :
    ∃ m w', m ≤ n ∧ StepsN m u w' ∧ Whnf w' := by
  induction hw generalizing u with
  | refl t => exact ⟨0, u, Nat.le_refl 0, .refl u, hp.whnf ww⟩
  | step s _ ih =>
    cases par_step_le s hp with
    | intro u1 h =>
      cases ih h.2 ww with
      | intro m h' =>
        cases h' with
        | intro w' h' =>
          cases h.1 with
          | inl e => exact ⟨m, w', Nat.le_succ_of_le h'.1, e ▸ h'.2⟩
          | inr s' => exact ⟨m + 1, w', Nat.succ_le_succ h'.1, .step s' h'.2.1, h'.2.2⟩

/-- A weak reduct normalizes in no more head steps. -/
theorem StepsN.wtail {t u w : Term} {n : Nat} (h : WSteps t u) (hw : StepsN n t w) (ww : Whnf w) :
    ∃ m w', m ≤ n ∧ StepsN m u w' ∧ Whnf w' := by
  induction h generalizing n w with
  | refl _ => exact ⟨n, w, Nat.le_refl n, hw, ww⟩
  | step s _ ih =>
    cases StepsN.par s.par hw ww with
    | intro m h1 =>
      cases h1 with
      | intro w1 h1 =>
        cases ih h1.2.1 h1.2.2 with
        | intro m' h2 =>
          cases h2 with
          | intro w2 h2 => exact ⟨m', w2, Nat.le_trans h2.1 h1.1, h2.2⟩

/-- After a head step, a weak reduct normalizes in strictly fewer. -/
theorem StepsN.wtail_lt {t t1 u w : Term} {n : Nat} (s : Step t t1) (h : WSteps t1 u)
    (hw : StepsN n t w) (ww : Whnf w) : ∃ m w', m < n ∧ StepsN m u w' ∧ Whnf w' := by
  cases StepsN.after_step s hw ww with
  | intro m hm =>
    cases StepsN.wtail h hm.2 ww with
    | intro m' h' =>
      cases h' with
      | intro w' h' =>
        rw [hm.1]
        exact ⟨m', w', Nat.lt_succ_of_le h'.1, h'.2⟩

-- ---------------------------------------------------------------------------
-- Head-first fires, and runs of them
-- ---------------------------------------------------------------------------

/-- A fire from `t` to `u` is head-first if a head step of `t`, then weak
    steps, reach `u`.  A head step is one (no weak steps after it). -/
def HeadFirst (t u : Term) : Prop := ∃ t1, Step t t1 ∧ WSteps t1 u

theorem HeadFirst.ofStep {t u : Term} (s : Step t u) : HeadFirst t u := ⟨u, s, .refl u⟩

theorem HeadFirst.wsteps {t u : Term} (h : HeadFirst t u) : WSteps t u := by
  obtain ⟨_, s, hs⟩ := h
  exact .step s.weak hs

/-- A head run with jets, of `k` steps: each a head step or a head-first
    fire. -/
inductive JRunN : Nat → Term → Term → Prop
  | refl (t : Term) : JRunN 0 t t
  | step {k : Nat} {t t' u : Term} (h : HeadFirst t t') (hs : JRunN k t' u) : JRunN (k + 1) t u

theorem JRunN.wsteps {k : Nat} {t u : Term} (h : JRunN k t u) : WSteps t u := by
  induction h with
  | refl t => exact .refl t
  | step h _ ih => exact h.wsteps.trans ih

/-- **A jetted head run is never longer than the plain one.**  If `t`
    reaches a weak head normal form in `n` head steps, every run of head
    steps and head-first fires from `t` has at most `n` steps; so it ends.
    (Hindley and Seldin, Theorem 3.22, for head runs, with a bound.) -/
theorem jrun_le {k n : Nat} {t u w : Term} (h : JRunN k t u) (hw : StepsN n t w)
    (ww : Whnf w) : k ≤ n := by
  induction h generalizing n w with
  | refl _ => exact Nat.zero_le n
  | step hf _ ih =>
    obtain ⟨t1, s, ht1⟩ := hf
    obtain ⟨m, w', hm, hw', ww'⟩ := StepsN.wtail_lt s ht1 hw ww
    exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (ih hw' ww') hm)

/-- **Where it ends, it ends at a reduct of the plain run's end.**  If a
    jetted head run from `t` reaches a weak head normal form `u`, then `t`
    reaches a weak head normal form by head steps alone, and `u` is a weak
    reduct of it. -/
theorem jrun_whnf {k : Nat} {t u : Term} (h : JRunN k t u) (hu : Whnf u) :
    ∃ w, Eval t w ∧ WSteps w u :=
  eval_back h.wsteps ⟨.refl u, hu⟩

-- ---------------------------------------------------------------------------
-- Which fires are head-first: pins over Curry's Y
-- ---------------------------------------------------------------------------

/-- A term applied to arguments, first first. -/
def apps (f : Term) : List Term → Term
  | [] => f
  | a :: as => apps (f ⬝ a) as

theorem Step.apps {f f' : Term} : ∀ (as : List Term), Step f f' → Step (apps f as) (apps f' as)
  | [], s => s
  | a :: as, s => Step.apps as (.left a s)

theorem WSteps.apps {f f' : Term} : ∀ (as : List Term), WSteps f f' → WSteps (apps f as) (apps f' as)
  | [], s => s
  | a :: as, s => WSteps.apps as (s.left a)

def knotX (G : Term) : Term := S ⬝ (S ⬝ (K ⬝ S) ⬝ K) ⬝ (K ⬝ (S ⬝ I ⬝ I)) ⬝ G
def knot (G : Term) : Term := knotX G ⬝ knotX G

/-- **`Ycomb ⬝ G` head-contracts, and three weak steps reach its knot.**
    `Ycomb` is `S A B`, so `Ycomb ⬝ G` is a head redex; it contracts to
    `A ⬝ G ⬝ (B ⬝ G)`, and `A = K (S I I)`, `B ⬝ G = knotX G`. -/
theorem ycomb_head (G : Term) :
    Step (Ycomb ⬝ G) (K ⬝ (S ⬝ I ⬝ I) ⬝ G ⬝ knotX G) ∧
    WSteps (K ⬝ (S ⬝ I ⬝ I) ⬝ G ⬝ knotX G) (knot G) :=
  ⟨.S _ _ _,
   .step (.left _ (.K _ _)) (.step (.S _ _ _) (.step (.left _ (.I _)) (.single (.right _ (.I _)))))⟩

/-- **A pin over Curry's Y fires head-first** whenever its theorem is
    proved through the knot: the head step is `Ycomb`'s `S`. -/
theorem head_of_knot {G r : Term} (as : List Term) (h : WSteps (apps (knot G) as) r) :
    HeadFirst (apps (Ycomb ⬝ G) as) r :=
  ⟨_, Step.apps as (ycomb_head G).1, (WSteps.apps as (ycomb_head G).2).trans h⟩

end AvonJets

#print axioms AvonJets.jrun_le
#print axioms AvonJets.jrun_whnf
#print axioms AvonJets.head_of_knot
