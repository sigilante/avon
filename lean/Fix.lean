import Ski.Simulation

/-!
# Y unfolded in one step (`--fix`), proved

With `--fix`, share mode rewrites `Y g` to `g (Y g)` in one step, Y
being Curry's `S (K (S I I)) (S (S (K S) K) (K (S I I)))`
(`docs/DESIGN.md` §6.11).  The rewrite is not a reduction: `Y g`
reduces to the knot `X X`, `X = S (S (K S) K) (K (S I I)) g`, and so does
`g (Y g)` up to `g`, but neither reduces to the other.  This file proves
what the rewrite keeps, in two parts (`docs/LEAN-JETS.md` §7).

**A. Any term.**  `XSteps` is a run mixing weak steps and the rewrite at
any position, in any order.  Every term it reaches has a common reduct
with its start (`fix_join`, from lean-ski's `church_rosser`), so a
normal form `--fix` reaches is the one the plain run reaches
(`fix_normal`).  This licenses `--fix` in share mode, for every term.

**B. Compiled programs, Y a jet.**  Lean-ski's `simulation` says every
source step of a compiled program is matched by weak steps through `Tr`;
its recursive calls unroll `Ycomb` by S, K and I.  Here Y is a jet: an
open term's variable 0, a constant with the one rule `Y g` to `g (Y g)`,
which a weak step never looks inside (`JStep`).  A source binder `x` is
variable `x + 1`, so no binder is ever Y.  `compJ` is lean-ski's compiler
(`comp`, `compLam`, `wrapLift`, `FEqn.compile`) with each recursive
equation's `Ycomb` the jet, and `TrJ` is lean-ski's `Tr` over it.

- `simulationJ`: every source step is matched by steps of the run with
  the jet; a recursive call is the jet's one step, then the body's
  instance.
- `fixed_of_fixedJ`, `tr_of_trJ`: read back, Y as `Ycomb` (`rbT`), the
  jet program is lean-ski's compiled program (`Fixed`) and every jet
  state is a compiled form of its source state by lean-ski's own `Tr`.
- `fix_simulation`: the two together.
- `sum_fixedJ`, `loop_fixedJ`: lean-ski's compiled `sum` and `loop`
  programs, each `Ycomb` the jet (`jetify`), are what the jet compiler
  gives, decided by the kernel; each has four recursive equations
  (`sum_loop_recursive`), and reading back gives lean-ski's own
  environment (`genvR_genvJOf`).  So `sum_fix_simulation` is Y's
  simulation for `sum` up to lean-ski's `Tr` over `genvOf sumText`.

**Why Y is a jet here, and not every `Ycomb` tree.**  Avon finds Y by
tree identity, so a program whose compiled code happens to spell Y, such
as the closure `λx. S I I (S (K x) (S I I))`, which compiles to `Ycomb`
exactly (`closure_spells_Y`), is rewritten too.  Applied to `N`, the
source takes a β-step that lean-ski's simulation matches by S-reducing
that very redex; a run that never S-reduces Y rewrites it to `N (Y N)`
instead, so that simulation does not carry over.  Part A still covers
that program: the two are convertible.  Part B marks Y where the compiler
ties recursion, as a witness would mark Y's addresses.

**What stays trusted:** that Avon's rewrite is `JStep.fix` and
`FixStep.fix` (`src/reduce.c`: the redex root becomes `App(g, y)`, `y` a
fresh `App(Y, g)`); `--memory`'s sharing, which keeps the same terms
under one node; and the reducer's strategy, which picks one run of the
many these theorems allow.  The theorems are about values and source
states; a step count is not the plain run's (`docs/DESIGN.md` §6.5).

Run from lean-ski: `cd ~/Code/ski/lean-ski && lake env lean ~/avon/lean/Fix.lean`.
The kernel checks every theorem as the file elaborates.
-/

open Term Front

set_option linter.unusedSectionVars false

namespace AvonFix

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

-- ---------------------------------------------------------------------------
-- A: any term, the rewrite mixed with weak steps
-- ---------------------------------------------------------------------------

/-- `--fix`'s rewrite, `Y g` to `g (Y g)`, at any position. -/
inductive FixStep : Term → Term → Prop
  | fix (g : Term) : FixStep (Ycomb ⬝ g) (g ⬝ (Ycomb ⬝ g))
  | left {f f' : Term} (x : Term) : FixStep f f' → FixStep (f ⬝ x) (f' ⬝ x)
  | right (f : Term) {x x' : Term} : FixStep x x' → FixStep (f ⬝ x) (f ⬝ x')

/-- A step of a run with `--fix`: a weak step or the rewrite, in any order. -/
inductive XStep : Term → Term → Prop
  | weak {t u : Term} : WStep t u → XStep t u
  | fix {t u : Term} : FixStep t u → XStep t u

inductive XSteps : Term → Term → Prop
  | refl (t : Term) : XSteps t t
  | step {t t' u : Term} : XStep t t' → XSteps t' u → XSteps t u

/-- The rewrite is a conversion: both sides reduce to `g` over the knot. -/
theorem fixStep_join {t u : Term} (h : FixStep t u) : ∃ w, WSteps t w ∧ WSteps u w := by
  induction h with
  | fix g =>
    exact ⟨g ⬝ knot g, (ycomb_knot g).trans (knot_unroll g), WSteps.right g (ycomb_knot g)⟩
  | left x _ ih =>
    obtain ⟨w, h1, h2⟩ := ih
    exact ⟨w ⬝ x, h1.left x, h2.left x⟩
  | right f _ ih =>
    obtain ⟨w, h1, h2⟩ := ih
    exact ⟨f ⬝ w, WSteps.right f h1, WSteps.right f h2⟩

/-- **A run with `--fix` stays convertible with the plain one.**  Whatever
    a run mixing weak steps and the rewrite reaches, the plain run from
    the same term reduces to a common reduct of it (by lean-ski's
    `church_rosser`). -/
theorem fix_join {t u : Term} (h : XSteps t u) : ∃ w, WSteps t w ∧ WSteps u w := by
  induction h with
  | refl t => exact ⟨t, .refl t, .refl t⟩
  | @step t t1 u s _ ih =>
    obtain ⟨w2, h12, hu2⟩ := ih
    obtain ⟨w1, h01, h11⟩ : ∃ w, WSteps t w ∧ WSteps t1 w := by
      cases s with
      | weak s => exact ⟨t1, .single s, .refl t1⟩
      | fix s => exact fixStep_join s
    obtain ⟨w3, h13, h23⟩ := church_rosser h11 h12
    exact ⟨w3, h01.trans h13, hu2.trans h23⟩

/-- **A normal form `--fix` reaches is SKI's.**  If a run with the rewrite
    reaches a term no weak step applies to, the plain run reaches that
    same term. -/
theorem fix_normal {t n : Term} (h : XSteps t n) (hn : ∀ u, ¬ WStep n u) : WSteps t n := by
  obtain ⟨w, htw, hnw⟩ := fix_join h
  cases hnw with
  | refl => exact htw
  | step s _ => exact absurd s (hn _)

/-- Why B takes Y as a jet: the closure `λx. S I I (S (K x) (S I I))`
    compiles, by lean-ski's abstraction, to `Ycomb` exactly, so a finder
    of Y by tree identity rewrites it too. -/
theorem closure_spells_Y :
    abs 0 ((S ⬝ I ⬝ I).toO ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .var 0) ⬝ₒ (S ⬝ I ⬝ I).toO)) = Ycomb.toO := by
  decide

-- ---------------------------------------------------------------------------
-- B: the simulation, Y a jet
-- ---------------------------------------------------------------------------

/-! Terms with the jet: open terms whose variable 0 is Y, a constant with
one rule, `Y g` to `g (Y g)`, and no other.  A source binder `x` is
variable `x + 1`, so no binder is ever Y.  The compiler below is
lean-ski's (`comp`, `compLam`, `wrapLift`, `FEqn.compile`), its globals
resolved to these terms and a recursive equation's `Ycomb` the jet. -/

/-- The jet. -/
def Yv : OTerm := .var 0

/-- A source binder's variable. -/
def bv (x : Nat) : Nat := x + 1

/-- Every variable a jet term may hold is Y: it is closed but for the jet. -/
def YClosed (t : OTerm) : Prop := ∀ i ∈ t.vars, i = 0

/-- `wrapLift` over source binders. -/
def wrapLiftJ (caps ps : List Nat) (body : OTerm) : OTerm :=
  wrapLift (caps.map bv) (ps.map bv) body

mutual
  /-- `comp ∘ resolve`, the globals jet terms. -/
  def compJ (genvJ : Nm → OTerm) (scope : List Nat) : CSrc → OTerm
    | .glob n => genvJ n
    | .var x => .var (bv x)
    | .app f a => compJ genvJ scope f ⬝ₒ compJ genvJ scope a
    | .lam x b => compLamJ genvJ (scope.filter fun s => (CSrc.lam x b).occurs s) [x] b
  /-- `compLam ∘ resolve`. -/
  def compLamJ (genvJ : Nm → OTerm) (caps ps : List Nat) : CSrc → OTerm
    | .lam y b => compLamJ genvJ caps (ps ++ [y]) b
    | .glob n => wrapLiftJ caps ps (genvJ n)
    | .var x => wrapLiftJ caps ps (.var (bv x))
    | .app f a => wrapLiftJ caps ps (compJ genvJ (caps ++ ps) f ⬝ₒ compJ genvJ (caps ++ ps) a)
end

theorem compLamJ_chain (genvJ : Nm → OTerm) : ∀ (e : CSrc) (caps ps : List Nat),
    compLamJ genvJ caps ps e =
      wrapLiftJ caps (ps ++ e.peel.1) (compJ genvJ (caps ++ (ps ++ e.peel.1)) e.peel.2)
  | .glob _, caps, ps => by
    show wrapLiftJ caps ps _ = wrapLiftJ caps (ps ++ []) (compJ genvJ (caps ++ (ps ++ [])) _)
    rw [List.append_nil]; rfl
  | .var _, caps, ps => by
    show wrapLiftJ caps ps _ = wrapLiftJ caps (ps ++ []) (compJ genvJ (caps ++ (ps ++ [])) _)
    rw [List.append_nil]; rfl
  | .app _ _, caps, ps => by
    show wrapLiftJ caps ps _ = wrapLiftJ caps (ps ++ []) (compJ genvJ (caps ++ (ps ++ [])) _)
    rw [List.append_nil]; rfl
  | .lam y b, caps, ps => by
    show compLamJ genvJ caps (ps ++ [y]) b = _
    rw [compLamJ_chain genvJ b caps (ps ++ [y])]
    show wrapLiftJ caps (ps ++ [y] ++ b.peel.1) (compJ genvJ (caps ++ (ps ++ [y] ++ b.peel.1)) b.peel.2) =
      wrapLiftJ caps (ps ++ (y :: b.peel.1)) (compJ genvJ (caps ++ (ps ++ (y :: b.peel.1))) b.peel.2)
    rw [List.append_assoc]; rfl

/-- Unbound variables are junk, `K`, as `toTerm` closes them; Y stays. -/
def junkY : Nat → OTerm := fun i => if i = 0 then Yv else .K

/-- **The compiled program, the jet at each recursion**: `FEqn.compile`,
    with `Ycomb` the jet; every global's term closed but for it. -/
def FixedJ (P : Nm → Option GDef) (genvJ : Nm → OTerm) : Prop :=
  (∀ n a j m, P n = some (.ctor a j m) → genvJ n = (toTerm (ctorO a j m)).toO) ∧
  (∀ n ps b, P n = some (.eqn ⟨ps, none, b⟩) →
    genvJ n = (absN (ps.map bv) (compJ genvJ ps b)).subst junkY) ∧
  (∀ n s ps b, P n = some (.eqn ⟨ps, some s, b⟩) →
    genvJ n = Yv ⬝ₒ (absN ((s :: ps).map bv) (compJ genvJ (s :: ps) b)).subst junkY) ∧
  (∀ n, YClosed (genvJ n))

/-- **A run with the jet**: weak steps, which never look inside Y, and Y's
    rule. -/
inductive JStep : OTerm → OTerm → Prop
  | weak {t u : OTerm} : OWStep t u → JStep t u
  | fix (g : OTerm) : JStep (Yv ⬝ₒ g) (g ⬝ₒ (Yv ⬝ₒ g))
  | left {f f' : OTerm} (x : OTerm) : JStep f f' → JStep (f ⬝ₒ x) (f' ⬝ₒ x)
  | right (f : OTerm) {x x' : OTerm} : JStep x x' → JStep (f ⬝ₒ x) (f ⬝ₒ x')

inductive JSteps : OTerm → OTerm → Prop
  | refl (t : OTerm) : JSteps t t
  | step {t t' u : OTerm} : JStep t t' → JSteps t' u → JSteps t u

theorem JSteps.trans {t u v : OTerm} (h₁ : JSteps t u) (h₂ : JSteps u v) : JSteps t v := by
  induction h₁ with
  | refl _ => exact h₂
  | step h _ ih => exact .step h (ih h₂)

theorem JSteps.of_weak {t u : OTerm} (h : OWSteps t u) : JSteps t u := by
  induction h with
  | refl t => exact .refl t
  | step h _ ih => exact .step (.weak h) ih

theorem JSteps.left {f f' : OTerm} (x : OTerm) (h : JSteps f f') : JSteps (f ⬝ₒ x) (f' ⬝ₒ x) := by
  induction h with
  | refl _ => exact .refl _
  | step h _ ih => exact .step (.left x h) ih

theorem JSteps.right (f : OTerm) {x x' : OTerm} (h : JSteps x x') : JSteps (f ⬝ₒ x) (f ⬝ₒ x') := by
  induction h with
  | refl _ => exact .refl _
  | step h _ ih => exact .step (.right f h) ih

theorem JSteps.appL {t u : OTerm} (h : JSteps t u) : ∀ as, JSteps (appL t as) (appL u as)
  | [] => h
  | a :: as => JSteps.appL (JSteps.left a h) as

/-- **`t` is a compiled form of `c`, Y a jet**: lean-ski's `Tr`, its
    closures' environments over source binders, with no `self` case: the
    jet's unfolding is `Y ⬝ F` itself, the global's own term. -/
inductive TrJ (genvJ : Nm → OTerm) (P : Nm → Option GDef) : Cl → OTerm → Prop
  | const (t : Term) : TrJ genvJ P (.const t) t.toO
  | gref (n : Nm) : TrJ genvJ P (.gref n) (genvJ n)
  | clo {caps ps : List Nat} {b : CSrc} {ρ : Nat → Cl} {γ : Nat → OTerm} :
      (∀ i, TrJ genvJ P (ρ i) (γ (bv i))) → γ 0 = Yv →
      TrJ genvJ P (.clo caps ps b ρ) ((wrapLiftJ caps ps (compJ genvJ (caps ++ ps) b)).subst γ)
  | app {f a : Cl} {t u : OTerm} : TrJ genvJ P f t → TrJ genvJ P a u → TrJ genvJ P (.app f a) (t ⬝ₒ u)

section
variable {genvJ : Nm → OTerm} {P : Nm → Option GDef}

theorem TrJ.apps {f : Cl} {t : OTerm} (hf : TrJ genvJ P f t) :
    ∀ {as : List Cl} {ts : List OTerm}, All2 (TrJ genvJ P) as ts → TrJ genvJ P (f.apps as) (appL t ts)
  | _, _, .nil => hf
  | _, _, .cons r h => TrJ.apps (TrJ.app hf r) h

theorem TrJ.apps_inv : ∀ {as : List Cl} {f : Cl} {t : OTerm}, TrJ genvJ P (f.apps as) t →
    ∃ tf ts, t = appL tf ts ∧ TrJ genvJ P f tf ∧ All2 (TrJ genvJ P) as ts
  | [], _, _, h => ⟨_, [], rfl, h, .nil⟩
  | a :: as, f, t, h =>
    match TrJ.apps_inv (as := as) h with
    | ⟨tfa, ts, e, hfa, hs⟩ => by
      cases hfa with
      | app hf ha => exact ⟨_, _ :: ts, e, hf, .cons ha hs⟩

theorem TrJ.override {ρ : Nat → Cl} {γ : Nat → OTerm} (h : ∀ i, TrJ genvJ P (ρ i) (γ (bv i))) :
    ∀ {xs : List Nat} {as : List Cl} {ts : List OTerm}, All2 (TrJ genvJ P) as ts →
      ∀ i, TrJ genvJ P (overrideCl ρ xs as i) (override γ (xs.map bv) ts (bv i))
  | [], _, _, .nil, i => h i
  | [], _, _, .cons _ _, i => h i
  | _ :: _, _, _, .nil, i => h i
  | x :: xs, _, _, .cons r hs, i =>
    TrJ.override (ρ := updCl ρ x _) (γ := upd γ (bv x) _)
      (fun y => by
        unfold updCl upd
        by_cases e : y = x
        · rw [if_pos e, if_pos (by rw [e])]; exact r
        · rw [if_neg e, if_neg (by unfold bv; omega)]; exact h y) hs i

theorem override_zero (γ : Nat → OTerm) :
    ∀ (xs : List Nat) (ts : List OTerm), override γ (xs.map bv) ts 0 = γ 0
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, t :: ts => by
    show override (upd γ (bv x) t) (xs.map bv) ts 0 = γ 0
    rw [override_zero (upd γ (bv x) t) xs ts, upd, if_neg (by unfold bv; omega)]

theorem subst_yclosed {t : OTerm} (h : YClosed t) {γ : Nat → OTerm} (h0 : γ 0 = Yv) :
    t.subst γ = t := by
  rw [show t.subst γ = t.subst OTerm.var from
    subst_agree fun i hi => by
      rw [h i ((OTerm.mem_vars i t).1 (OTerm.mem_of_occ hi))]; exact h0]
  exact subst_var t

/-- **Compiling commutes with instantiating**, Y a jet. -/
theorem trJ_inst (hY : ∀ n, YClosed (genvJ n)) {ρ : Nat → Cl} {γ : Nat → OTerm}
    (h : ∀ i, TrJ genvJ P (ρ i) (γ (bv i))) (h0 : γ 0 = Yv) :
    ∀ (sc : List Nat) (e : CSrc), TrJ genvJ P (inst sc ρ e) ((compJ genvJ sc e).subst γ)
  | _, .glob n => by
    show TrJ genvJ P (.gref n) ((genvJ n).subst γ)
    rw [subst_yclosed (hY n) h0]
    exact .gref n
  | _, .var x => h x
  | sc, .app f a => .app (trJ_inst hY h h0 sc f) (trJ_inst hY h h0 sc a)
  | sc, .lam x b => by
    show TrJ genvJ P (.clo _ _ _ ρ) ((compLamJ genvJ _ [x] b).subst γ)
    rw [compLamJ_chain]
    exact .clo h h0

/-- `override` with each formal's own value changes nothing. -/
theorem override_self (γ : Nat → OTerm) : ∀ xs : List Nat, override γ xs (xs.map γ) = γ
  | [] => rfl
  | x :: xs => by
    show override (upd γ x (γ x)) xs (xs.map γ) = γ
    rw [show upd γ x (γ x) = γ from funext fun y => by
      unfold upd; by_cases e : y = x
      · rw [if_pos e, e]
      · rw [if_neg e]]
    exact override_self γ xs

/-- A lifted combinator applied to its parameters, open. -/
theorem wrapLiftJ_beta (caps ps : List Nat) (B : OTerm) (γ : Nat → OTerm) (ts : List OTerm)
    (hl : ts.length = ps.length) :
    OWSteps (appL ((wrapLiftJ caps ps B).subst γ) ts) (B.subst (override γ (ps.map bv) ts)) := by
  have e1 : (wrapLiftJ caps ps B).subst γ =
      appL ((absN (caps.map bv ++ ps.map bv) B).subst γ) ((caps.map bv).map γ) := by
    unfold wrapLiftJ wrapLift
    rw [subst_appL, List.map_map]
    rfl
  have h := absN_beta_subst (caps.map bv ++ ps.map bv) B γ ((caps.map bv).map γ ++ ts)
    (by simp [hl])
  rw [override_append γ (caps.map bv) (ps.map bv) ((caps.map bv).map γ) ts (by simp),
    override_self] at h
  rw [e1, ← appL_append]
  exact h

end

theorem override_range (γ F : Nat → OTerm) : ∀ L,
    override γ (List.range L) ((List.range L).map F) = fun y => if y < L then F y else γ y
  | 0 => funext fun y => (if_neg (Nat.not_lt_zero y)).symm
  | L + 1 => by
    have e : List.range (L + 1) = List.range L ++ [L] := List.range_succ
    rw [e, List.map_append, override_append γ _ _ _ _ (List.length_map _), override_range γ F L]
    funext y
    show (if y = L then F L else if y < L then F y else γ y) = if y < L + 1 then F y else γ y
    by_cases h1 : y = L
    · rw [if_pos h1, if_pos (by omega), h1]
    · by_cases h2 : y < L
      · rw [if_neg h1, if_pos h2, if_pos (by omega)]
      · rw [if_neg h1, if_neg h2, if_neg (by omega)]

/-- **A Scott constructor selects**, open: the constructor at position `j`
    of `m` with `a` fields, applied to its fields and `m` continuations,
    weakly reduces to continuation `j` applied to the fields. -/
theorem ctorO_beta {a j m : Nat} (hj : j < m) {fs ks : List OTerm}
    (hf : fs.length = a) (hk : ks.length = m) :
    OWSteps (appL (ctorO a j m) (fs ++ ks)) (appL (ks.getD j .K) fs) := by
  have hl : (fs ++ ks).length = a + m := by rw [List.length_append, hf, hk]
  have h := absN_beta_subst (List.range (a + m)) (appL (.var (a + j)) ((List.range a).map .var))
    OTerm.var (fs ++ ks) (by rw [hl, List.length_range])
  rw [subst_var] at h
  have e : fs ++ ks = (List.range (a + m)).map (fun i => (fs ++ ks).getD i .K) := by
    have := map_getD_range OTerm.K (fs ++ ks)
    rw [hl] at this
    exact this.symm
  rw [e, override_range, subst_appL, List.map_map] at h
  rw [← e] at h
  have e1 : (OTerm.var (a + j)).subst
      (fun y => if y < a + m then (fs ++ ks).getD y .K else OTerm.var y) = ks.getD j .K := by
    show (if a + j < a + m then (fs ++ ks).getD (a + j) .K else OTerm.var (a + j)) = ks.getD j .K
    rw [if_pos (by omega), ← hf]
    exact getD_app_right OTerm.K fs ks j
  have e2 : (List.range a).map
      (OTerm.subst (fun y => if y < a + m then (fs ++ ks).getD y .K else OTerm.var y) ∘ OTerm.var) =
        fs := by
    have e3 : (List.range a).map
        (OTerm.subst (fun y => if y < a + m then (fs ++ ks).getD y .K else OTerm.var y) ∘ OTerm.var) =
        (List.range fs.length).map (fun i => fs.getD i .K) := by
      rw [hf]
      exact List.map_congr_left fun i hi => by
        have hi' := List.mem_range.mp hi
        show (if i < a + m then (fs ++ ks).getD i .K else OTerm.var i) = fs.getD i .K
        rw [if_pos (by omega)]
        exact getD_app_left OTerm.K fs ks i (by omega)
    rw [e3, map_getD_range]
  rw [e1, e2] at h
  exact h

theorem All2.getDJ {α β : Type} {R : α → β → Prop} {da : α} {db : β} (hd : R da db) :
    ∀ {as : List α} {bs : List β}, All2 R as bs → ∀ j, R (as.getD j da) (bs.getD j db)
  | _, _, .nil, _ => hd
  | _, _, .cons r _, 0 => r
  | _, _, .cons _ h, j + 1 => All2.getDJ hd h j

theorem occ_absN {y : Nat} : ∀ {xs : List Nat} {t : OTerm}, Occ y (absN xs t) → Occ y t ∧ y ∉ xs
  | [], _, h => ⟨h, by simp⟩
  | x :: xs, t, h => by
    have h1 := occ_abs h
    have h2 := occ_absN h1.1
    exact ⟨h2.1, by simp [h1.2, h2.2]⟩

theorem ctorO_noocc {a j m : Nat} (hj : j < m) {i : Nat} (hi : Occ i (ctorO a j m)) : False := by
    have ⟨h1, h2⟩ := occ_absN hi
    apply h2
    have hv : i ∈ (appL (.var (a + j)) ((List.range a).map .var)).vars :=
      (OTerm.mem_vars i _).1 (OTerm.mem_of_occ h1)
    rw [List.mem_range]
    revert hv
    suffices ∀ (t : OTerm) (l : List Nat), (∀ k ∈ t.vars, k < a + m) → (∀ k ∈ l, k < a + m) →
        i ∈ (appL t (l.map .var)).vars → i < a + m by
      intro hv
      exact this (.var (a + j)) (List.range a) (by simp [OTerm.vars]; omega)
        (by intro k hk; simp at hk; omega) hv
    intro t l
    induction l generalizing t with
    | nil => intro ht _ hv; exact ht i hv
    | cons k l ih =>
      intro ht hl hv
      exact ih (t ⬝ₒ .var k) (by
        intro z hz; simp [OTerm.vars] at hz
        rcases hz with hz | hz
        · exact ht z hz
        · rw [hz]; exact hl k (by simp)) (fun z hz => hl z (by simp [hz])) hv

theorem ctorO_toTerm {a j m : Nat} (hj : j < m) : (toTerm (ctorO a j m)).toO = ctorO a j m := by
  unfold toTerm
  rw [toO_close]
  exact (subst_agree fun i hi => (ctorO_noocc hj hi).elim).trans (subst_var _)

section
variable {genvJ : Nm → OTerm} {P : Nm → Option GDef}

theorem trJ_junk : ∀ i, TrJ genvJ P (junk i) (junkY (bv i)) := fun i => by
  show TrJ genvJ P (.const K) (if bv i = 0 then Yv else .K)
  rw [if_neg (by unfold bv; omega)]
  exact .const K

/-- **The simulation, Y a jet.**  If `c` steps to `c'` in the source
    semantics and `t` is a compiled form of `c`, Y a jet, then a run with
    the jet takes `t` to a compiled form of `c'`.  A recursive call is
    the jet's one step, `Y F` to `F (Y F)`, then `F`'s instance; it never
    looks inside Y. -/
theorem simulationJ (hF : FixedJ P genvJ) {c c' : Cl} (hs : SStep P c c') :
    ∀ {t : OTerm}, TrJ genvJ P c t → ∃ t', JSteps t t' ∧ TrJ genvJ P c' t' := by
  induction hs with
  | @beta caps ps b ρ args hl =>
    intro t ht
    obtain ⟨tf, ts, et, hf, hts⟩ := TrJ.apps_inv ht
    cases hf with
    | @clo _ _ _ _ γ hρ h0 =>
      rw [et]
      exact ⟨_, JSteps.of_weak (wrapLiftJ_beta caps ps _ γ ts (hts.length.symm.trans hl)),
        trJ_inst hF.2.2.2 (TrJ.override hρ hts) (by rw [override_zero, h0]) _ _⟩
  | @delta n ps b args hP hl =>
    intro t ht
    obtain ⟨tf, ts, et, hf, hts⟩ := TrJ.apps_inv ht
    cases hf with
    | gref _ =>
      rw [et, hF.2.1 n ps b hP]
      have h := absN_beta_subst (ps.map bv) (compJ genvJ ps b) junkY ts
        (by rw [List.length_map]; exact hts.length.symm.trans hl)
      exact ⟨_, JSteps.of_weak h,
        trJ_inst hF.2.2.2 (TrJ.override trJ_junk hts) (by rw [override_zero]; rfl) _ _⟩
  | @fix n s ps b args hP hl =>
    intro t ht
    obtain ⟨tf, ts, et, hf, hts⟩ := TrJ.apps_inv ht
    cases hf with
    | gref _ =>
      rw [et]
      have hg := hF.2.2.1 n s ps b hP
      have h1 : JSteps (appL (genvJ n) ts)
          (appL ((absN ((s :: ps).map bv) (compJ genvJ (s :: ps) b)).subst junkY ⬝ₒ genvJ n) ts) := by
        rw [hg]; exact JSteps.appL (.step (.fix _) (.refl _)) ts
      have h2 := absN_beta_subst ((s :: ps).map bv) (compJ genvJ (s :: ps) b) junkY (genvJ n :: ts)
        (by simp only [List.length_map, List.length_cons]; exact congrArg Nat.succ (hts.length.symm.trans hl))
      exact ⟨_, h1.trans (JSteps.of_weak h2),
        trJ_inst hF.2.2.2 (TrJ.override trJ_junk (.cons (.gref n) hts))
          (by rw [override_zero]; rfl) _ _⟩
  | @ctor n a j m fs ks hP hj hf hk =>
    intro t ht
    obtain ⟨tf, ts, et, htf, hts⟩ := TrJ.apps_inv ht
    obtain ⟨tfs, tks, e2, h1, h2⟩ := All2.split hts
    cases htf with
    | gref _ =>
      rw [et, e2, hF.1 n a j m hP, ctorO_toTerm hj]
      exact ⟨_, JSteps.of_weak (ctorO_beta hj (h1.length.symm.trans hf) (h2.length.symm.trans hk)),
        TrJ.apps (All2.getDJ (.const K) h2 j) h1⟩
  | left a _ ih =>
    intro t ht
    cases ht with
    | app hf ha =>
      obtain ⟨t', h, h'⟩ := ih hf
      exact ⟨_, JSteps.left _ h, .app h' ha⟩
  | right f _ ih =>
    intro t ht
    cases ht with
    | app hf ha =>
      obtain ⟨t', h, h'⟩ := ih ha
      exact ⟨_, JSteps.right _ h, .app hf h'⟩

/-- **The simulation, Y a jet, for runs.** -/
theorem simulationJ_steps (hF : FixedJ P genvJ) {c c' : Cl} (hs : SSteps P c c') :
    ∀ {t : OTerm}, TrJ genvJ P c t → ∃ t', JSteps t t' ∧ TrJ genvJ P c' t' := by
  induction hs with
  | refl c => exact fun ht => ⟨_, .refl _, ht⟩
  | step s _ ih =>
    intro t ht
    obtain ⟨t1, h1, h1'⟩ := simulationJ hF s ht
    obtain ⟨t2, h2, h2'⟩ := ih h1'
    exact ⟨t2, h1.trans h2, h2'⟩

end

-- ---------------------------------------------------------------------------
-- B, read back: the jet is lean-ski's compiled program, and Tr
-- ---------------------------------------------------------------------------

/-- Read a jet term back: Y as `Ycomb`, a source binder's variable as the
    binder's own. -/
def ρR : Nat → OTerm := fun i => if i = 0 then Ycomb.toO else .var (i - 1)
def rb (t : OTerm) : OTerm := t.subst ρR

/-- Read a jet term back to a closed term, its other variables junk. -/
def σR : Nat → Term := fun i => if i = 0 then Ycomb else K
def rbT (t : OTerm) : Term := t.close σR

theorem close_subst (σ : Nat → Term) (τ : Nat → OTerm) :
    ∀ t : OTerm, (t.subst τ).close σ = t.close (fun i => (τ i).close σ)
  | .S => rfl
  | .K => rfl
  | .I => rfl
  | .var _ => rfl
  | .app f x => by
    show OTerm.close σ (f.subst τ) ⬝ OTerm.close σ (x.subst τ) = _
    rw [close_subst σ τ f, close_subst σ τ x]; rfl

theorem mem_rb (x : Nat) : ∀ t : OTerm, (rb t).mem x = t.mem (bv x)
  | .S => rfl
  | .K => rfl
  | .I => rfl
  | .var y => by
    show (ρR y).mem x = (y == bv x)
    unfold ρR bv
    by_cases h : y = 0
    · rw [if_pos h, mem_toO]; subst h; simp
    · rw [if_neg h]
      show (y - 1 == x) = (y == x + 1)
      by_cases h2 : y = x + 1
      · subst h2; simp
      · have h3 : y - 1 ≠ x := by omega
        rw [beq_eq_false_iff_ne.2 h3, beq_eq_false_iff_ne.2 h2]
  | .app f a => by
    show ((rb f).mem x || (rb a).mem x) = (f.mem (bv x) || a.mem (bv x))
    rw [mem_rb x f, mem_rb x a]

theorem abs_nomem {x : Nat} : ∀ t : OTerm, t.mem x = false → abs x t = .K ⬝ₒ t
  | .S, _ => rfl
  | .K, _ => rfl
  | .I, _ => rfl
  | .var y, h => by
    have : y ≠ x := by simpa [OTerm.mem] using h
    simp [abs, this]
  | .app e f, h => by rw [abs_app, if_pos h]

theorem rb_var_iff (x : Nat) (f : OTerm) : rb f = .var x ↔ f = .var (bv x) := by
  cases f with
  | var y =>
    show ρR y = .var x ↔ _
    unfold ρR bv
    by_cases h : y = 0
    · rw [if_pos h]; subst h; simp [Ycomb, Term.toO]
    · rw [if_neg h]; simp; omega
  | app _ _ => simp [rb, OTerm.subst]
  | S => simp [rb, OTerm.subst]
  | K => simp [rb, OTerm.subst]
  | I => simp [rb, OTerm.subst]

/-- **Reading back commutes with abstracting.** -/
theorem rb_abs (x : Nat) : ∀ t : OTerm, rb (abs (bv x) t) = abs x (rb t)
  | .S => rfl
  | .K => rfl
  | .I => rfl
  | .var y => by
    by_cases h : y = bv x
    · subst h
      show rb (if bv x = bv x then .I else .K ⬝ₒ .var (bv x)) = abs x (ρR (bv x))
      rw [if_pos rfl]
      show OTerm.I = abs x (if bv x = 0 then Ycomb.toO else .var (bv x - 1))
      rw [if_neg (by unfold bv; omega)]
      show OTerm.I = abs x (.var (x + 1 - 1))
      rw [Nat.add_sub_cancel]; simp [abs]
    · show rb (if y = bv x then .I else .K ⬝ₒ .var y) = abs x (ρR y)
      rw [if_neg h]
      show .K ⬝ₒ ρR y = abs x (ρR y)
      unfold ρR
      by_cases h0 : y = 0
      · rw [if_pos h0]
        show OTerm.K ⬝ₒ Ycomb.toO = abs x Ycomb.toO
        rw [abs_nomem _ (mem_toO x Ycomb)]
      · rw [if_neg h0]
        have : y - 1 ≠ x := by unfold bv at h; omega
        simp [abs, this]
  | .app e f => by
    show rb (abs (bv x) (.app e f)) = abs x (.app (rb e) (rb f))
    rw [abs_app, abs_app]
    have hm : (OTerm.app (rb e) (rb f)).mem x = (OTerm.app e f).mem (bv x) :=
      mem_rb x (.app e f)
    have hme : (rb e).mem x = e.mem (bv x) := mem_rb x e
    rw [hm, hme]
    by_cases h1 : (OTerm.app e f).mem (bv x) = false
    · rw [if_pos h1, if_pos h1]; rfl
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : f = .var (bv x) ∧ e.mem (bv x) = false
      · rw [if_pos h2, if_pos ⟨(rb_var_iff x f).2 h2.1, h2.2⟩]
      · rw [if_neg h2, if_neg (fun h => h2 ⟨(rb_var_iff x f).1 h.1, h.2⟩)]
        show OTerm.S.subst ρR ⬝ₒ rb (abs (bv x) e) ⬝ₒ rb (abs (bv x) f) = _
        rw [rb_abs x e, rb_abs x f]; rfl

theorem rb_absN (t : OTerm) : ∀ xs : List Nat, rb (absN (xs.map bv) t) = absN xs (rb t)
  | [] => rfl
  | x :: xs => by
    show rb (abs (bv x) (absN (xs.map bv) t)) = abs x (absN xs (rb t))
    rw [rb_abs, rb_absN t xs]

theorem rb_wrapLiftJ (caps ps : List Nat) (B : OTerm) :
    rb (wrapLiftJ caps ps B) = wrapLift caps ps (rb B) := by
  unfold wrapLiftJ wrapLift
  rw [rb, subst_appL, ← List.map_append, ← rb, rb_absN, List.map_map, List.map_map]
  congr 1

section
variable {genvJ : Nm → OTerm} {genv : Nm → Term}

mutual
  /-- **The jet compiler is lean-ski's**, read back. -/
  theorem rb_compJ (hg : ∀ n, rb (genvJ n) = (genv n).toO) :
      ∀ (sc : List Nat) (e : CSrc), rb (compJ genvJ sc e) = comp sc (e.resolve genv)
    | _, .glob n => hg n
    | _, .var x => by
      show ρR (bv x) = .var x
      unfold ρR bv; rw [if_neg (by omega), Nat.add_sub_cancel]
    | sc, .app f a => by
      show OTerm.app (rb (compJ genvJ sc f)) (rb (compJ genvJ sc a)) = _
      rw [rb_compJ hg sc f, rb_compJ hg sc a]; rfl
    | sc, .lam x b => by
      show rb (compLamJ genvJ _ [x] b) = compLam _ [x] (b.resolve genv)
      have ho : (fun s => (Src.lam x (b.resolve genv)).occurs s) = (fun s => (CSrc.lam x b).occurs s) :=
        funext fun s => CSrc.occurs_resolve genv s (.lam x b)
      rw [ho]
      exact rb_compLamJ hg _ [x] b
  theorem rb_compLamJ (hg : ∀ n, rb (genvJ n) = (genv n).toO) :
      ∀ (caps ps : List Nat) (e : CSrc),
        rb (compLamJ genvJ caps ps e) = compLam caps ps (e.resolve genv)
    | caps, ps, .lam y b => by
      show rb (compLamJ genvJ caps (ps ++ [y]) b) = compLam caps (ps ++ [y]) (b.resolve genv)
      exact rb_compLamJ hg caps (ps ++ [y]) b
    | caps, ps, .glob n => by
      show rb (wrapLiftJ caps ps (genvJ n)) = wrapLift caps ps (genv n).toO
      rw [rb_wrapLiftJ, hg]
    | caps, ps, .var x => by
      show rb (wrapLiftJ caps ps (.var (bv x))) = wrapLift caps ps (.var x)
      rw [rb_wrapLiftJ]
      show wrapLift caps ps (ρR (bv x)) = _
      unfold ρR bv; rw [if_neg (by omega), Nat.add_sub_cancel]
    | caps, ps, .app f a => by
      show rb (wrapLiftJ caps ps (compJ genvJ (caps ++ ps) f ⬝ₒ compJ genvJ (caps ++ ps) a)) =
        wrapLift caps ps (comp (caps ++ ps) (f.resolve genv) ⬝ₒ comp (caps ++ ps) (a.resolve genv))
      rw [rb_wrapLiftJ]
      show wrapLift caps ps (OTerm.app (rb _) (rb _)) = _
      rw [rb_compJ hg (caps ++ ps) f, rb_compJ hg (caps ++ ps) a]
end

end

theorem rbT_eq (t : OTerm) : rbT t = (rb t).close (fun _ => K) := by
  unfold rbT rb
  rw [close_subst]
  congr 1
  funext i
  unfold σR ρR
  by_cases h : i = 0
  · rw [if_pos h, if_pos h, close_toO]
  · rw [if_neg h, if_neg h]; rfl

theorem rbT_junkY (t : OTerm) : rbT (t.subst junkY) = rbT t := by
  unfold rbT
  rw [close_subst]
  congr 1
  funext i
  unfold junkY σR
  by_cases h : i = 0
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]; rfl

theorem rb_yclosed {t : OTerm} (h : YClosed t) : rb t = (rbT t).toO := by
  unfold rb rbT
  rw [toO_close]
  exact subst_agree fun i hi => by
    rw [h i ((OTerm.mem_vars i t).1 (OTerm.mem_of_occ hi))]; rfl

section
variable {genvJ : Nm → OTerm} {P : Nm → Option GDef}

/-- The program the jet compiler gives, read back. -/
def genvR (genvJ : Nm → OTerm) : Nm → Term := fun n => rbT (genvJ n)

/-- **The jet program is lean-ski's compiled program**: read back, every
    global's term is what lean-ski's compiler gives (`Fixed`), Y as
    `Ycomb`. -/
theorem fixed_of_fixedJ (hF : FixedJ P genvJ) : Fixed P (genvR genvJ) := by
  have hg : ∀ n, rb (genvJ n) = (genvR genvJ n).toO := fun n => rb_yclosed (hF.2.2.2 n)
  refine ⟨fun n a j m hP => ?_, fun n e hP => ?_⟩
  · show rbT (genvJ n) = _
    rw [hF.1 n a j m hP]
    unfold rbT
    rw [close_toO]
  · obtain ⟨ps, self, b⟩ := e
    cases self with
    | none =>
      show rbT (genvJ n) = toTerm (compDef ps (b.resolve (genvR genvJ)))
      rw [hF.2.1 n ps b hP, rbT_junkY, rbT_eq, rb_absN, rb_compJ hg]
      rfl
    | some s =>
      show rbT (genvJ n) = toTerm (compRec s ps (b.resolve (genvR genvJ)))
      rw [hF.2.2.1 n s ps b hP]
      show σR 0 ⬝ rbT ((absN ((s :: ps).map bv) (compJ genvJ (s :: ps) b)).subst junkY) = _
      rw [rbT_junkY, rbT_eq, rb_absN, rb_compJ hg]
      show Ycomb ⬝ _ = (Ycomb.toO ⬝ₒ _).close (fun _ => K)
      show Ycomb ⬝ _ = Ycomb.toO.close (fun _ => K) ⬝ _
      rw [close_toO]

/-- **Every jet state reads back to a compiled form, by lean-ski's `Tr`.** -/
theorem tr_of_trJ (hF : FixedJ P genvJ) {c : Cl} {t : OTerm} (h : TrJ genvJ P c t) :
    Tr (genvR genvJ) P c (rbT t) := by
  have hg : ∀ n, rb (genvJ n) = (genvR genvJ n).toO := fun n => rb_yclosed (hF.2.2.2 n)
  induction h with
  | const t => show Tr _ P _ (t.toO.close σR); rw [close_toO]; exact .const t
  | gref n => exact .gref n
  | @clo caps ps b ρ γ _ h0 ih =>
    have e : rbT ((wrapLiftJ caps ps (compJ genvJ (caps ++ ps) b)).subst γ) =
        (wrapLift caps ps (comp (caps ++ ps) (b.resolve (genvR genvJ)))).close
          (fun i => rbT (γ (bv i))) := by
      rw [← rb_compJ hg, ← rb_wrapLiftJ]
      unfold rbT rb
      rw [close_subst, close_subst]
      congr 1
      funext i
      unfold ρR
      by_cases hi : i = 0
      · rw [if_pos hi, close_toO, hi, h0]; rfl
      · rw [if_neg hi]
        show _ = (γ (i - 1 + 1)).close σR
        rw [Nat.sub_add_cancel (by omega)]
    rw [e]
    exact .clo ih
  | app _ _ ihf iha => exact .app ihf iha

/-- **Y's simulation, up to lean-ski's `Tr`.**  A compiled program run
    with Y a jet, `Y g` to `g (Y g)` in one step and never looked inside,
    matches every run of the source: each state it reaches reads back,
    Y as `Ycomb`, to a compiled form of the source's state, by lean-ski's
    `Tr` over lean-ski's compiled program. -/
theorem fix_simulation (hF : FixedJ P genvJ) {c c' : Cl} (hs : SSteps P c c') {t : OTerm}
    (ht : TrJ genvJ P c t) :
    ∃ t', JSteps t t' ∧ TrJ genvJ P c' t' ∧ Tr (genvR genvJ) P c' (rbT t') := by
  obtain ⟨t', h1, h2⟩ := simulationJ_steps hF hs ht
  exact ⟨t', h1, h2, tr_of_trJ hF h2⟩

end

-- ---------------------------------------------------------------------------
-- B applies: lean-ski's compiled programs, Y a jet
-- ---------------------------------------------------------------------------

/-- A closed term with every `Ycomb` the jet, as Avon finds Y by tree
    identity when it loads a term. -/
def jetify (t : Term) : OTerm :=
  if t = Ycomb then Yv else
  match t with
  | .app f x => .app (jetify f) (jetify x)
  | t => t.toO

theorem jetify_yclosed : ∀ t : Term, YClosed (jetify t)
  | .S => by intro i h; simp [jetify, Ycomb, Term.toO, OTerm.vars] at h
  | .K => by intro i h; simp [jetify, Ycomb, Term.toO, OTerm.vars] at h
  | .I => by intro i h; simp [jetify, Ycomb, Term.toO, OTerm.vars] at h
  | .app f x => by
    intro i h
    unfold jetify at h
    split at h
    · simpa [Yv, OTerm.vars] using h
    · simp only [OTerm.vars, List.mem_append] at h
      rcases h with h | h
      · exact jetify_yclosed f i h
      · exact jetify_yclosed x i h

/-- Reading back undoes `jetify`. -/
theorem rbT_jetify : ∀ t : Term, rbT (jetify t) = t
  | .S => rfl
  | .K => rfl
  | .I => rfl
  | .app f x => by
    unfold jetify
    split
    · rename_i h; rw [h]; rfl
    · show rbT (jetify f) ⬝ rbT (jetify x) = f ⬝ x
      rw [rbT_jetify f, rbT_jetify x]

/-- `FixedJ`, decided for a program's definitions, `absNF` for speed. -/
def fixedJCheck (defs : List (Nm × GDef)) (genvJ : Nm → OTerm) : Bool :=
  defs.all fun p =>
    match defs.lookup p.1 with
    | some (.ctor a j m) => genvJ p.1 == (toTerm (ctorOF a j m)).toO
    | some (.eqn ⟨ps, none, b⟩) =>
      genvJ p.1 == (absNF (ps.map bv) (compJ genvJ ps b)).subst junkY
    | some (.eqn ⟨ps, some s, b⟩) =>
      genvJ p.1 == Yv ⬝ₒ (absNF ((s :: ps).map bv) (compJ genvJ (s :: ps) b)).subst junkY
    | none => true

theorem fixedJ_of_check {defs : List (Nm × GDef)} {genvJ : Nm → OTerm}
    (h : fixedJCheck defs genvJ = true) (hY : ∀ n, YClosed (genvJ n)) :
    FixedJ (fun n => defs.lookup n) genvJ := by
  unfold fixedJCheck at h
  rw [List.all_eq_true] at h
  have get : ∀ {n : Nm} {d : GDef}, defs.lookup n = some d → ∃ p ∈ defs, p.1 = n :=
    fun hn => lookup_some_mem hn
  refine ⟨fun n a j m hn => ?_, fun n ps b hn => ?_, fun n s ps b hn => ?_, hY⟩
  · obtain ⟨p, hp, hp1⟩ := get hn
    have hc := h p hp
    rw [hp1] at hc
    simp only [show defs.lookup n = some (.ctor a j m) from hn, beq_iff_eq] at hc
    rw [hc, ctorOF_eq]
  · obtain ⟨p, hp, hp1⟩ := get hn
    have hc := h p hp
    rw [hp1] at hc
    simp only [show defs.lookup n = some (.eqn ⟨ps, none, b⟩) from hn, beq_iff_eq] at hc
    rw [hc, absNF_eq]
  · obtain ⟨p, hp, hp1⟩ := get hn
    have hc := h p hp
    rw [hp1] at hc
    simp only [show defs.lookup n = some (.eqn ⟨ps, some s, b⟩) from hn, beq_iff_eq] at hc
    rw [hc, absNF_eq]

/-- The jet program of a source file: lean-ski's compiled globals, each
    `Ycomb` the jet. -/
def genvJOf (src : List Nat) : Nm → OTerm := fun n => jetify (genvOf src n)

theorem genvR_genvJOf (src : List Nat) : genvR (genvJOf src) = genvOf src :=
  funext fun n => rbT_jetify _

set_option maxRecDepth 100000 in
/-- **B applies to lean-ski's `sum` program**: its compiled globals, `Ycomb`
    the jet, are what the jet compiler gives. -/
theorem sum_fixedJ : FixedJ (progOf sumText) (genvJOf sumText) :=
  fixedJ_of_check (by decide +kernel) (fun _ => jetify_yclosed _)

set_option maxRecDepth 100000 in
theorem loop_fixedJ : FixedJ (progOf loopText) (genvJOf loopText) :=
  fixedJ_of_check (by decide +kernel) (fun _ => jetify_yclosed _)

/-- Each program has recursive equations, where the jet's rule fires. -/
theorem sum_loop_recursive :
    ((progDefs sumText).filter fun p => match p.2 with
      | .eqn ⟨_, some _, _⟩ => true | _ => false).length = 4 ∧
    ((progDefs loopText).filter fun p => match p.2 with
      | .eqn ⟨_, some _, _⟩ => true | _ => false).length = 4 := by decide +kernel

/-- **Y's simulation for `sum`, up to lean-ski's `Tr` over lean-ski's own
    compiled program** (`sum_fixed`). -/
theorem sum_fix_simulation {c c' : Cl} (hs : SSteps (progOf sumText) c c') {t : OTerm}
    (ht : TrJ (genvJOf sumText) (progOf sumText) c t) :
    ∃ t', JSteps t t' ∧ Tr (genvOf sumText) (progOf sumText) c' (rbT t') := by
  obtain ⟨t', h1, _, h3⟩ := fix_simulation sum_fixedJ hs ht
  rw [genvR_genvJOf] at h3
  exact ⟨t', h1, h3⟩

end AvonFix

#print axioms AvonFix.fix_join
#print axioms AvonFix.fix_normal
#print axioms AvonFix.simulationJ_steps
#print axioms AvonFix.fix_simulation
#print axioms AvonFix.fixed_of_fixedJ
#print axioms AvonFix.sum_fix_simulation
#print axioms AvonFix.loop_fixedJ
#print axioms AvonFix.sum_loop_recursive
#print axioms AvonFix.closure_spells_Y
