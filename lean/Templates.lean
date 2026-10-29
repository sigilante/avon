import Ski.Abs
import Std.Data.HashMap

/-!
# Avon's supercombinator templates: the load check and the fire, proved

In share mode a template's key at the head with all its arguments is
replaced, in one step, by the template's body instantiated over them
(`docs/DESIGN.md` §6.9).  `src/tmpl.c` accepts a template only if
abstracting its body over its formals gives its key; whatever produced
it, Python's expander, front1 or discovery, that one check stands
between a file and the reducer.  This file proves the check and the fire
(`docs/LEAN-JETS.md` §6).

* **The C abstracts as lean-ski does.**  `absC` is `hc_abstract`, line for
  line, and equals lean-ski's `abs` (`absC_eq`); `keyC`, `load_one`'s loop
  over the formals from the last, is `absN` (`keyC_eq`).
* **What `load_one` accepts is licensed.**  `loadC` is its verdict: a
  body using a variable no formal names is open, a closed head over the
  formals in order is η, a key that is no application is a bare
  combinator; otherwise the key is `absN xs body` (`loadC_accept`).
* **The fire is the body.**  `compile` is `load_one`'s compile into
  instructions, constants and arguments, and `instC` is `tmpl_instance`'s
  run of them; run, a compiled body is the body with each formal's
  argument for it, the last occurrence of a formal binding
  (`compile_den`).
* **So a fire is a reduct** (`template_fire`): for an accepted template and
  any arguments, as many as its formals, the key applied to them weakly
  reduces to what `tmpl_instance` builds.  This is lean-ski's
  `absN_beta_subst`, over open terms, so a referenced term's atoms, other
  than `S`, `K` and `I`, are inert variables.

**The replay.**  `Replay.replay` runs `av_templates_load`'s loop over a
template directory with `loadC` for `load_one`, and with the two checks
the model leaves to the file and the table: the key's digest against the
file's (SHA-256, written here, `digest_of`'s first 16 bytes) and a key
already accepted.  `tests/templates_lean_check.sh` requires its counts,
accepted, refused and skipped, to be Avon's on every set the tests ship
and on copies changed to reach each refusal but a digest collision.  The
replay is not proved; it checks by those totals that the check's model
reads as the C does, and it runs neither `compile` nor `instC`.  It reads
numbers as the compilers write them, digits only, where the C's `strtoul`
would also take leading blanks and a sign; it refuses a formals list with
a trailing comma, and text after the body behind a tab, which the C
accepts; and it has no depth limit where `parse_body` stops at 100,000
levels: inputs no shipped file holds.

**What stays trusted:** that `absC`, `loadC`, `compile` and `instC` read as
the C does (the replay tests the first two by its counts); that a key's canonical node is the term
it stands for (`hc_canon`, `hc_app`), and that a referenced term holds no
formal's marker (both parsers refuse a leaf name beginning `@`); the
globals, the constants' nodes with inner templates wrapped, each a jet
node standing for its term; and the reducer's other paths for a
template, a constructor's dispatch, a case's join, a successor built as a
word (`sucop`), a deferred root (`tmpl_defer`) and the root written in
place, which act as the instance would and are tested, not proved.  The theorems are about
values; a jet's count is not the term's (`docs/DESIGN.md` §6.5).

Run from lean-ski, which supplies `Ski.Abs`:

    cd ~/Code/ski/lean-ski && lake env lean --run ~/avon/lean/Templates.lean DIR...

The kernel checks the theorems as the file elaborates; `main` then
replays each template directory and prints its counts.
-/

open Term

namespace AvonTemplates

-- ---------------------------------------------------------------------------
-- Bodies, as `parse_body` builds them
-- ---------------------------------------------------------------------------

/-- `AV_JET_ARITY_MAX`: formals are below it; a referenced term's atoms are
    variables from it up. -/
def arityMax : Nat := 64

/-- A template's body as `parse_body` (`src/tmpl.c`) builds it: `B_VAR`, a
    formal's variable `v` (below `AV_JET_ARITY_MAX`, 64); `B_REF`, a
    referenced term or `S`, `K`, `I`, its atoms variables from 64 up; and
    `B_APP`. -/
inductive Body
  | var (v : Nat)
  | ref (c : OTerm)
  | app (f x : Body)

namespace Body

/-- The term a body stands for: what `load_one`'s canonical nodes `cn`
    hold, a formal's marker `@x<v>` as variable `v`. -/
def toO : Body → OTerm
  | .var v => .var v
  | .ref c => c
  | .app f x => .app f.toO x.toO

/-- `closed[]`: no formal's variable. -/
def closed : Body → Bool
  | .var _ => false
  | .ref _ => true
  | .app f x => f.closed && x.closed

/-- The formals' variables the body uses. -/
def vars : Body → List Nat
  | .var v => [v]
  | .ref _ => []
  | .app f x => f.vars ++ x.vars

/-- The variables of its referenced terms: atoms. -/
def refVars : Body → List Nat
  | .var _ => []
  | .ref c => c.vars
  | .app f x => f.refVars ++ x.refVars

end Body

-- ---------------------------------------------------------------------------
-- The key: hc_abstract
-- ---------------------------------------------------------------------------

/-- `hc_abstract` (`src/tmpl.c`), line for line, over the terms its
    canonical nodes stand for: a node not an application is `I` if it is
    the marker and `K` over it otherwise; an application without the
    marker is `K` over it (`hc_free_in` reads the marker set `hc_app`
    keeps, `mem`); `M x` with `x` not in `M` is `M` (η); else `S` over
    both abstractions. -/
def absC (x : Nat) : OTerm → OTerm
  | .app e f =>
    if (OTerm.app e f).mem x = false then .K ⬝ₒ .app e f
    else if f = .var x ∧ e.mem x = false then e
    else .S ⬝ₒ absC x e ⬝ₒ absC x f
  | t => if t = .var x then .I else .K ⬝ₒ t

/-- **The C abstracts as lean-ski does**: `hc_abstract` is lean-ski's
    `abs`, aviary's bracket abstraction with η. -/
theorem absC_eq (x : Nat) : ∀ t, absC x t = abs x t
  | .S => rfl
  | .K => rfl
  | .I => rfl
  | .var y => by
    by_cases h : y = x
    · subst h; simp [absC, abs]
    · simp [absC, abs, h]
  | .app e f => by
    simp only [absC, abs]
    rw [absC_eq x e, absC_eq x f]

/-- `load_one`'s key: the body abstracted over the formals, the last
    first. -/
def keyC (xs : List Nat) (t : OTerm) : OTerm := xs.foldr absC t

theorem keyC_eq (xs : List Nat) (t : OTerm) : keyC xs t = absN xs t := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    show absC x (keyC xs t) = abs x (absN xs t)
    rw [ih, absC_eq]

-- ---------------------------------------------------------------------------
-- The verdict: load_one's checks
-- ---------------------------------------------------------------------------

/-- What `load_one` makes of a template before its key is compared with
    the file's: `accept` (0), open (2), η (3) or a bare combinator (5).
    The digest comparison (1) and the duplicate (4) need the file and the
    table; `Check` below replays them. -/
inductive Verdict | accept | openV | eta | leaf
  deriving DecidableEq, Repr

/-- The body's spine, stripped of the formals in order from the last;
    `none` if it is not that application. -/
def etaSpine : List Nat → Body → Option Body
  | [], b => some b
  | x :: rest, .app f (.var v) => if v = x then etaSpine rest f else none
  | _ :: _, _ => none

/-- η: the body is a closed `H` applied to the formals in order. -/
def isEta (xs : List Nat) (b : Body) : Bool :=
  match etaSpine xs.reverse b with
  | some h => h.closed
  | none => false

/-- `load_one`: open first, then η, then the key, refused if it is no
    application.  The key comes with the verdict. -/
def loadC (xs : List Nat) (b : Body) : Verdict × OTerm :=
  if b.vars.any (fun v => !xs.contains v) then (.openV, .K)
  else if isEta xs b then (.eta, .K)
  else
    let t := keyC xs b.toO
    match t with
    | .app _ _ => (.accept, t)
    | _ => (.leaf, t)

theorem loadC_accept {xs : List Nat} {b : Body} (h : (loadC xs b).1 = .accept) :
    (∀ v ∈ b.vars, v ∈ xs) ∧ (loadC xs b).2 = absN xs b.toO := by
  have hopen : (b.vars.any fun v => !xs.contains v) = false := by
    cases ho : (b.vars.any fun v => !xs.contains v)
    · rfl
    · unfold loadC at h; rw [if_pos ho] at h; cases h
  have heta : isEta xs b = false := by
    cases he : isEta xs b
    · rfl
    · unfold loadC at h
      rw [if_neg (by rw [hopen]; decide), if_pos he] at h; cases h
  have hk : (loadC xs b).2 = keyC xs b.toO := by
    unfold loadC
    rw [if_neg (by rw [hopen]; decide), if_neg (by rw [heta]; decide)]
    simp only
    split <;> rfl
  refine ⟨fun v hv => ?_, by rw [hk, keyC_eq]⟩
  have hn := List.any_eq_false.1 hopen v hv
  cases hc : xs.contains v
  · rw [hc] at hn; exact absurd rfl hn
  · exact List.contains_iff_mem.1 hc

-- ---------------------------------------------------------------------------
-- The compile and the instance
-- ---------------------------------------------------------------------------

/-- An instruction's operand: a constant, an argument, an earlier
    instruction's result (`TMPL_CONST`, `TMPL_ARG`, `TMPL_RES`). -/
inductive Opnd | const (j : Nat) | arg (i : Nat) | res (j : Nat)

/-- A compiled template: `T->ops`, pairs of operands, and `T->consts`. -/
structure Prog where
  ops : List (Opnd × Opnd)
  consts : List OTerm

/-- `argix`: a formal's position, the last occurrence binding. -/
def lastIdx : List Nat → Nat → Nat
  | [], _ => 0
  | _ :: xs, v => if xs.contains v then lastIdx xs v + 1 else 0

/-- `load_one`'s compile, children first, as `opnd[]` is filled: a
    formal's variable is its argument, a maximal closed subterm a constant,
    an open application an instruction over its parts' operands. -/
def compile (ix : Nat → Nat) : Body → Prog → Opnd × Prog
  | .var v, P => (.arg (ix v), P)
  | .ref c, P => (.const P.consts.length, { P with consts := P.consts ++ [c] })
  | .app f x, P =>
    if (Body.app f x).closed then
      (.const P.consts.length, { P with consts := P.consts ++ [(Body.app f x).toO] })
    else
      let r1 := compile ix f P
      let r2 := compile ix x r1.2
      (.res r2.2.ops.length, { r2.2 with ops := r2.2.ops ++ [(r1.1, r2.1)] })

/-- `OPND`: an operand's node, from the constants, the arguments (first
    argument first) and the results so far. -/
def resolve (cs args res : List OTerm) : Opnd → OTerm
  | .const j => cs.getD j .K
  | .arg i => args.getD i .K
  | .res j => res.getD j .K

/-- The step `tmpl_instance` takes per instruction: one application of
    its two operands' nodes, appended to the results. -/
def opStep (cs args : List OTerm) (res : List OTerm) (p : Opnd × Opnd) : List OTerm :=
  res ++ [resolve cs args res p.1 ⬝ₒ resolve cs args res p.2]

/-- The results of `tmpl_instance`'s loop. -/
def runOps (cs args : List OTerm) (ops : List (Opnd × Opnd)) : List OTerm :=
  ops.foldl (opStep cs args) []

/-- `tmpl_instance`: the instructions run over the arguments, then the
    root operand's node. -/
def instC (P : Prog) (root : Opnd) (args : List OTerm) : OTerm :=
  resolve P.consts args (runOps P.consts args P.ops) root

theorem foldl_opStep (cs args : List OTerm) :
    ∀ (l : List (Opnd × Opnd)) (acc : List OTerm),
      ∃ d, l.foldl (opStep cs args) acc = acc ++ d ∧ d.length = l.length
  | [], acc => ⟨[], by simp⟩
  | p :: l, acc => by
    obtain ⟨d, h, hl⟩ := foldl_opStep cs args l (opStep cs args acc p)
    refine ⟨(resolve cs args acc p.1 ⬝ₒ resolve cs args acc p.2) :: d, ?_, by simp [hl]⟩
    rw [List.foldl_cons, h]
    simp [opStep]

theorem runOps_append (cs args : List OTerm) (ops more : List (Opnd × Opnd)) :
    ∃ d, runOps cs args (ops ++ more) = runOps cs args ops ++ d := by
  unfold runOps
  rw [List.foldl_append]
  obtain ⟨d, h, _⟩ := foldl_opStep cs args more (ops.foldl (opStep cs args) [])
  exact ⟨d, h⟩

theorem runOps_length (cs args : List OTerm) (ops : List (Opnd × Opnd)) :
    (runOps cs args ops).length = ops.length := by
  obtain ⟨d, h, hl⟩ := foldl_opStep cs args ops []
  unfold runOps; rw [h]; simp [hl]

theorem runOps_snoc (cs args : List OTerm) (ops : List (Opnd × Opnd)) (p : Opnd × Opnd) :
    runOps cs args (ops ++ [p]) = opStep cs args (runOps cs args ops) p := by
  unfold runOps; rw [List.foldl_append]; rfl

theorem getD_append_left {α : Type} (l d : List α) (x : α) {i : Nat} (h : i < l.length) :
    (l ++ d).getD i x = l.getD i x := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc {α : Type} (l e : List α) (a x : α) : (l ++ [a] ++ e).getD l.length x = a := by
  simp [List.getD_eq_getElem?_getD]

theorem toO_closed {σ : Nat → OTerm} :
    ∀ b : Body, b.closed = true → (∀ y ∈ b.refVars, σ y = .var y) → b.toO.subst σ = b.toO
  | .var _, h, _ => by cases h
  | .ref c, _, hr => by
    show c.subst σ = c
    rw [subst_agree (τ₂ := OTerm.var) (fun i hi => hr i (by
      show i ∈ c.vars; exact (OTerm.mem_vars i c).1 (OTerm.mem_of_occ hi))), subst_var]
  | .app f x, h, hr => by
    simp only [Body.closed, Bool.and_eq_true] at h
    show OTerm.app (f.toO.subst σ) (x.toO.subst σ) = OTerm.app f.toO x.toO
    rw [toO_closed f h.1 (fun y hy => hr y (by simp [Body.refVars, hy])),
      toO_closed x h.2 (fun y hy => hr y (by simp [Body.refVars, hy]))]

/-- **The compile is the body**: run by `tmpl_instance`, a compiled
    body's root operand is the body with each formal's argument for it,
    whatever constants and instructions come before or after it. -/
theorem compile_den (ix : Nat → Nat) (args : List OTerm) (σ : Nat → OTerm) :
    ∀ (b : Body) (P : Prog),
      (∀ v ∈ b.vars, args.getD (ix v) .K = σ v) → (∀ y ∈ b.refVars, σ y = .var y) →
      (∃ dc, (compile ix b P).2.consts = P.consts ++ dc) ∧
      (∃ dops, (compile ix b P).2.ops = P.ops ++ dops) ∧
      ∀ (e : List OTerm) (more : List (Opnd × Opnd)),
        resolve ((compile ix b P).2.consts ++ e) args
          (runOps ((compile ix b P).2.consts ++ e) args ((compile ix b P).2.ops ++ more))
          (compile ix b P).1 = b.toO.subst σ
  | .var v, P, hv, _ => by
    refine ⟨⟨[], by simp [compile]⟩, ⟨[], by simp [compile]⟩, fun e more => ?_⟩
    simp only [compile, resolve]
    exact hv v (by simp [Body.vars])
  | .ref c, P, _, hr => by
    refine ⟨⟨[c], rfl⟩, ⟨[], by simp [compile]⟩, fun e more => ?_⟩
    simp only [compile, resolve]
    rw [getD_snoc]
    exact (toO_closed (.ref c) rfl hr).symm
  | .app f x, P, hv, hr => by
    by_cases hc : (Body.app f x).closed = true
    · refine ⟨⟨[(Body.app f x).toO], by simp [compile, hc]⟩, ⟨[], by simp [compile, hc]⟩,
        fun e more => ?_⟩
      simp only [compile, hc, if_true, resolve]
      rw [getD_snoc]
      exact (toO_closed (.app f x) hc hr).symm
    · have hvf : ∀ v ∈ f.vars, args.getD (ix v) .K = σ v :=
        fun v h => hv v (by simp [Body.vars, h])
      have hvx : ∀ v ∈ x.vars, args.getD (ix v) .K = σ v :=
        fun v h => hv v (by simp [Body.vars, h])
      have hrf : ∀ y ∈ f.refVars, σ y = .var y := fun y h => hr y (by simp [Body.refVars, h])
      have hrx : ∀ y ∈ x.refVars, σ y = .var y := fun y h => hr y (by simp [Body.refVars, h])
      obtain ⟨⟨dc1, hc1⟩, ⟨do1, ho1⟩, hd1⟩ := compile_den ix args σ f P hvf hrf
      obtain ⟨⟨dc2, hc2⟩, ⟨do2, ho2⟩, hd2⟩ :=
        compile_den ix args σ x (compile ix f P).2 hvx hrx
      simp only [compile, hc, Bool.false_eq_true, if_false]
      generalize compile ix f P = r1 at hc1 ho1 hd1 hc2 ho2 hd2 ⊢
      generalize compile ix x r1.2 = r2 at hc2 ho2 hd2 ⊢
      obtain ⟨o1, P1⟩ := r1
      obtain ⟨o2, P2⟩ := r2
      simp only at hc1 ho1 hd1 hc2 ho2 hd2 ⊢
      refine ⟨⟨dc1 ++ dc2, by simp [hc2, hc1]⟩, ⟨do1 ++ do2 ++ [(o1, o2)], by simp [ho2, ho1]⟩,
        fun e more => ?_⟩
      simp only [resolve]
      obtain ⟨d, hd⟩ := runOps_append (P2.consts ++ e) args (P2.ops ++ [(o1, o2)]) more
      rw [hd, runOps_snoc]
      have hgx := runOps_length (P2.consts ++ e) args P2.ops
      rw [← hgx]
      simp only [opStep]
      rw [getD_snoc]
      show OTerm.app _ _ = OTerm.app (f.toO.subst σ) (x.toO.subst σ)
      congr 1
      · have := hd1 (dc2 ++ e) do2
        rw [← List.append_assoc, ← hc2, ← ho2] at this
        exact this
      · have := hd2 e []
        rw [List.append_nil] at this
        exact this

-- ---------------------------------------------------------------------------
-- The licence
-- ---------------------------------------------------------------------------

theorem override_not_mem (ρ : Nat → OTerm) (v : Nat) :
    ∀ (xs : List Nat) (Ns : List OTerm), v ∉ xs → override ρ xs Ns v = ρ v
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | x :: xs, N :: Ns, h => by
    simp only [List.mem_cons, not_or] at h
    show override (upd ρ x N) xs Ns v = ρ v
    rw [override_not_mem (upd ρ x N) v xs Ns h.2, upd, if_neg h.1]

/-- `override` gives a formal its argument at `argix`, the last
    occurrence, as `load_one` binds it. -/
theorem override_lastIdx (ρ : Nat → OTerm) (v : Nat) :
    ∀ (xs : List Nat) (Ns : List OTerm), Ns.length = xs.length → v ∈ xs →
      override ρ xs Ns v = Ns.getD (lastIdx xs v) .K
  | [], _, _, h => by cases h
  | _ :: _, [], hl, _ => by cases hl
  | x :: xs, N :: Ns, hl, h => by
    show override (upd ρ x N) xs Ns v = (N :: Ns).getD (lastIdx (x :: xs) v) .K
    simp only [lastIdx]
    by_cases hc : xs.contains v = true
    · rw [if_pos hc, override_lastIdx (upd ρ x N) v xs Ns (Nat.succ.inj hl)
        (List.contains_iff_mem.1 hc)]
      simp
    · rw [if_neg hc]
      have hn : v ∉ xs := fun hm => hc (List.contains_iff_mem.2 hm)
      have hx : v = x := by
        rcases List.mem_cons.1 h with e | e
        · exact e
        · exact absurd e hn
      rw [override_not_mem _ v xs Ns hn, upd, if_pos hx]
      simp

/-- **A template's fire is sound.**  If `load_one` accepts formals `xs`
    and body `b`, whose referenced terms' atoms are no formals (both
    parsers refuse a leaf name beginning `@`, the markers' prefix), then
    for any arguments, as many as the formals, the key applied to them
    weakly reduces to what `tmpl_instance` builds from the compiled
    template.  So the jet whose term is the key may fire as one step: its
    result is a reduct of the redex. -/
theorem template_fire {xs : List Nat} {b : Body} (hacc : (loadC xs b).1 = .accept)
    (hr : ∀ y ∈ b.refVars, y ∉ xs) (args : List OTerm) (hlen : args.length = xs.length) :
    OWSteps (appL (loadC xs b).2 args)
      (instC (compile (lastIdx xs) b ⟨[], []⟩).2 (compile (lastIdx xs) b ⟨[], []⟩).1 args) := by
  obtain ⟨hvars, hkey⟩ := loadC_accept hacc
  have hβ := absN_beta_subst xs b.toO OTerm.var args hlen
  rw [subst_var] at hβ
  rw [hkey]
  refine hβ.trans ?_
  have hden := compile_den (lastIdx xs) args (override OTerm.var xs args) b ⟨[], []⟩
    (fun v hv => (override_lastIdx OTerm.var v xs args hlen (hvars v hv)).symm)
    (fun y hy => override_not_mem OTerm.var y xs args (hr y hy))
  have := hden.2.2 [] []
  simp only [List.append_nil] at this
  unfold instC
  rw [this]
  exact .refl _

-- ---------------------------------------------------------------------------
-- The replay: Avon's loader over its files, with the model above
-- ---------------------------------------------------------------------------

/-! Nothing below is proved; it is the check that the model reads as the C
does.  `replay` runs `av_templates_load`'s loop over a template directory
with `loadC` for `load_one`'s verdict, then the two checks `loadC` leaves
to the file and the table: the key's digest against the file's (SHA-256,
written here) and a key already accepted.  `tests/templates_lean_check.sh`
compares its counts with Avon's own. -/

namespace Replay

def kSHA : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- SHA-256 (FIPS 180-4) of a byte string. -/
def sha256 (msg : ByteArray) : ByteArray := Id.run do
  let ml := msg.size
  let mut m := msg.push 0x80
  while m.size % 64 != 56 do m := m.push 0
  let bits := (ml * 8 : Nat)
  for i in [0:8] do m := m.push ((bits >>> (8 * (7 - i))) % 256).toUInt8
  let mut h : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  for c in [0:m.size / 64] do
    let mut w : Array UInt32 := Array.mkEmpty 64
    for t in [0:16] do
      let b := fun j => (m.get! (64 * c + 4 * t + j)).toUInt32
      w := w.push ((b 0 <<< 24) ||| (b 1 <<< 16) ||| (b 2 <<< 8) ||| b 3)
    for t in [16:64] do
      let s0 := rotr w[t-15]! 7 ^^^ rotr w[t-15]! 18 ^^^ (w[t-15]! >>> 3)
      let s1 := rotr w[t-2]! 17 ^^^ rotr w[t-2]! 19 ^^^ (w[t-2]! >>> 10)
      w := w.push (w[t-16]! + s0 + w[t-7]! + s1)
    let mut a := h[0]!; let mut b := h[1]!; let mut c' := h[2]!; let mut d := h[3]!
    let mut e := h[4]!; let mut f := h[5]!; let mut g := h[6]!; let mut hh := h[7]!
    for t in [0:64] do
      let S1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
      let ch := (e &&& f) ^^^ ((~~~e) &&& g)
      let t1 := hh + S1 + ch + kSHA[t]! + w[t]!
      let S0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
      let maj := (a &&& b) ^^^ (a &&& c') ^^^ (b &&& c')
      let t2 := S0 + maj
      hh := g; g := f; f := e; e := d + t1; d := c'; c' := b; b := a; a := t1 + t2
    h := #[h[0]! + a, h[1]! + b, h[2]! + c', h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g,
      h[7]! + hh]
  let mut out := ByteArray.empty
  for x in h do
    for j in [0:4] do out := out.push (x >>> (8 * (3 - j).toUInt32)).toUInt8
  return out

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n]!

/-- A digest: SHA-256's first 16 bytes as 32 hex digits (`digest_of`). -/
def digestOf (s : String) : String :=
  let d := sha256 s.toUTF8
  String.ofList ((List.range 16).flatMap fun i =>
    let b := (d.get! i).toNat
    [hexDigit (b / 16), hexDigit (b % 16)])

/-- `hash_all`: a leaf's digest from its name, an application's from its
    parts'.  Atoms are variables from 64 up, named by `atoms`. -/
partial def digest (atoms : Array String) (memo : Std.HashMap UInt64 (List (OTerm × String)))
    (t : OTerm) : String × Std.HashMap UInt64 (List (OTerm × String)) :=
  match t with
  | .S => (digestOf "S", memo)
  | .K => (digestOf "K", memo)
  | .I => (digestOf "I", memo)
  | .var v => (digestOf (atoms.getD (v - 64) s!"@x{v}"), memo)
  | .app f x =>
    let k := hash (repr t).pretty
    match (memo.getD k []).find? (·.1 == t) with
    | some (_, d) => (d, memo)
    | none =>
      let (df, m1) := digest atoms memo f
      let (dx, m2) := digest atoms m1 x
      let d := digestOf ("(" ++ df ++ " " ++ dx ++ ")")
      (d, m2.insert k ((t, d) :: m2.getD k []))

/-- The atom table: names other than `S`, `K`, `I`, as variables from 64. -/
structure Atoms where
  names : Array String := #[]

def Atoms.leaf (A : Atoms) (name : String) : OTerm × Atoms :=
  match name with
  | "S" => (.S, A) | "K" => (.K, A) | "I" => (.I, A)
  | _ =>
    match A.names.findIdx? (· == name) with
    | some i => (.var (64 + i), A)
    | none => (.var (64 + A.names.size), { names := A.names.push name })

/-- `av_parse_dag`'s form: `dag <id>=<leaf>|<l>.<r> … @<root>`. -/
def parseDag (A : Atoms) (src : String) : Option (OTerm × Atoms) := Id.run do
  let toks := (src.splitOn " ").filter (· ≠ "")
  if toks.head? != some "dag" then return none
  let mut env : Std.HashMap Nat OTerm := {}
  let mut A := A
  for tok in toks.tail do
    if tok.startsWith "@" then
      return (env.get? ((tok.drop 1).toString.toNat!)).map (·, A)
    match tok.splitOn "=" with
    | [id, rhs] =>
      match rhs.splitOn "." with
      | [l, r] =>
        if l.all Char.isDigit && r.all Char.isDigit && l ≠ "" && r ≠ "" then
          match env.get? l.toNat!, env.get? r.toNat! with
          | some tl, some tr => env := env.insert id.toNat! (.app tl tr)
          | _, _ => return none
        else
          let (t, A') := A.leaf rhs; A := A'; env := env.insert id.toNat! t
      | _ => let (t, A') := A.leaf rhs; A := A'; env := env.insert id.toNat! t
    | _ => return none
  return none

/-- `av_parse`'s printed form: leaves and parentheses, application to the
    left. -/
partial def parsePrinted (A : Atoms) (src : String) : Option (OTerm × Atoms) :=
  let toks := tokenize src.toList [] ""
  match go A toks [] with
  | some (t, A, []) => some (t, A)
  | _ => none
where
  tokenize : List Char → List String → String → List String
    | [], acc, cur => (if cur = "" then acc else cur :: acc).reverse
    | c :: cs, acc, cur =>
      let acc := if (c = '(' || c = ')' || c = ' ' || c = '\t') && cur ≠ "" then cur :: acc else acc
      let cur := if c = '(' || c = ')' || c = ' ' || c = '\t' then "" else cur.push c
      tokenize cs (if c = '(' then "(" :: acc else if c = ')' then ")" :: acc else acc) cur
  go (A : Atoms) : List String → List OTerm → Option (OTerm × Atoms × List String)
    | [], ts =>
      match ts.reverse with
      | [] => none
      | h :: tl => some (tl.foldl (· ⬝ₒ ·) h, A, [])
    | ")" :: rest, ts =>
      match ts.reverse with
      | [] => none
      | h :: tl => some (tl.foldl (· ⬝ₒ ·) h, A, ")" :: rest)
    | "(" :: rest, ts =>
      match go A rest [] with
      | some (t, A', ")" :: rest') => go A' rest' (t :: ts)
      | _ => none
    | name :: rest, ts => let (t, A') := A.leaf name; go A' rest (t :: ts)

/-- A file's hash field: `skijack-2:` and 32 lowercase hex digits
    (`av_hash_parse`); its 32 digits. -/
def hashField (s : String) : Option String :=
  let d := (s.drop 10).toString
  if s.startsWith "skijack-2:" && d.length = 32 &&
      d.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then some d else none

/-- `parse_body`: `` ` `` an application, `v<n>` a formal, `#<32 hex>` a
    referenced term, `S`, `K`, `I`; the rest after it. -/
partial def parseBody (refs : Std.HashMap String OTerm) : List Char → Option (Body × List Char)
  | ' ' :: cs => parseBody refs cs
  | '`' :: cs => do
    let (f, r1) ← parseBody refs cs
    let (x, r2) ← parseBody refs r1
    return (.app f x, r2)
  | 'v' :: cs =>
    let ds := cs.takeWhile Char.isDigit
    if ds.isEmpty then none else
    let v := (String.ofList ds).toNat!
    if v < arityMax then some (.var v, cs.drop ds.length) else none
  | '#' :: cs =>
    let h := String.ofList (cs.take 32)
    if cs.length < 32 then none else
    (refs.get? h).map fun t => (.ref t, cs.drop 32)
  | 'S' :: cs => some (.ref .S, cs)
  | 'K' :: cs => some (.ref .K, cs)
  | 'I' :: cs => some (.ref .I, cs)
  | _ => none

/-- `strtoul`'s digits at the start of a field, 0 if none. -/
def leadingNat (s : String) : Nat :=
  let ds := s.toList.takeWhile Char.isDigit
  if ds.isEmpty then 0 else (String.ofList ds).toNat!

/-- The formals field: comma-separated, each below 64, as many as the
    arity, the arity above 0. -/
def parseFormals (arity : Nat) (s : String) : Option (List Nat) :=
  if arity = 0 then none else
  let parts := if s = "" then [] else s.splitOn ","
  if parts.any (fun p => p = "" || !p.all Char.isDigit) then none else
  let xs := parts.map String.toNat!
  if xs.any (· ≥ arityMax) || xs.length ≠ arity then none else some xs

structure Counts where
  accepted : Nat := 0
  refused : Nat := 0
  skipped : Nat := 0

/-- `av_templates_load`'s two files and loop, `load_one` as `loadC`. -/
def replay (terms templates : String) : Except String Counts := do
  let mut A : Atoms := {}
  let mut refs : Std.HashMap String OTerm := {}
  for line in terms.splitOn "\n" do
    let fs := line.splitOn "\t"
    if fs.length < 3 then
      if line ≠ "" then throw "malformed template_terms.tsv line" else continue
    let some h := hashField fs[0]! | throw "malformed hash in template_terms.tsv"
    let src := "\t".intercalate (fs.drop 2)
    let parsed := if src.startsWith "dag " then parseDag A src else parsePrinted A src
    let some (t, A') := parsed | throw "unparsable term in template_terms.tsv"
    A := A'
    if (digest A.names {} t).1 ≠ h then throw "a template term does not match its hash"
    refs := refs.insert h t
  let mut c : Counts := {}
  let mut keys : List OTerm := []
  for line in templates.splitOn "\n" do
    let fs := line.splitOn "\t"
    if fs.length < 6 then
      if line ≠ "" then throw "malformed templates.tsv line" else continue
    let some key := hashField fs[0]! | throw "malformed hash in templates.tsv"
    let arity := leadingNat fs[3]!
    if arity > arityMax then c := { c with skipped := c.skipped + 1 }; continue
    let some xs := parseFormals arity fs[4]! | c := { c with refused := c.refused + 1 }; continue
    let bodyText := "\t".intercalate (fs.drop 5)
    match parseBody refs bodyText.toList with
    | some (b, rest) =>
      if !(rest.all (· = ' ')) then c := { c with refused := c.refused + 1 }; continue
      let (v, t) := loadC xs b
      match v with
      | .openV | .eta | .leaf => c := { c with skipped := c.skipped + 1 }
      | .accept =>
        if (digest A.names {} t).1 ≠ key then c := { c with refused := c.refused + 1 }
        else if keys.contains t then c := { c with skipped := c.skipped + 1 }
        else
          keys := t :: keys
          c := { c with accepted := c.accepted + 1 }
    | none => c := { c with refused := c.refused + 1 }
  return c

end Replay

end AvonTemplates

#print axioms AvonTemplates.template_fire
#print axioms AvonTemplates.absC_eq

open AvonTemplates.Replay in
def main (args : List String) : IO UInt32 := do
  -- SHA-256's own test vectors first
  let abc := digestOf "abc"
  if abc ≠ "ba7816bf8f01cfea414140de5dae2223" then
    IO.eprintln s!"sha256 wrong: {abc}"; return 1
  for dir in args do
    let terms ← IO.FS.readFile (dir ++ "/template_terms.tsv")
    let tmpl ← IO.FS.readFile (dir ++ "/templates.tsv")
    match replay terms tmpl with
    | .ok c => IO.println s!"{dir}: {c.accepted} accepted, {c.refused} refused, {c.skipped} skipped"
    | .error e => IO.println s!"{dir}: load fails: {e}"
  return 0
