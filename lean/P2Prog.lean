import Ski.ZK.Poseidon2Ex

/-!
# Avon's Poseidon2, printed from a program Lean proves

Avon runs Poseidon2 natively (`--p2`, `docs/DESIGN.md` §6.12) and writes
the jet's outputs into witness tables.  Its C is `src/p2_prog.h`, which
this file prints, and two theorems tie what it prints to lean-ski's
specification `Poseidon2.permute`:

* `run_prog`: the program `prog`, fifty-two layers of sixteen
  expressions each, computes `permute` on every state of sixteen.  The
  layers are lean-ski's own (`mat4LE`, `mixLE`, `sboxLE`, `sbox0LE`,
  `intLinLE`): the expressions from which her SKI term `P` and the
  Poseidon2 AIR are proved, joined by her bridges (`bridge_mat4`, …).
* `runC_eq`, with `prog_ok`: the program evaluated as C evaluates it --
  `uint64_t` arithmetic, which wraps at `2^64`, and each layer's results
  stored as `uint32_t` -- equals the program evaluated over the naturals,
  on every state of sixteen `uint32_t` values.  Every intermediate value
  is bounded below `2^64` (`bnd`, `fits`), so nothing wraps.

So `runC s prog = permute s` for every state of sixteen `uint32_t` values
(`permuteC`).  What is trusted is the printer below and C11's unsigned
arithmetic (6.2.5p9: `uint64_t` arithmetic is exact modulo `2^64`).  The
printer is `cExpr`, one line of C per constructor; `cBody`, which computes
a layer's sixteen results from the old state before storing them; `header`,
which prints each distinct layer once and calls the layers in `prog`'s
order; and the text of `av_p2_sbox`, which `sboxC` models step for step.

Run from lean-ski, which supplies `Ski.ZK.Poseidon2Ex`:

    cd ~/lean-ski && lake env lean --run ~/avon/lean/P2Prog.lean OUT.h

The kernel checks the theorems as the file elaborates; `main` then writes
the header to `OUT.h`.  `tests/p2_witness_check.sh` compares it with
`src/p2_prog.h`, byte for byte.
-/

open Poseidon2 Poseidon2SKI

namespace AvonP2

-- ---------------------------------------------------------------------------
-- The program
-- ---------------------------------------------------------------------------

/-- A layer: sixteen expressions over the previous state's sixteen
    elements. -/
abbrev Layer := List Ex

def step (s : List Nat) (L : Layer) : List Nat := L.map (Ex.eval (at16 s))

def run (s : List Nat) (prog : List Layer) : List Nat := prog.foldl step s

/-- A full round: the S-box layer with its constants, `M₄` on each block,
    the column mixing. -/
def full (rc : List Nat) : List Layer := [sboxLE rc, mat4LE, mixLE]

/-- A partial round: a constant and the S-box on the first element, the
    internal layer. -/
def part (c : Nat) : List Layer := [sbox0LE c, intLinLE]

/-- **The program**: the external layer, four full rounds, thirteen
    partial rounds, four full rounds. -/
def prog : List Layer :=
  [mat4LE, mixLE] ++ rcInitial.flatMap full ++ rcInternal.flatMap part ++ rcTerminal.flatMap full

theorem run_append (s : List Nat) (a b : List Layer) : run s (a ++ b) = run (run s a) b :=
  List.foldl_append

theorem run_ext (s : List Nat) (hs : s.length = 16) : run s [mat4LE, mixLE] = extLinear s := by
  show mixLE.map (Ex.eval (at16 (mat4LE.map (Ex.eval (at16 s))))) = extLinear s
  rw [bridge_mat4 s hs, bridge_mix _ (mat4L_len s hs)]
  rfl

theorem run_full1 (s rc : List Nat) (hs : s.length = 16) (hc : rc.length = 16) :
    run s (full rc) = extRound s rc := by
  show mixLE.map (Ex.eval (at16 (mat4LE.map (Ex.eval (at16 ((sboxLE rc).map (Ex.eval (at16 s)))))))) =
    extRound s rc
  rw [bridge_sbox s rc hs hc, bridge_mat4 _ (sboxL_len rc s hs hc),
    bridge_mix _ (mat4L_len _ (sboxL_len rc s hs hc))]
  rfl

theorem run_part1 (s : List Nat) (c : Nat) (hs : s.length = 16) : run s (part c) = intRound s c := by
  show intLinLE.map (Ex.eval (at16 ((sbox0LE c).map (Ex.eval (at16 s))))) = intRound s c
  rw [bridge_sbox0 s c hs, bridge_intLin _ (by rw [sbox0L_len]; exact hs), intRound_split]

theorem extRound_len (s rc : List Nat) (hs : s.length = 16) (hc : rc.length = 16) :
    (extRound s rc).length = 16 := by
  rw [extRound_split]
  exact mixL_len _ (mat4L_len _ (sboxL_len rc s hs hc))

theorem run_full : ∀ (rcs : List (List Nat)), rcs.all (fun rc => decide (rc.length = 16)) = true →
    ∀ s : List Nat, s.length = 16 → run s (rcs.flatMap full) = rcs.foldl extRound s
  | [], _, _, _ => rfl
  | rc :: rcs, h, s, hs => by
    have hc : rc.length = 16 := of_decide_eq_true (band_l h)
    rw [List.flatMap_cons, run_append, run_full1 s rc hs hc, List.foldl_cons]
    exact run_full rcs (band_r h) _ (extRound_len s rc hs hc)

theorem run_part : ∀ (cs : List Nat) (s : List Nat), s.length = 16 →
    run s (cs.flatMap part) = cs.foldl intRound s
  | [], _, _ => rfl
  | c :: cs, s, hs => by
    rw [List.flatMap_cons, run_append, run_part1 s c hs, List.foldl_cons]
    refine run_part cs _ ?_
    rw [intRound_split]
    exact intLinear_len _ (by rw [sbox0L_len]; exact hs)

/-- **The program computes the specification** on every state of
    sixteen. -/
theorem run_prog (s : List Nat) (hs : s.length = 16) : run s prog = permute s := by
  have hI : rcInitial.all (fun rc => decide (rc.length = 16)) = true := by decide
  have hT : rcTerminal.all (fun rc => decide (rc.length = 16)) = true := by decide
  have he : (extLinear s).length = 16 := by
    rw [extLinear_split]; exact mixL_len _ (mat4L_len s hs)
  have h1 := foldl_ext_len rcInitial hI _ he
  have h2 := foldl_int_len rcInternal _ h1
  show run s ([mat4LE, mixLE] ++ rcInitial.flatMap full ++ rcInternal.flatMap part ++
    rcTerminal.flatMap full) =
    rcTerminal.foldl extRound (rcInternal.foldl intRound (rcInitial.foldl extRound (extLinear s)))
  rw [run_append, run_append, run_append, run_ext s hs, run_full rcInitial hI _ he,
    run_part rcInternal _ h1, run_full rcTerminal hT _ h2]

-- ---------------------------------------------------------------------------
-- The program as C evaluates it
-- ---------------------------------------------------------------------------

/-- `uint64_t` arithmetic wraps at `W`. -/
def W : Nat := 2 ^ 64

/-- The largest input: elements are `uint32_t`. -/
def B : Nat := 2 ^ 32 - 1

/-- The printed S-box, `av_p2_sbox`, step for step, each product wrapping
    as `uint64_t` does. -/
def sboxC (x : Nat) : Nat :=
  let a := x % p
  let a2 := a * a % W % p
  let a3 := a2 * a % W % p
  let a6 := a3 * a3 % W % p
  a6 * a % W % p

/-- An expression as its printed C evaluates it: a literal is printed only
    below `W` (`fits`), so it is exact. -/
def evalC (ρ : Nat → Nat) : Ex → Nat
  | .var i => ρ i
  | .lit n => n
  | .add a b => (evalC ρ a + evalC ρ b) % W
  | .mul a b => (evalC ρ a * evalC ρ b) % W
  | .md a => evalC ρ a % p
  | .sbox a => sboxC (evalC ρ a)

/-- A layer as C evaluates it: each result stored as `uint32_t`. -/
def stepC (s : List Nat) (L : Layer) : List Nat := L.map fun e => evalC (at16 s) e % 2 ^ 32

def runC (s : List Nat) (prog : List Layer) : List Nat := prog.foldl stepC s

/-- An upper bound on an expression's value, its inputs at most `B`. -/
def bnd : Ex → Nat
  | .var _ => B
  | .lit n => n
  | .add a b => bnd a + bnd b
  | .mul a b => bnd a * bnd b
  | .md _ => p - 1
  | .sbox _ => p - 1

/-- Every variable is one of the sixteen elements, and every literal and
    every sum and product is below `W`. -/
def fits : Ex → Bool
  | .var i => decide (i < 16)
  | .lit n => decide (n < W)
  | .add a b => fits a && fits b && decide (bnd a + bnd b < W)
  | .mul a b => fits a && fits b && decide (bnd a * bnd b < W)
  | .md a => fits a
  | .sbox a => fits a

theorem mod_p_le (x : Nat) : x % p ≤ p - 1 := by
  have : x % p < p := Nat.mod_lt _ (by decide)
  omega

theorem mm (u v : Nat) : (u % p * v) % p = (u * v) % p := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem mm' (u v : Nat) : (u * (v % p)) % p = (u * v) % p := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem small (a b : Nat) (ha : a ≤ p - 1) (hb : b ≤ p - 1) : a * b % W = a * b := by
  apply Nat.mod_eq_of_lt
  have : a * b ≤ (p - 1) * (p - 1) := Nat.mul_le_mul ha hb
  have : (p - 1) * (p - 1) < W := by decide
  omega

theorem sbox_chain (a : Nat) :
    (a * a % p * a % p) * (a * a % p * a % p) % p * a % p = a ^ 7 % p := by
  rw [mm (a * a) a, mm (a * a * a) (a * a * a % p), mm' (a * a * a) (a * a * a),
    mm (a * a * a * (a * a * a)) a]
  congr 1
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc]

/-- **The printed S-box is the specification's.** -/
theorem sboxC_eq (x : Nat) : sboxC x = sbox x := by
  have ha := mod_p_le x
  simp only [sboxC, sbox]
  rw [small _ _ ha ha, small _ _ (mod_p_le _) ha, small _ _ (mod_p_le _) (mod_p_le _),
    small _ _ (mod_p_le _) ha, Nat.pow_mod]
  exact sbox_chain (x % p)

theorem evalC_eq (ρ : Nat → Nat) (hρ : ∀ i, ρ i ≤ B) :
    ∀ e : Ex, fits e = true → evalC ρ e = Ex.eval ρ e ∧ Ex.eval ρ e ≤ bnd e
  | .var i, _ => ⟨rfl, hρ i⟩
  | .lit _, _ => ⟨rfl, Nat.le_refl _⟩
  | .add a b, h => by
    simp only [fits, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨fa, fb⟩, hw⟩ := h
    obtain ⟨ea, ba⟩ := evalC_eq ρ hρ a fa
    obtain ⟨eb, bb⟩ := evalC_eq ρ hρ b fb
    have hle : Ex.eval ρ a + Ex.eval ρ b ≤ bnd a + bnd b := Nat.add_le_add ba bb
    refine ⟨?_, hle⟩
    show (evalC ρ a + evalC ρ b) % W = Ex.eval ρ a + Ex.eval ρ b
    rw [ea, eb]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hw)
  | .mul a b, h => by
    simp only [fits, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨fa, fb⟩, hw⟩ := h
    obtain ⟨ea, ba⟩ := evalC_eq ρ hρ a fa
    obtain ⟨eb, bb⟩ := evalC_eq ρ hρ b fb
    have hle : Ex.eval ρ a * Ex.eval ρ b ≤ bnd a * bnd b := Nat.mul_le_mul ba bb
    refine ⟨?_, hle⟩
    show (evalC ρ a * evalC ρ b) % W = Ex.eval ρ a * Ex.eval ρ b
    rw [ea, eb]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hw)
  | .md a, h => by
    obtain ⟨ea, _⟩ := evalC_eq ρ hρ a h
    refine ⟨?_, mod_p_le _⟩
    show evalC ρ a % p = Poseidon2.md (Ex.eval ρ a)
    rw [ea]; rfl
  | .sbox a, h => by
    obtain ⟨ea, _⟩ := evalC_eq ρ hρ a h
    refine ⟨?_, mod_p_le _⟩
    show sboxC (evalC ρ a) = Poseidon2.sbox (Ex.eval ρ a)
    rw [ea, sboxC_eq]

/-- A layer C can run: sixteen expressions, as the printed layer stores
    sixteen results; every expression fits; and every result is at most
    `B`, so it is an input of the next layer and a `uint32_t`. -/
def layerOK (L : Layer) : Bool :=
  decide (L.length = 16) && L.all fun e => fits e && decide (bnd e ≤ B)

/-- Every layer of the program is one C can run, checked by the kernel. -/
theorem prog_ok : prog.all layerOK = true := by decide +kernel

theorem at16_le (s : List Nat) (hs : ∀ x ∈ s, x ≤ B) (i : Nat) : at16 s i ≤ B := by
  unfold at16
  rw [List.getD_eq_getElem?_getD]
  cases h : s[i]? with
  | none => exact Nat.zero_le _
  | some x => exact hs x (List.mem_of_getElem? h)

theorem stepC_eq (s : List Nat) (hs : ∀ x ∈ s, x ≤ B) (L : Layer) (hL : layerOK L = true) :
    stepC s L = step s L ∧ ∀ x ∈ step s L, x ≤ B := by
  have hρ := at16_le s hs
  have he : ∀ e ∈ L, fits e = true ∧ bnd e ≤ B := by
    intro e hm
    have := List.all_eq_true.1 (band_r hL) e hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  refine ⟨?_, ?_⟩
  · apply List.map_congr_left
    intro e hm
    obtain ⟨hf, hb⟩ := he e hm
    obtain ⟨ec, eb⟩ := evalC_eq _ hρ e hf
    rw [ec]
    apply Nat.mod_eq_of_lt
    have : B < 2 ^ 32 := by decide
    omega
  · intro x hx
    obtain ⟨e, hm, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hf, hb⟩ := he e hm
    exact Nat.le_trans (evalC_eq _ hρ e hf).2 hb

theorem runC_eq : ∀ (ls : List Layer), ls.all layerOK = true →
    ∀ s : List Nat, (∀ x ∈ s, x ≤ B) → runC s ls = run s ls
  | [], _, _, _ => rfl
  | L :: ls, h, s, hs => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨e1, e2⟩ := stepC_eq s hs L h.1
    show runC (stepC s L) ls = run (step s L) ls
    rw [e1]
    exact runC_eq ls h.2 _ e2

/-- **Avon's C computes the specification**: on every state of sixteen
    `uint32_t` values, the printed program, run with C's arithmetic, gives
    `permute`. -/
theorem permuteC (s : List Nat) (hs : s.length = 16) (hb : ∀ x ∈ s, x ≤ B) :
    runC s prog = permute s := by
  rw [runC_eq prog prog_ok s hb, run_prog s hs]

-- ---------------------------------------------------------------------------
-- The printer
-- ---------------------------------------------------------------------------

/-- One line of C per constructor; `evalC` is what each line computes. -/
def cExpr : Ex → String
  | .var i => s!"(uint64_t)s[{i}]"
  | .lit n => s!"UINT64_C({n})"
  | .add a b => s!"({cExpr a} + {cExpr b})"
  | .mul a b => s!"({cExpr a} * {cExpr b})"
  | .md a => s!"({cExpr a} % UINT64_C({p}))"
  | .sbox a => s!"av_p2_sbox({cExpr a})"

/-- A layer's body: every result from the old state, then the new
    state. -/
def cBody (L : Layer) : String :=
  let ts := (L.zipIdx).map fun (e, i) => s!"    t[{i}] = {cExpr e};\n"
  "    uint64_t t[16];\n" ++ String.join ts ++
    "    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];\n"

/-- The distinct layers, each printed once, and the program as calls in
    order. -/
def header : String := Id.run do
  let mut bodies : Array String := #[]
  let mut calls : Array Nat := #[]
  for L in prog do
    let b := cBody L
    match bodies.findIdx? (· == b) with
    | some k => calls := calls.push k
    | none => calls := calls.push bodies.size; bodies := bodies.push b
  let fns := (bodies.toList.zipIdx).map fun (b, k) =>
    s!"static void av_p2_layer{k}(uint32_t s[16]) \{\n{b}}\n\n"
  let body := String.join (calls.toList.map fun k => s!"    av_p2_layer{k}(s);\n")
  return "/*  Poseidon2 over BabyBear, width 16, printed by lean/P2Prog.lean from\n" ++
    " *  the program Lean proves equal to lean-ski's specification\n" ++
    " *  (AvonP2.permuteC).  Generated; do not edit. */\n\n" ++
    "#include <stdint.h>\n\n" ++
    "/*  sboxC: x^7 mod p, each product below 2^62. */\n" ++
    "static uint64_t av_p2_sbox(uint64_t x) {\n" ++
    s!"    uint64_t a = x % UINT64_C({p});\n" ++
    s!"    uint64_t a2 = a * a % UINT64_C({p});\n" ++
    s!"    uint64_t a3 = a2 * a % UINT64_C({p});\n" ++
    s!"    uint64_t a6 = a3 * a3 % UINT64_C({p});\n" ++
    s!"    return a6 * a % UINT64_C({p});\n" ++
    "}\n\n" ++ String.join fns ++
    s!"/*  The program: {prog.length} layers, inputs any uint32_t. */\n" ++
    "static void av_p2_prog(uint32_t s[16]) {\n" ++ body ++ "}\n"

end AvonP2

#print axioms AvonP2.permuteC

def main (args : List String) : IO UInt32 := do
  match args with
  | [out] => IO.FS.writeFile out AvonP2.header; return 0
  | _ => IO.eprintln "usage: lake env lean --run P2Prog.lean OUT.h"; return 1
