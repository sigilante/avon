import Ski.BitArith
import Ski.Words
import Ski.Quote
import Ski.Fuel

/-!
# The interpreter jet: `whnfF`'s adequacy, proved

The interpreter jet (`docs/DESIGN.md` §7) runs a generated interpreter's
fuel loop natively.  It decodes the object term, reduces it in copy mode
with the fuel as its bound, and encodes the outcome.  Its licence is the
tower's adequacy theorem (§18.3): the self-interpreter, on an encoded
term, computes the encoding of the term's value.  This file proves that
theorem for `whnfF`, the 618-atom self-interpreter of the ski-in-ski
paper, which states it as Lemma `lem:step` and Theorem `thm:fuel` and
proves it on paper (`docs/LEAN-JETS.md` §8).

* **The pins.**  `whnfPin` is the conformance dictionary's `whnfF`, and
  `sPin` … `consPin` are its constructors; `main` prints them, and
  `tests/interp_lean_check.sh` requires each to be the dictionary's term,
  byte for byte, and `interpreters.tsv`'s `whnfF` core to be keyed by it.
  Each recursive function is `Ycomb` over a generator, and the generators
  reassemble the 618 atoms exactly (`whnf_pin`).  The object type's
  constructors are lean-ski's `quoteT` encoding (`pins_compiled`).
* **The pieces**, each by symbolic runs that the kernel checks, as in
  `lean/Words.lean`, with each function's callees as variables:
  - `sp_spec`: the spine walker passes the head leaf's continuation the
    encoded arguments, first first;
  - `rb_spec`: the rebuilder reassembles a head and its arguments;
  - `stepS_spec`, `stepK_spec`, `stepI_spec`: each arm contracts its rule
    with enough arguments and answers `Nothing` short of them.
* **Step adequacy** (`step_spec`): `step ⟨M⟩` reduces to `Nothing` if `M`
  is in weak head normal form, and to `Just ⟨M'⟩` if `M` contracts its
  head redex to `M'`, as lean-ski's `step?` says (`step?_spine`).
* **Fuel adequacy** (`whnfF_adequate`): `whnfF ⟨k⟩ ⟨M⟩` reduces to the
  encoding of lean-ski's `evalF k M`, `Just` the weak head normal form
  reached within `k` step-attempts and `Nothing` otherwise.  That is the
  paper's Theorem `thm:fuel`, both cases at once, and the outcome the jet
  produces.
* **Why the jet reads by structure** (`lookalike_probes_as_S`,
  `lookalike_answers_apart`): `S (K ⟨S⟩) I` behaves as `⟨S⟩` on every
  argument, so a probe reads it as `S`, but `Just` of each has a different
  normal form.  Probing is sound up to extensional equality only, and the
  theorem above is about the encodings themselves.

**What stays trusted:** that the jet's copy-mode run computes `evalF`:
`reduce.c`'s copy mode as `step?`, one fuel unit per step-attempt
(`tests/test_interp.c` and the conformance fuel cases test it); the
reading of the datum by structure and the encoding of the outcome; and residual jets
inside the object run keeping copy-mode counts (§6.5).  The four other
cores the jet serves, `wf5Abs`, `wf5Omg`, `wfQ` and `wfN`, are not
proved.

Run from lean-ski: `cd ~/Code/ski/lean-ski && lake env lean --run
~/avon/lean/Interp.lean OUT`.  The kernel checks the theorems as the file
elaborates; `main` writes the pins to `OUT`.
-/

open Term BitArith

namespace AvonInterp

-- ---------------------------------------------------------------------------
-- The pins: the dictionary's terms, and each function's generator
-- ---------------------------------------------------------------------------

/-- `rb`, under Y. -/
def rbG : OTerm :=
  .S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ .I)) ⬝ₒ .K)))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K))) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ .K))) ⬝ₒ (.K ⬝ₒ (.var 20))))

/-- `sp`, under Y. -/
def spG : OTerm :=
  .S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ .K) ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ .I)) ⬝ₒ .K)))))) ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ .I)) ⬝ₒ .K)))))) ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ .I)) ⬝ₒ .K)))))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K)))))) ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.var 22))) ⬝ₒ .K)))))

/-- `stepS`. -/
def stepSO : OTerm :=
  .S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ .K)) ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ .K)))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ .K)))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.var 21)))))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.var 23)))))) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.var 20)))) ⬝ₒ (.var 20))))) ⬝ₒ (.K ⬝ₒ (.var 20))))))))))

/-- `stepK`. -/
def stepKO : OTerm :=
  .S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ .K)) ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ .K)))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.var 21)))) ⬝ₒ (.var 23))))))

/-- `stepI`. -/
def stepIO : OTerm :=
  .S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ .K)) ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.var 21)))) ⬝ₒ (.var 23)))

/-- `step`. -/
def stepO : OTerm :=
  .S ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.var 24) ⬝ₒ (.K ⬝ₒ .K)) ⬝ₒ (.K ⬝ₒ (.var 25))) ⬝ₒ (.K ⬝ₒ (.var 26))) ⬝ₒ (.K ⬝ₒ (.var 27))

/-- `loop`, under Y. -/
def loopG : OTerm :=
  .S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ .K)))))) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .S) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.var 28) ⬝ₒ (.var 21)))))) ⬝ₒ .K))

def appPin : Term := S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)))) ⬝ (K ⬝ K))))

def justPin : Term := S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)

def consPin : Term := S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)))) ⬝ (K ⬝ K))

def sPin : Term := S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ K)

def kPin : Term := K ⬝ (S ⬝ (K ⬝ K) ⬝ K)

def iPin : Term := K ⬝ (K ⬝ K)

/-- The 618-atom `whnfF`, as the dictionary pins it. -/
def whnfPin : Term :=
  S ⬝ (K ⬝ (S ⬝ I ⬝ I)) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ K) ⬝ (K ⬝ (S ⬝ I ⬝ I))) ⬝ (S ⬝ (K ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ I ⬝ (K ⬝ K)))))) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (S ⬝ (S ⬝ (S ⬝ (S ⬝ (S ⬝ (K ⬝ (S ⬝ I ⬝ I)) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ K) ⬝ (K ⬝ (S ⬝ I ⬝ I))) ⬝ (S ⬝ (K ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ K) ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)))))) ⬝ (K ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)))))) ⬝ (K ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)))))))) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ S))) ⬝ (S ⬝ (K ⬝ K)))))) ⬝ (K ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ (S ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)))) ⬝ (K ⬝ K))))) ⬝ K))))))) ⬝ (K ⬝ K)) ⬝ (K ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ K)) ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ K)))) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ K)))))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K))))))))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ I ⬝ I)) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ K) ⬝ (K ⬝ (S ⬝ I ⬝ I))) ⬝ (S ⬝ (K ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ K))) ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)))) ⬝ (K ⬝ K))))))))))))))) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)))) ⬝ (K ⬝ K)))))))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)))) ⬝ (K ⬝ K))))))))) ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)))) ⬝ (K ⬝ K))))))))))))))))) ⬝ (K ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ K)) ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ K)))) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K))))) ⬝ (S ⬝ (K ⬝ (S ⬝ I ⬝ I)) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ K) ⬝ (K ⬝ (S ⬝ I ⬝ I))) ⬝ (S ⬝ (K ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ K))) ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)))) ⬝ (K ⬝ K)))))))))))))))))) ⬝ (K ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ K)) ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K))))) ⬝ (S ⬝ (K ⬝ (S ⬝ I ⬝ I)) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ K) ⬝ (K ⬝ (S ⬝ I ⬝ I))) ⬝ (S ⬝ (K ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ K))) ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)))) ⬝ (K ⬝ K))))))))))))))) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K))))))) ⬝ K)))


-- ---------------------------------------------------------------------------
-- The program, reassembled
-- ---------------------------------------------------------------------------

/-- Each function's callees: `App`, `Just`, `cons`, then `rb` and `sp`. -/
def envA : Nat → Term := fun i =>
  if i = 20 then appPin else if i = 21 then justPin else if i = 22 then consPin else K

def rbT : Term := Ycomb ⬝ rbG.close envA
def spT : Term := Ycomb ⬝ spG.close envA

def envB : Nat → Term := fun i => if i = 23 then rbT else if i = 24 then spT else envA i

def stepST : Term := stepSO.close envB
def stepKT : Term := stepKO.close envB
def stepIT : Term := stepIO.close envB

def envC : Nat → Term := fun i =>
  if i = 25 then stepST else if i = 26 then stepKT else if i = 27 then stepIT else envB i

def stepT : Term := stepO.close envC

def env : Nat → Term := fun i => if i = 28 then stepT else envC i

def loopT : Term := Ycomb ⬝ loopG.close env

/-- **The generators reassemble the pinned `whnfF`**, all 618 atoms. -/
theorem whnf_pin : whnfPin = loopT := by decide

/-- The object type's constructors are the encoding of lean-ski's `quoteT`,
    and `Just` and `cons` are the compiled `Just` and `Cons`. -/
theorem pins_compiled :
    sPin = toTerm (ctorO 0 0 4) ∧ kPin = toTerm (ctorO 0 1 4) ∧ iPin = toTerm (ctorO 0 2 4) ∧
    appPin = toTerm (ctorO 2 3 4) ∧ justPin = toTerm (ctorO 1 1 2) ∧
    consPin = toTerm (ctorO 2 1 2) := by decide

-- ---------------------------------------------------------------------------
-- Curry's knot, and symbolic runs
-- ---------------------------------------------------------------------------

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

/-- Variables `0 .. xs.length - 1` closed to `xs`, the rest by `env`. -/
def sig (xs : List Term) (i : Nat) : Term := xs.getD i (env i)

-- ---------------------------------------------------------------------------
-- Encodings
-- ---------------------------------------------------------------------------

/-- A Scott list of terms (`nil` is `K`). -/
def encL : List Term → Term
  | [] => K
  | x :: r => consPin ⬝ x ⬝ encL r

/-- `maybe`: `Nothing` is `K`, `Just t` the encoding of `t` under `Just`. -/
def encOpt : Option Term → Term
  | none => K
  | some t => justPin ⬝ quoteT t

theorem quoteT_S : quoteT .S = sPin := pins_compiled.1.symm
theorem quoteT_K : quoteT .K = kPin := pins_compiled.2.1.symm
theorem quoteT_I : quoteT .I = iPin := pins_compiled.2.2.1.symm
theorem quoteT_app (f a : Term) : quoteT (f ⬝ a) = appPin ⬝ quoteT f ⬝ quoteT a := by
  rw [show quoteT (f ⬝ a) = toTerm (ctorO 2 3 4) ⬝ quoteT f ⬝ quoteT a from rfl,
    pins_compiled.2.2.2.1]

/-- A term's head leaf and its arguments, first first. -/
def headOf : Term → Term
  | .app f _ => headOf f
  | t => t

def argsOf : Term → List Term
  | .app f x => argsOf f ++ [x]
  | _ => []

-- ---------------------------------------------------------------------------
-- sp: the spine walker
-- ---------------------------------------------------------------------------

/-- The continuation the head leaf selects. -/
def sel (h cS cK cI : Term) : Term :=
  match h with
  | .S => cS | .K => cK | .I => cI | _ => K

/-- **The spine walker decomposes as the host does**: `sp ⟨M⟩ acc` passes
    the continuation of `M`'s head leaf its arguments, encoded, first
    first, before `acc`. -/
theorem sp_spec (cS cK cI : Term) : ∀ (M : Term) (acc : List Term),
    WSteps (knot (spG.close envA) ⬝ quoteT M ⬝ encL acc ⬝ cS ⬝ cK ⬝ cI)
      (sel (headOf M) cS cK cI ⬝ encL ((argsOf M).map quoteT ++ acc))
  | .S, acc => by
    have h := run (n := 100) (t := spG ⬝ₒ .var 0 ⬝ₒ sPin.toO ⬝ₒ .var 1 ⬝ₒ .var 2 ⬝ₒ .var 3 ⬝ₒ .var 4)
      (u := .var 2 ⬝ₒ .var 1) (by decide) (sig [knot (spG.close envA), encL acc, cS, cK, cI])
    rw [quoteT_S]
    exact (((((knot_unroll _).left _).left _).left _).left _).left _ |>.trans h
  | .K, acc => by
    have h := run (n := 100) (t := spG ⬝ₒ .var 0 ⬝ₒ kPin.toO ⬝ₒ .var 1 ⬝ₒ .var 2 ⬝ₒ .var 3 ⬝ₒ .var 4)
      (u := .var 3 ⬝ₒ .var 1) (by decide) (sig [knot (spG.close envA), encL acc, cS, cK, cI])
    rw [quoteT_K]
    exact (((((knot_unroll _).left _).left _).left _).left _).left _ |>.trans h
  | .I, acc => by
    have h := run (n := 100) (t := spG ⬝ₒ .var 0 ⬝ₒ iPin.toO ⬝ₒ .var 1 ⬝ₒ .var 2 ⬝ₒ .var 3 ⬝ₒ .var 4)
      (u := .var 4 ⬝ₒ .var 1) (by decide) (sig [knot (spG.close envA), encL acc, cS, cK, cI])
    rw [quoteT_I]
    exact (((((knot_unroll _).left _).left _).left _).left _).left _ |>.trans h
  | .app f x, acc => by
    have h := run (n := 100)
      (t := spG ⬝ₒ .var 0 ⬝ₒ (appPin.toO ⬝ₒ .var 5 ⬝ₒ .var 6) ⬝ₒ .var 1 ⬝ₒ .var 2 ⬝ₒ .var 3 ⬝ₒ .var 4)
      (u := .var 0 ⬝ₒ .var 5 ⬝ₒ (.var 22 ⬝ₒ .var 6 ⬝ₒ .var 1) ⬝ₒ .var 2 ⬝ₒ .var 3 ⬝ₒ .var 4)
      (by decide) (sig [knot (spG.close envA), encL acc, cS, cK, cI, quoteT f, quoteT x])
    rw [quoteT_app]
    have ih := sp_spec cS cK cI f (quoteT x :: acc)
    have e : (argsOf (f ⬝ x)).map quoteT ++ acc = (argsOf f).map quoteT ++ (quoteT x :: acc) := by
      simp [argsOf]
    rw [show headOf (f ⬝ x) = headOf f from rfl, e]
    exact ((((((knot_unroll _).left _).left _).left _).left _).left _ |>.trans h).trans ih

-- ---------------------------------------------------------------------------
-- rb: the rebuilder
-- ---------------------------------------------------------------------------

/-- **The rebuilder reassembles**: `rb ⟨h⟩ [⟨x1⟩ … ⟨xn⟩]` is `⟨h x1 … xn⟩`. -/
theorem rb_spec : ∀ (xs : List Term) (h : Term),
    WSteps (knot (rbG.close envA) ⬝ quoteT h ⬝ encL (xs.map quoteT)) (quoteT (xs.foldl (· ⬝ ·) h))
  | [], h => by
    have r := run (n := 100) (t := rbG ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ .K) (u := .var 1) (by decide)
      (sig [knot (rbG.close envA), quoteT h])
    exact (((knot_unroll _).left _).left _).trans r
  | x :: xs, h => by
    have r := run (n := 100) (t := rbG ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ (consPin.toO ⬝ₒ .var 2 ⬝ₒ .var 3))
      (u := .var 0 ⬝ₒ (.var 20 ⬝ₒ .var 1 ⬝ₒ .var 2) ⬝ₒ .var 3) (by decide)
      (sig [knot (rbG.close envA), quoteT h, quoteT x, encL (xs.map quoteT)])
    have ih := rb_spec xs (h ⬝ x)
    rw [quoteT_app] at ih
    exact ((((knot_unroll _).left _).left _).trans r).trans ih

theorem rbT_spec (xs : List Term) (h : Term) :
    WSteps (rbT ⬝ quoteT h ⬝ encL (xs.map quoteT)) (quoteT (xs.foldl (· ⬝ ·) h)) :=
  (((ycomb_knot _).left _).left _).trans (rb_spec xs h)

-- ---------------------------------------------------------------------------
-- The three step arms
-- ---------------------------------------------------------------------------

/-- One head step on a leaf and its arguments: `I x`, `K x y`, `S x y z`,
    the rest of the spine rebuilt over the result; `none` short of the
    arity. -/
def spineStep : Term → List Term → Option Term
  | .I, x :: r => some (r.foldl (· ⬝ ·) x)
  | .K, x :: _ :: r => some (r.foldl (· ⬝ ·) x)
  | .S, x :: y :: z :: r => some (r.foldl (· ⬝ ·) (x ⬝ z ⬝ (y ⬝ z)))
  | _, _ => none

theorem just_congr {t u : Term} (h : WSteps t u) : WSteps (justPin ⬝ t) (justPin ⬝ u) :=
  WSteps.right _ h

theorem stepI_spec : ∀ args : List Term,
    WSteps (stepIT ⬝ encL (args.map quoteT)) (encOpt (spineStep .I args))
  | [] => run (n := 100) (t := stepIO ⬝ₒ .K) (u := .K) (by decide) (sig [])
  | x :: r => by
    have h := run (n := 100) (t := stepIO ⬝ₒ (consPin.toO ⬝ₒ .var 1 ⬝ₒ .var 2))
      (u := .var 21 ⬝ₒ (.var 23 ⬝ₒ .var 1 ⬝ₒ .var 2)) (by decide)
      (sig [K, quoteT x, encL (r.map quoteT)])
    exact h.trans (just_congr (rbT_spec r x))

theorem stepK_spec : ∀ args : List Term,
    WSteps (stepKT ⬝ encL (args.map quoteT)) (encOpt (spineStep .K args))
  | [] => run (n := 100) (t := stepKO ⬝ₒ .K) (u := .K) (by decide) (sig [])
  | [x] => run (n := 100) (t := stepKO ⬝ₒ (consPin.toO ⬝ₒ .var 1 ⬝ₒ .K)) (u := .K) (by decide)
      (sig [K, quoteT x])
  | x :: y :: r => by
    have h := run (n := 100)
      (t := stepKO ⬝ₒ (consPin.toO ⬝ₒ .var 1 ⬝ₒ (consPin.toO ⬝ₒ .var 2 ⬝ₒ .var 3)))
      (u := .var 21 ⬝ₒ (.var 23 ⬝ₒ .var 1 ⬝ₒ .var 3)) (by decide)
      (sig [K, quoteT x, quoteT y, encL (r.map quoteT)])
    exact h.trans (just_congr (rbT_spec r x))

theorem stepS_spec : ∀ args : List Term,
    WSteps (stepST ⬝ encL (args.map quoteT)) (encOpt (spineStep .S args))
  | [] => run (n := 100) (t := stepSO ⬝ₒ .K) (u := .K) (by decide) (sig [])
  | [x] => run (n := 100) (t := stepSO ⬝ₒ (consPin.toO ⬝ₒ .var 1 ⬝ₒ .K)) (u := .K) (by decide)
      (sig [K, quoteT x])
  | [x, y] => run (n := 100)
      (t := stepSO ⬝ₒ (consPin.toO ⬝ₒ .var 1 ⬝ₒ (consPin.toO ⬝ₒ .var 2 ⬝ₒ .K))) (u := .K) (by decide)
      (sig [K, quoteT x, quoteT y])
  | x :: y :: z :: r => by
    have h := run (n := 100)
      (t := stepSO ⬝ₒ (consPin.toO ⬝ₒ .var 1 ⬝ₒ (consPin.toO ⬝ₒ .var 2 ⬝ₒ
        (consPin.toO ⬝ₒ .var 3 ⬝ₒ .var 4))))
      (u := .var 21 ⬝ₒ (.var 23 ⬝ₒ (.var 20 ⬝ₒ (.var 20 ⬝ₒ .var 1 ⬝ₒ .var 3) ⬝ₒ
        (.var 20 ⬝ₒ .var 2 ⬝ₒ .var 3)) ⬝ₒ .var 4)) (by decide)
      (sig [K, quoteT x, quoteT y, quoteT z, encL (r.map quoteT)])
    have hr := rbT_spec r (x ⬝ z ⬝ (y ⬝ z))
    rw [quoteT_app, quoteT_app, quoteT_app] at hr
    exact h.trans (just_congr hr)

-- ---------------------------------------------------------------------------
-- step: lean-ski's head step, on the spine
-- ---------------------------------------------------------------------------

theorem spine_eq : ∀ M : Term, M = (argsOf M).foldl (· ⬝ ·) (headOf M)
  | .S => rfl
  | .K => rfl
  | .I => rfl
  | .app f x => by
    show f ⬝ x = (argsOf f ++ [x]).foldl (· ⬝ ·) (headOf f)
    rw [List.foldl_append, ← spine_eq f]; rfl

theorem headOf_leaf : ∀ M : Term, headOf M = .S ∨ headOf M = .K ∨ headOf M = .I
  | .S => .inl rfl
  | .K => .inr (.inl rfl)
  | .I => .inr (.inr rfl)
  | .app f _ => headOf_leaf f

theorem spineStep_snoc {h : Term} {as : List Term} {r : Term} (hs : spineStep h as = some r)
    (x : Term) : spineStep h (as ++ [x]) = some (r ⬝ x) := by
  cases h <;> rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
    simp_all [spineStep, List.foldl_append]

/-- **lean-ski's head step is the step on the spine**: `step?` contracts
    the head redex, `I x`, `K x y` or `S x y z`, rebuilding the spine over
    the result, or finds none. -/
theorem step?_spine : ∀ M : Term, step? M = spineStep (headOf M) (argsOf M)
  | .S => rfl
  | .K => rfl
  | .I => rfl
  | .app f x => by
    have ih := step?_spine f
    show step? (f ⬝ x) = spineStep (headOf f) (argsOf f ++ [x])
    cases hsf : spineStep (headOf f) (argsOf f) with
    | some r =>
      rw [spineStep_snoc hsf]
      simp [step?, ih, hsf]
    | none =>
      have hstep : step? f = none := ih.trans hsf
      have hf := spine_eq f
      have hl := headOf_leaf f
      generalize headOf f = h at hf hsf hl ⊢
      generalize argsOf f = as at hf hsf ⊢
      subst hf
      rcases hl with rfl | rfl | rfl <;>
        rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
        simp only [spineStep, reduceCtorEq] at hsf <;>
        simp [step?, spineStep]
termination_by M => sizeOf M

theorem stepT_arms (M : Term) :
    WSteps (stepT ⬝ quoteT M)
      (sel (headOf M) stepST stepKT stepIT ⬝ encL ((argsOf M).map quoteT)) := by
  have h := run (n := 100) (t := stepO ⬝ₒ .var 1)
    (u := .var 24 ⬝ₒ .var 1 ⬝ₒ .K ⬝ₒ .var 25 ⬝ₒ .var 26 ⬝ₒ .var 27) (by decide) (sig [K, quoteT M])
  have hk := (((((ycomb_knot (spG.close envA)).left (quoteT M)).left (encL [])).left stepST).left
    stepKT).left stepIT
  have hs := sp_spec stepST stepKT stepIT M []
  rw [List.append_nil] at hs
  exact h.trans (hk.trans hs)

/-- **Step adequacy** (the paper's Lemma `lem:step`): `step ⟨M⟩` is
    `Nothing` if `M` is in weak head normal form, and `Just ⟨M'⟩` if `M`
    contracts its head redex to `M'`, as lean-ski's `step?` says. -/
theorem step_spec (M : Term) : WSteps (stepT ⬝ quoteT M) (encOpt (step? M)) := by
  refine (stepT_arms M).trans ?_
  rw [step?_spine]
  rcases headOf_leaf M with h | h | h <;> rw [h]
  · exact stepS_spec _
  · exact stepK_spec _
  · exact stepI_spec _

-- ---------------------------------------------------------------------------
-- The fuel loop
-- ---------------------------------------------------------------------------

theorem loop_spec : ∀ (k : Nat) (M : Term),
    WSteps (knot (loopG.close env) ⬝ encNat k ⬝ quoteT M) (encOpt (evalF k M))
  | 0, M => by
    have h := run (n := 100) (t := loopG ⬝ₒ .var 0 ⬝ₒ .K ⬝ₒ .var 1) (u := .K) (by decide)
      (sig [knot (loopG.close env), quoteT M])
    exact (((knot_unroll _).left _).left _).trans h
  | k + 1, M => by
    have h := run (n := 100) (t := loopG ⬝ₒ .var 0 ⬝ₒ (Scott.Suc.toO ⬝ₒ .var 2) ⬝ₒ .var 1)
      (u := .var 28 ⬝ₒ .var 1 ⬝ₒ (.var 21 ⬝ₒ .var 1) ⬝ₒ (.var 0 ⬝ₒ .var 2)) (by decide)
      (sig [knot (loopG.close env), quoteT M, encNat k])
    have h0 := (((knot_unroll (loopG.close env)).left (encNat (k + 1))).left (quoteT M)).trans h
    refine h0.trans ((((step_spec M).left _).left _).trans ?_)
    show WSteps (encOpt (step? M) ⬝ (justPin ⬝ quoteT M) ⬝ (knot (loopG.close env) ⬝ encNat k))
      (encOpt (match step? M with | none => some M | some t' => evalF k t'))
    cases hs : step? M with
    | none => exact .single (.K _ _)
    | some M' =>
      have hj := run (n := 20) (t := justPin.toO ⬝ₒ .var 1 ⬝ₒ .var 2 ⬝ₒ .var 3)
        (u := .var 3 ⬝ₒ .var 1) (by decide)
        (sig [K, quoteT M', justPin ⬝ quoteT M, knot (loopG.close env) ⬝ encNat k])
      exact hj.trans (loop_spec k M')

/-- **Fuel adequacy for `whnfF`** (the paper's Theorem `thm:fuel`), for the
    618-atom term the dictionary pins: given fuel `k` and an encoded term
    `M`, `whnfF` reduces to the encoding of lean-ski's `evalF k M`, `Just`
    the weak head normal form `M` reaches within `k` step-attempts and
    `Nothing` otherwise. -/
theorem whnfF_adequate (k : Nat) (M : Term) :
    WSteps (whnfPin ⬝ encNat k ⬝ quoteT M) (encOpt (evalF k M)) := by
  rw [whnf_pin]
  exact (((ycomb_knot _).left _).left _).trans (loop_spec k M)

-- ---------------------------------------------------------------------------
-- Why the jet reads by structure: a look-alike the probes cannot tell
-- ---------------------------------------------------------------------------

/-- A weak redex at the root. -/
def isRedex : Term → Bool
  | .app (.app (.app .S _) _) _ => true
  | .app (.app .K _) _ => true
  | .app .I _ => true
  | _ => false

/-- A weak normal form: no redex anywhere. -/
def wnormal : Term → Bool
  | .app f x => !isRedex (.app f x) && wnormal f && wnormal x
  | _ => true

theorem wnormal_no_step {t u : Term} (h : WStep t u) : wnormal t = false := by
  induction h with
  | S f g x => simp [wnormal, isRedex]
  | K x y => simp [wnormal, isRedex]
  | I x => simp [wnormal, isRedex]
  | left x _ ih => simp [wnormal, ih]
  | right f _ ih => simp [wnormal, ih]

/-- A weak normal form reduces only to itself (Hindley and Seldin,
    Exercise 2.34(c)). -/
theorem wnormal_steps {t u : Term} (hn : wnormal t = true) (h : WSteps t u) : u = t := by
  cases h with
  | refl => rfl
  | step s _ => exact absurd (wnormal_no_step s) (by simp [hn])

/-- Distinct weak normal forms are not convertible: they have no common
    reduct (Church–Rosser; Hindley and Seldin, Corollary 2.32.3). -/
theorem wnormal_apart {a b : Term} (ha : wnormal a = true) (hb : wnormal b = true)
    (hab : a ≠ b) : ¬ ∃ w, WSteps a w ∧ WSteps b w := by
  rintro ⟨w, haw, hbw⟩
  exact hab ((wnormal_steps ha haw).symm.trans (wnormal_steps hb hbw))

/-- The look-alike datum `S (K ⟨S⟩) I`: the η-expansion of the object
    `S` constructor. -/
def lookalike : Term := S ⬝ (K ⬝ sPin) ⬝ I

/-- **The probes cannot tell it from `⟨S⟩`.**  Applied to any term it
    reduces to `⟨S⟩` applied to that term, so on fresh atoms, the markers
    a probe applies, it behaves as `⟨S⟩` does: the two are extensionally
    equal (Hindley and Seldin, Chapter 8).  A decoder that probes reads it
    as `S`. -/
theorem lookalike_probes_as_S (x : Term) : WSteps (lookalike ⬝ x) (sPin ⬝ x) :=
  .step (.S _ _ _) (.step (.left _ (.K _ _)) (.single (.right _ (.I _))))

/-- `Just`, on any term, reduces to its normal form `K (S I (K x))`. -/
theorem just_nf (x : Term) : WSteps (justPin ⬝ x) (K ⬝ (S ⬝ I ⬝ (K ⬝ x))) :=
  run (n := 20) (t := justPin.toO ⬝ₒ .var 1) (u := .K ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ .var 1)))
    (by decide) (sig [K, x])

/-- **But the answers differ.**  `Just` the look-alike, which the unjetted
    interpreter answers at fuel 1 (`tests/test_interp.c`), and `Just ⟨S⟩`,
    which a probing jet answered, are not convertible: their normal forms
    differ.  So a jet's licence, weak equality, does not follow from a
    probe's reading, extensional equality; the jet reads its datum by
    structure (`docs/LEAN-JETS.md` §8). -/
theorem lookalike_answers_apart :
    ¬ ∃ w, WSteps (justPin ⬝ lookalike) w ∧ WSteps (justPin ⬝ sPin) w := by
  rintro ⟨w, h1, h2⟩
  obtain ⟨v1, hv1, hw1⟩ := church_rosser (just_nf lookalike) h1
  obtain ⟨v2, hv2, hw2⟩ := church_rosser (just_nf sPin) h2
  obtain ⟨v, hv1', hv2'⟩ := church_rosser hw1 hw2
  have n1 : wnormal (K ⬝ (S ⬝ I ⬝ (K ⬝ lookalike))) = true := by decide
  have n2 : wnormal (K ⬝ (S ⬝ I ⬝ (K ⬝ sPin))) = true := by decide
  exact wnormal_apart n1 n2 (by decide) ⟨v, hv1.trans hv1', hv2.trans hv2'⟩

-- ---------------------------------------------------------------------------
-- The printer
-- ---------------------------------------------------------------------------

/-- Avon's printed form, as the dictionary writes its terms. -/
def pr : Term → String
  | .S => "S" | .K => "K" | .I => "I"
  | .app f x => pr f ++ " " ++ (match x with | .app _ _ => "(" ++ pr x ++ ")" | _ => pr x)

/-- The pins, one per line, by the dictionary's names for them. -/
def pins : String :=
  String.join ([("whnfF", whnfPin), ("S", sPin), ("K", kPin), ("I", iPin), ("App", appPin),
    ("Just", justPin), ("Nothing", encOpt none), ("cons", consPin),
    ("Zero", encNat 0), ("Suc", Scott.Suc)].map fun (n, t) => n ++ "\t" ++ pr t ++ "\n")

end AvonInterp

#print axioms AvonInterp.whnfF_adequate
#print axioms AvonInterp.step_spec
#print axioms AvonInterp.whnf_pin
#print axioms AvonInterp.pins_compiled
#print axioms AvonInterp.lookalike_probes_as_S
#print axioms AvonInterp.lookalike_answers_apart

def main (args : List String) : IO UInt32 := do
  match args with
  | [out] => IO.FS.writeFile out AvonInterp.pins; return 0
  | _ => IO.eprintln "usage: lake env lean --run Interp.lean OUT"; return 1
