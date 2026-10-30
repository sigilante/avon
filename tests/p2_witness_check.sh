#!/usr/bin/env bash
# The composed witness with the Poseidon2 jet (lean-ski's P2Jet.p2Row).
#
# For lean-ski's statement `p2pre h` ("sixteen 31-bit values whose
# Poseidon2 permutation begins with h") and its witness, test vector 1:
#
#   1. lean-ski writes the statement and the witness (`lake exe composed
#      emit-p2`);
#   2. build/avon witness --statement writes the table: the statement's
#      heap with the bits and region filled in, the run with the jet's step
#      at its atom, padded to the statement's heights;
#   3. lean-ski's prover, ski-air compp-prove, runs the same witness, proves
#      and verifies, and writes its own table; Avon's must be byte-identical;
#   4. `ski-air compp-prove-table` proves Avon's table, and `ski-air
#      compp-verify` checks the proof from the statement alone
#      (Circuit.p2preExport_sound: the memory holds a preimage of h);
#   5. a witness with one bit flipped does not satisfy the statement, and
#      Avon refuses it as ski-air does;
#   6. the hidden hand-off (`lake exe composed emit-handoff`): for each of
#      the two `p2commit c pat` statements Avon's table is byte-identical to
#      ski-air's, `compp-prove-table` proves it, and `ski-air compp-chain`
#      verifies the two proofs as a chain (lean-ski's
#      Circuit.p2commit_chainB); a header with a 495-entry pattern is
#      refused;
#   7. two jet calls in one statement, from lean-ski #65 on (`lake exe composed emit-p2chain`):
#      for `p2chain h`, "the permutation of the permutation of my values
#      begins with h", Avon's table, with the jet on the comb at J and on
#      the first call's outputs, on the stack, at J+1, is byte-identical to
#      ski-air's, and `compp-prove-table` and `compp-verify` prove and check
#      it (lean-ski's Circuit.p2chainExport_sound); a flipped bit is refused;
#   8. the native Poseidon2 jet: for each test vector x,
#      `avon reduce --p2=P.dag` on lean-ski's `P ⬝ stateN x` (`lake exe
#      p2run`) reaches `stateN (permute x)`, Plonky3's output, in one step,
#      one permutation run natively (lean-ski's P_specN licenses it); and
#      the chain P (P (P x)) of test vector 1, one shared P (`p2run chain`),
#      reaches `stateN (permute^3 x)` in three steps, three run natively,
#      none declined;
#   9. the permutation itself: lean/P2Prog.lean, checked against lean-ski,
#      proves its program equal to the specification with C's arithmetic
#      (AvonP2.permuteC, on lean-ski's axioms only) and prints it; the print
#      must be src/p2_prog.h, byte for byte.
#
# Avon and ski-air read a false bit only as the cell A 0 1; lean-ski's
# p2Row also accepts any A f x with f at K and x at I.  The narrower reading
# costs completeness only: the statement's witness writes A 0 1.
#
# Run from the repository root after `make`.  LEAN_SKI defaults to
# ~/Code/ski/lean-ski.  One heavy job at a time: nothing here runs in
# parallel.

set -euo pipefail

export LEAN_SKI=${LEAN_SKI:-$HOME/Code/ski/lean-ski}   # ski-air finds Lean through it
. tests/pins.sh
pin_check lean-ski "$LEAN_SKI" "$LEAN_SKI_PIN"
AVON=${AVON:-build/avon}
OUT=${OUT:-build/p2-witness}
AVON=$(cd "$(dirname "$AVON")" && pwd)/$(basename "$AVON")

rm -rf "$OUT"
mkdir -p "$OUT/stmt" "$OUT/avon" "$OUT/ski-air" "$OUT/proofs"
OUT=$(cd "$OUT" && pwd)
fail=0

echo "--- lean-ski: the statement p2pre h and its witness"
(cd "$LEAN_SKI" && lake build composed circuit > /dev/null && lake exe composed emit-p2 "$OUT/stmt")
stmt="$OUT/stmt/p2pre.public.txt"
wit="$OUT/stmt/p2pre.witness.txt"

echo "--- ski-air"
if [ -z "${SKI_AIR:-}" ]; then
    (cd "$LEAN_SKI/bench/plonky3" && cargo build --release --quiet)
    SKI_AIR="$LEAN_SKI/bench/plonky3/target/release/ski-air"
fi

echo "--- the witness"
"$AVON" witness --statement="$stmt" "$wit" > "$OUT/avon/table.txt" 2> "$OUT/avon/err.txt" \
    || { echo "FAIL: Avon: $(cat "$OUT/avon/err.txt")"; exit 1; }
echo "avon: $(cat "$OUT/avon/err.txt")"
"$SKI_AIR" compp-prove "$stmt" "$wit" "$OUT/proofs/ski-air.proof" --table="$OUT/ski-air/table.txt" | tail -n 1
if cmp -s "$OUT/avon/table.txt" "$OUT/ski-air/table.txt"; then
    echo "byte-identical to ski-air's table"
else
    echo "FAIL: Avon's table differs from ski-air's"
    fail=1
fi
"$SKI_AIR" compp-prove-table "$stmt" "$OUT/avon/table.txt" "$OUT/proofs/avon.proof" | tail -n 1 || fail=1
"$SKI_AIR" compp-verify "$stmt" "$OUT/proofs/avon.proof" || fail=1

echo "--- a witness that does not satisfy the statement"
awk 'NR == 1 { $0 = ($0 == "1") ? "0" : "1" } { print }' "$wit" > "$OUT/stmt/bad.witness.txt"
if "$AVON" witness --statement="$stmt" "$OUT/stmt/bad.witness.txt" > /dev/null 2> "$OUT/avon/bad.err"; then
    echo "FAIL: Avon wrote a table for a witness that does not satisfy the statement"
    fail=1
else
    echo "avon refuses: $(cat "$OUT/avon/bad.err")"
fi
if "$SKI_AIR" compp-prove "$stmt" "$OUT/stmt/bad.witness.txt" "$OUT/proofs/bad.proof" > /dev/null 2> "$OUT/ski-air/bad.err"; then
    echo "FAIL: ski-air proved a witness that does not satisfy the statement"
    fail=1
else
    echo "ski-air refuses: $(cat "$OUT/ski-air/bad.err")"
fi

echo "--- the hidden hand-off: two p2commit statements over one commitment"
(cd "$LEAN_SKI" && lake exe composed emit-handoff "$OUT/stmt" > /dev/null)
for n in handoff1 handoff2; do
    "$AVON" witness --statement="$OUT/stmt/$n.public.txt" "$OUT/stmt/handoff.witness.txt" > "$OUT/avon/$n.txt" \
        2> "$OUT/avon/$n.err" || { echo "FAIL: Avon ($n): $(cat "$OUT/avon/$n.err")"; fail=1; continue; }
    echo "avon ($n): $(cat "$OUT/avon/$n.err")"
    "$SKI_AIR" compp-prove "$OUT/stmt/$n.public.txt" "$OUT/stmt/handoff.witness.txt" "$OUT/proofs/$n.ski-air.proof" \
        --table="$OUT/ski-air/$n.txt" > /dev/null
    if cmp -s "$OUT/avon/$n.txt" "$OUT/ski-air/$n.txt"; then
        echo "$n: byte-identical to ski-air's table"
    else
        echo "FAIL: $n: Avon's table differs from ski-air's"
        fail=1
    fi
    "$SKI_AIR" compp-prove-table "$OUT/stmt/$n.public.txt" "$OUT/avon/$n.txt" "$OUT/proofs/$n.proof" | tail -n 1 | cut -c1-100 \
        || fail=1
done
# Avon's two proofs verify as a chain (lean-ski's Circuit.p2commit_chainB).
"$SKI_AIR" compp-chain "$OUT/stmt/handoff1.public.txt" "$OUT/proofs/handoff1.proof" \
    "$OUT/stmt/handoff2.public.txt" "$OUT/proofs/handoff2.proof" | tail -n 1 | grep '^CHAIN OK' || fail=1
# A p2commit header with a 495-entry pattern is no statement.
awk 'NR == 1 { n = split($0, w, " "); w[10] = substr(w[10], 2); s = w[1]; for (i = 2; i <= n; i++) s = s " " w[i]; $0 = s } { print }' \
    "$OUT/stmt/handoff1.public.txt" > "$OUT/stmt/short.public.txt"
if "$AVON" witness --statement="$OUT/stmt/short.public.txt" "$OUT/stmt/handoff.witness.txt" > /dev/null 2> "$OUT/avon/short.err"; then
    echo "FAIL: Avon read a p2commit header with a 495-entry pattern"
    fail=1
else
    echo "avon refuses a malformed p2commit header: $(cat "$OUT/avon/short.err")"
fi

echo "--- two jet calls: the statement p2chain h"
# lean-ski has p2chain from #65 on; at an earlier pin the section says so.
if ! grep -q 'emit-p2chain' "$LEAN_SKI/bench/Composed.lean"; then
    echo "SKIP: lean-ski at $(git -C "$LEAN_SKI" rev-parse --short HEAD) predates p2chain (lean-ski #65)"
else
    (cd "$LEAN_SKI" && lake exe composed emit-p2chain "$OUT/stmt" > /dev/null)
    cs="$OUT/stmt/p2chain.public.txt"
    cw="$OUT/stmt/p2chain.witness.txt"
    if "$AVON" witness --statement="$cs" "$cw" > "$OUT/avon/chain.txt" 2> "$OUT/avon/chain.err"; then
        echo "avon (p2chain): $(cat "$OUT/avon/chain.err")"
        "$SKI_AIR" compp-prove "$cs" "$cw" "$OUT/proofs/chain.ski-air.proof" --table="$OUT/ski-air/chain.txt" > /dev/null
        if cmp -s "$OUT/avon/chain.txt" "$OUT/ski-air/chain.txt"; then
            echo "p2chain: byte-identical to ski-air's table"
        else
            echo "FAIL: p2chain: Avon's table differs from ski-air's"
            fail=1
        fi
        "$SKI_AIR" compp-prove-table "$cs" "$OUT/avon/chain.txt" "$OUT/proofs/chain.proof" | tail -n 1 | cut -c1-100 || fail=1
        "$SKI_AIR" compp-verify "$cs" "$OUT/proofs/chain.proof" || fail=1
    else
        echo "FAIL: Avon (p2chain): $(cat "$OUT/avon/chain.err")"
        fail=1
    fi
    awk 'NR == 1 { $0 = ($0 == "1") ? "0" : "1" } { print }' "$cw" > "$OUT/stmt/chain-bad.witness.txt"
    if "$AVON" witness --statement="$cs" "$OUT/stmt/chain-bad.witness.txt" > /dev/null 2> "$OUT/avon/chain-bad.err"; then
        echo "FAIL: Avon wrote a p2chain table for a witness that does not satisfy it"
        fail=1
    else
        echo "avon refuses (p2chain): $(cat "$OUT/avon/chain-bad.err")"
    fi
fi

echo "--- the native jet"
(cd "$LEAN_SKI" && lake build p2run > /dev/null)
for k in 0 1 2; do
    d="$OUT/jet/$k"
    mkdir -p "$d"
    (cd "$LEAN_SKI" && lake exe p2run "$k" "$d" > /dev/null)
    "$AVON" reduce --p2="$d/P.dag" "$d/p2.dag" > "$d/out" 2> "$d/err" || { echo "FAIL: vector $k: $(cat "$d/err")"; fail=1; continue; }
    if [ "$(head -n 1 "$d/out")" = "NORMAL 1" ] && tail -n +2 "$d/out" | cmp -s - "$d/p2.expected" &&
        grep -q '^p2: 1 occurrences of P bound (skijack-2:[0-9a-f]*); 1 permutations run natively among the contractions, 0 declined' "$d/err"; then
        echo "vector $k: stateN (permute x) in one step: $(cat "$d/err")"
    else
        echo "FAIL: vector $k: $(head -c 80 "$d/out") / $(cat "$d/err")"
        fail=1
    fi
done

d="$OUT/jet/chain"
mkdir -p "$d"
(cd "$LEAN_SKI" && lake exe p2run chain 1 3 "$d" > /dev/null)
if "$AVON" reduce --p2="$d/P.dag" "$d/chain.dag" > "$d/out" 2> "$d/err" &&
    [ "$(head -n 1 "$d/out")" = "NORMAL 3" ] && tail -n +2 "$d/out" | cmp -s - "$d/chain.expected" &&
    grep -q '^p2: 1 occurrences of P bound (skijack-2:[0-9a-f]*); 3 permutations run natively among the contractions, 0 declined' "$d/err"; then
    echo "a chain of three: stateN (permute^3 x) in three steps: $(cat "$d/err")"
else
    echo "FAIL: a chain of three: $(head -c 80 "$d/out") / $(cat "$d/err")"
    fail=1
fi

echo "--- the permutation, printed from its proof"
mkdir -p "$OUT/prog"
ROOT=$(pwd)
if (cd "$LEAN_SKI" && lake env lean --run "$ROOT/lean/P2Prog.lean" "$OUT/prog/p2_prog.h") > "$OUT/prog/lean.txt" 2>&1 &&
    grep -qx "'AvonP2.permuteC' depends on axioms: \[propext, Quot.sound\]" "$OUT/prog/lean.txt"; then
    if cmp -s "$OUT/prog/p2_prog.h" src/p2_prog.h; then
        echo "AvonP2.permuteC checked; src/p2_prog.h is its print, byte for byte"
    else
        echo "FAIL: src/p2_prog.h is not lean/P2Prog.lean's print"
        fail=1
    fi
else
    echo "FAIL: lean/P2Prog.lean: $(head -c 400 "$OUT/prog/lean.txt")"
    fail=1
fi

if [ "$fail" -eq 0 ]; then echo "PASS"; else echo "FAIL"; exit 1; fi
