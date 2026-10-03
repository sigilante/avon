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
#      Avon refuses it as ski-air does.
#
# Avon and ski-air read a false bit only as the cell A 0 1; lean-ski's
# p2Row also accepts any A f x with f at K and x at I.  The narrower reading
# costs completeness only: the statement's witness writes A 0 1.
#
# Run from the repository root after `make`.  LEAN_SKI defaults to
# ~/lean-ski.  One heavy job at a time: nothing here runs in parallel.

set -euo pipefail

export LEAN_SKI=${LEAN_SKI:-$HOME/lean-ski}   # ski-air finds Lean through it
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

if [ "$fail" -eq 0 ]; then echo "PASS"; else echo "FAIL"; exit 1; fi
