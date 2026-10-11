#!/usr/bin/env bash
# The witness strategy's acceptance.
#
# For every conformance target that reaches weak head normal form:
#
#   1. build/avon witness writes its table, and its contraction count must
#      equal the copy-mode count skijack exported;
#   2. lean-ski's prover, bench/plonky3's ski-air, is given the same terms
#      with those counts: it checks its own run reaches the same count,
#      proves, and verifies each, and writes its own table;
#   3. Avon's table must be byte-identical to ski-air's;
#   4. lean-ski's `lake exe aircheck` must ACCEPT Avon's table: it decides
#      the AIR's constraints (Air.checkA_iff), so an accepted table proves
#      the evaluation it ends on (Air.air_sound_eval).
#
# Targets stopped by host fuel diverge and have no witness.  Run from the
# repository root after `make`.  LEAN_SKI defaults to ~/Code/ski/lean-ski.

set -euo pipefail

export LEAN_SKI=${LEAN_SKI:-$HOME/Code/ski/lean-ski}   # ski-air finds Lean through it
. tests/pins.sh
pin_check lean-ski "$LEAN_SKI" "$LEAN_SKI_PIN"
AVON=${AVON:-build/avon}
OUT=${OUT:-build/witness}
ROOT=$(pwd)

rm -rf "$OUT"
mkdir -p "$OUT/avon" "$OUT/ski-air"
: > "$OUT/corpus.txt"
fail=0
count=0

while IFS=$'\t' read -r id file _max st steps _rest; do
    if [ "$st" != WHNF ]; then
        echo "no witness: $id ($st: the circuit proves weak head normal form only)"
        continue
    fi
    if ! "$AVON" witness "tests/conformance/$file" \
            > "$OUT/avon/$id.txt" 2> "$OUT/avon/$id.err"; then
        echo "FAIL $id: $(cat "$OUT/avon/$id.err")"
        fail=1
        continue
    fi
    read -r _ contr _ rows _ cells _ < "$OUT/avon/$id.err"
    if [ "$contr" != "$steps" ]; then
        echo "FAIL $id: the witness contracts $contr times, copy mode $steps"
        fail=1
    fi
    printf '%s %s %s\n' "$id" "$steps" "$(head -1 "$OUT/avon/$id.txt")" >> "$OUT/corpus.txt"
    count=$((count + 1))
done < tests/conformance/manifest.tsv
echo "$count witnesses written"

echo "--- ski-air: prove and verify"
# SKI_AIR: a built ski-air to use instead of building lean-ski's own (a
# binary outside the checkout finds the Lean project through $LEAN_SKI)
if [ -z "${SKI_AIR:-}" ]; then
    (cd "$LEAN_SKI/bench/plonky3" && cargo build --release --quiet)
    SKI_AIR="$LEAN_SKI/bench/plonky3/target/release/ski-air"
fi
if ! "$SKI_AIR" "$OUT/corpus.txt" "$OUT/ski-air" \
        | tee "$OUT/ski-air.log"; then
    echo "FAIL: ski-air reported failures"
    fail=1
fi

echo "--- byte-identical to ski-air's tables"
same=0
while read -r id _; do
    if cmp -s "$OUT/avon/$id.txt" "$OUT/ski-air/$id.txt"; then
        same=$((same + 1))
    else
        echo "FAIL $id: Avon's table differs from ski-air's"
        fail=1
    fi
done < "$OUT/corpus.txt"
echo "$same of $count identical"

echo "--- aircheck"
(cd "$LEAN_SKI" && lake build aircheck > /dev/null)
if ! (cd "$LEAN_SKI" && lake exe aircheck "$ROOT/$OUT"/avon/*.txt) | tee "$OUT/aircheck.log"; then
    echo "FAIL: aircheck rejected a table"
    fail=1
fi
accepted=$(grep -c '^ACCEPT' "$OUT/aircheck.log" || true)
echo "$accepted of $count accepted"
[ "$accepted" = "$count" ] || fail=1

if [ "$fail" != 0 ]; then
    echo "WITNESS CHECK FAILED"
    exit 1
fi
echo "witness check passed: $count witnesses proved, verified, identical, accepted"
