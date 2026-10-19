#!/usr/bin/env bash
# The composed witness with jets, under hiding (docs/ZK-JETS.md, milestone 8).
#
# For lean-ski's composed statements `and` and `or` and its SKIlark
# predicate `split8`, each with split8's source's templates:
#
#   1. lean-ski writes the statement with jets, its four heights public
#      budgets (`lake exe composed budget`: `log R M Lp Li`), and the
#      statement's jet table (`lake exe skilark cjets`, Air.jetTableC);
#   2. build/avon witness --statement --jet-table writes the table for the
#      witness: the statement's heap with the bits and region filled in,
#      one jetted segment per root, padded to the statement's heights;
#   3. lean-ski's prover, ski-air compj-prove, runs the same witness, proves
#      and verifies, and writes its own table; Avon's must be byte-identical;
#   4. lean-ski's `lake exe composed check-cj` must ACCEPT Avon's table
#      (CompM.checkCJ_sound: every term evaluates to K on its bits and
#      witness);
#   5. `ski-air compj-prove-table` proves Avon's own table under hiding, and
#      `ski-air compj-verify` checks the proof from the public files alone;
#   6. the witnesses that do not satisfy the statement (wrong, clear,
#      non-Boolean) are refused by Avon as by ski-air; the forged region's
#      table Avon writes is rejected by check-cj and does not prove; a
#      budget below the run's is refused by both.
#
# Run from the repository root after `make`.  LEAN_SKI defaults to
# ~/Code/ski/lean-ski.  One heavy job at a time: nothing here runs in
# parallel.

set -euo pipefail

export LEAN_SKI=${LEAN_SKI:-$HOME/Code/ski/lean-ski}   # ski-air finds Lean through it
. tests/pins.sh
pin_check lean-ski "$LEAN_SKI" "$LEAN_SKI_PIN"
AVON=${AVON:-build/avon}
OUT=${OUT:-build/zk-jet-witness}
ROOT=$(pwd)
AVON=$(cd "$(dirname "$AVON")" && pwd)/$(basename "$AVON")

rm -rf "$OUT"
mkdir -p "$OUT/avon" "$OUT/ski-air" "$OUT/proofs" "$OUT/stmt"
OUT=$(cd "$OUT" && pwd)
fail=0
lake_ski() { (cd "$LEAN_SKI" && lake exe "$@"); }

echo "--- lean-ski: statements with jets, and their jet tables"
(cd "$LEAN_SKI" && lake build composed skilark circuit > /dev/null)
lake_ski composed emit "$OUT/composed" > /dev/null
SRC="$LEAN_SKI/bench/plonky3/skilark/split8/source.ski"
# name, the statement's directory, POP's and INSTW's budgets
cases="and:$OUT/composed/and:9:9 or:$OUT/composed/or:9:9 split8:$LEAN_SKI/bench/plonky3/skilark/split8:14:14"
for c in $cases; do
    IFS=: read -r name dir lp li <<< "$c"
    lake_ski composed budget "$dir/public.txt" "$lp" "$li" "$OUT/stmt/$name.txt" > /dev/null
    lake_ski skilark cjets "$SRC" "$OUT/stmt/$name.txt" "$OUT/stmt/$name.jets" | tail -n 1
done

echo "--- ski-air"
# SKI_AIR: a built ski-air to use instead of building lean-ski's own
if [ -z "${SKI_AIR:-}" ]; then
    (cd "$LEAN_SKI/bench/plonky3" && cargo build --release --quiet)
    SKI_AIR="$LEAN_SKI/bench/plonky3/target/release/ski-air"
fi

for c in $cases; do
    IFS=: read -r name dir lp li <<< "$c"
    stmt="$OUT/stmt/$name.txt"
    jets="$OUT/stmt/$name.jets"
    echo "--- $name"
    if ! "$AVON" witness --statement="$stmt" --jet-table="$jets" "$dir/witness.txt" \
            > "$OUT/avon/$name.txt" 2> "$OUT/avon/$name.err"; then
        echo "FAIL $name: Avon: $(cat "$OUT/avon/$name.err")"
        fail=1
        continue
    fi
    echo "avon: $(cat "$OUT/avon/$name.err")"
    if ! "$SKI_AIR" compj-prove "$stmt" "$jets" "$SRC" "$dir/witness.txt" "$OUT/proofs/$name.ski-air.proof" \
            "$OUT/ski-air/$name.txt" > "$OUT/ski-air/$name.log"; then
        echo "FAIL $name: ski-air: $(tail -n 1 "$OUT/ski-air/$name.log")"
        fail=1
        continue
    fi
    if cmp -s "$OUT/avon/$name.txt" "$OUT/ski-air/$name.txt"; then
        echo "byte-identical to ski-air's table"
    else
        echo "FAIL $name: Avon's table differs from ski-air's"
        fail=1
    fi
    line=$(lake_ski composed check-cj "$SRC" "$stmt" "$OUT/avon/$name.txt" 2>&1 | grep -E '^(ACCEPT|REJECT)' || true)
    case "$line" in
        "ACCEPT $OUT/avon/$name.txt:"*) echo "check-cj: ACCEPT" ;;
        *) echo "FAIL $name: check-cj: $line"; fail=1 ;;
    esac
    if "$SKI_AIR" compj-prove-table "$stmt" "$jets" "$SRC" "$OUT/avon/$name.txt" "$OUT/proofs/$name.proof" \
            > "$OUT/proofs/$name.log" \
       && "$SKI_AIR" compj-verify "$stmt" "$jets" "$SRC" "$OUT/proofs/$name.proof" > "$OUT/proofs/$name.verify" \
       && grep -q '^VERIFIED' "$OUT/proofs/$name.verify"; then
        echo "Avon's table proved under hiding and verified alone"
    else
        echo "FAIL $name: Avon's table did not prove and verify: $(tail -n 1 "$OUT/proofs/$name.log")"
        fail=1
    fi

    # witnesses that do not satisfy the statement: refused by both
    for bad in wrong clear nonbool; do
        if "$AVON" witness --statement="$stmt" --jet-table="$jets" "$dir/witness_$bad.txt" \
                > /dev/null 2> "$OUT/avon/$name.$bad.err"; then
            echo "FAIL $name: Avon wrote a table for the $bad witness"
            fail=1
        elif "$SKI_AIR" compj-prove "$stmt" "$jets" "$SRC" "$dir/witness_$bad.txt" "$OUT/proofs/$name.$bad.proof" \
                > /dev/null 2>&1; then
            echo "FAIL $name: ski-air proved the $bad witness"
            fail=1
        else
            echo "the $bad witness: refused by both"
        fi
    done
    # the forged region: Avon runs it; Lean and the circuit reject the table
    if "$AVON" witness --statement="$stmt" --jet-table="$jets" "$dir/witness_forged.txt" \
            > "$OUT/avon/$name.forged.txt" 2> /dev/null; then
        line=$(lake_ski composed check-cj "$SRC" "$stmt" "$OUT/avon/$name.forged.txt" 2>&1 | grep -E '^(ACCEPT|REJECT)' || true)
        if [ "${line%% *}" != REJECT ]; then
            echo "FAIL $name: check-cj did not reject the forged region: $line"
            fail=1
        elif "$SKI_AIR" compj-prove-table "$stmt" "$jets" "$SRC" "$OUT/avon/$name.forged.txt" \
                "$OUT/proofs/$name.forged.proof" > /dev/null 2>&1; then
            echo "FAIL $name: the forged region's table proved"
            fail=1
        else
            echo "the forged region: rejected by check-cj, and no proof"
        fi
    else
        echo "the forged region: refused by Avon"
    fi
    # a POP budget below the run's: the largest power of two under the
    # run's pops (Avon's report), refused by both
    pops=$(sed -n 's/.* pops \([0-9][0-9]*\) .*/\1/p' "$OUT/avon/$name.err")
    if [ -z "$pops" ]; then
        echo "FAIL $name: no pop count in Avon's report"
        fail=1
        continue
    fi
    small=0
    while [ $(( 1 << (small + 1) )) -lt "$pops" ]; do small=$(( small + 1 )); done
    if [ "$small" -ge 9 ]; then
        lake_ski composed budget "$dir/public.txt" "$small" "$li" "$OUT/stmt/$name.small.txt" > /dev/null
        if "$AVON" witness --statement="$OUT/stmt/$name.small.txt" --jet-table="$jets" "$dir/witness.txt" \
                > /dev/null 2> "$OUT/avon/$name.small.err"; then
            echo "FAIL $name: Avon wrote a table over POP's budget 2^$small"
            fail=1
        elif ! grep -q "pops exceed POP's budget" "$OUT/avon/$name.small.err"; then
            echo "FAIL $name: Avon refused POP's budget 2^$small for another reason: $(cat "$OUT/avon/$name.small.err")"
            fail=1
        elif "$SKI_AIR" compj-prove "$OUT/stmt/$name.small.txt" "$jets" "$SRC" "$dir/witness.txt" \
                "$OUT/proofs/$name.small.proof" > /dev/null 2>&1; then
            echo "FAIL $name: ski-air proved over POP's budget 2^$small"
            fail=1
        else
            echo "POP's budget 2^$small: refused by both"
        fi
    fi
done

if [ "$fail" != 0 ]; then
    echo "ZK JET WITNESS CHECK FAILED"
    exit 1
fi
echo "zk jet witness check passed: and, or and split8 identical to ski-air's, accepted by check-cj, proved under hiding and verified; bad witnesses and budgets refused"
