#!/usr/bin/env bash
# The jetted witness's acceptance (docs/DESIGN.md §17, §18.1).
#
# For every row of lean-ski's corpus:
#
#   1. lean-ski's `lake exe jets emit` writes the term's jet table: the
#      licensed roots and jets, each root passing Air.rootOKB;
#   2. build/avon witness --jet-table writes its jetted table: at a root
#      with enough arguments, one instantiation row;
#   3. lean-ski's prover, bench/plonky3's ski-air, runs the same terms with
#      the same jet tables, proves and verifies each, and writes its own
#      tables; Avon's must be byte-identical;
#   4. lean-ski's `lake exe jets check` must ACCEPT Avon's table: it checks
#      Air.AcceptsJ with the roots recomputed from the term (sound:
#      Air.checkJA_sound), so an accepted table proves the evaluation up to
#      weak reduction of the value, with its head and arity
#      (Air.air_sound_jet);
#   5. `ski-air jet-prove` proves Avon's own tables, and `ski-air
#      jet-verify` checks each proof from the public files alone, after
#      Lean's statement check.
#
# Run from the repository root after `make`.  LEAN_SKI defaults to
# ~/lean-ski.  One heavy job at a time: lean-ski's exes and ski-air are
# small, but nothing here runs in parallel.

set -euo pipefail

LEAN_SKI=${LEAN_SKI:-$HOME/lean-ski}
AVON=${AVON:-build/avon}
OUT=${OUT:-build/jet-witness}
ROOT=$(pwd)

rm -rf "$OUT"
mkdir -p "$OUT/avon" "$OUT/ski-air" "$OUT/proofs"
OUT=$(cd "$OUT" && pwd)
fail=0

echo "--- lean-ski: the corpus and its jet tables"
(cd "$LEAN_SKI" && lake build jets > /dev/null && lake env lean --run bench/Dump.lean > "$OUT/corpus.txt" \
    && lake exe jets emit "$OUT/jets")

echo "--- avon: jetted witnesses"
count=0
while read -r name _steps term; do
    printf '%s\n' "$term" > "$OUT/avon/$name.term"
    if ! "$ROOT/$AVON" witness --jet-table="$OUT/jets/$name.jets" "$OUT/avon/$name.term" \
            > "$OUT/avon/$name.txt" 2> "$OUT/avon/$name.err"; then
        echo "FAIL $name: $(cat "$OUT/avon/$name.err")"
        fail=1
        continue
    fi
    echo "$name: $(cat "$OUT/avon/$name.err")"
    count=$((count + 1))
done < "$OUT/corpus.txt"

echo "--- ski-air: prove and verify, jetted"
(cd "$LEAN_SKI/bench/plonky3" && cargo build --release --quiet)
SKI_AIR="$LEAN_SKI/bench/plonky3/target/release/ski-air"
if ! "$SKI_AIR" jets "$OUT/corpus.txt" "$OUT/jets" "$OUT/ski-air" | tee "$OUT/ski-air.log"; then
    echo "FAIL: ski-air reported failures"
    fail=1
fi

echo "--- byte-identical to ski-air's tables"
same=0
while read -r name _; do
    if cmp -s "$OUT/avon/$name.txt" "$OUT/ski-air/jet_$name.txt"; then
        same=$((same + 1))
    else
        echo "FAIL $name: Avon's jetted table differs from ski-air's"
        fail=1
    fi
done < "$OUT/corpus.txt"
echo "$same of $count identical"

echo "--- lake exe jets check on Avon's tables"
if ! (cd "$LEAN_SKI" && lake exe jets check "$OUT"/avon/*.txt) | tee "$OUT/jets-check.log"; then
    echo "FAIL: jets check rejected a table"
    fail=1
fi
accepted=$(grep -c '^ACCEPT' "$OUT/jets-check.log" || true)
echo "$accepted of $count accepted"
[ "$accepted" = "$count" ] || fail=1

echo "--- ski-air: Avon's tables proved, and each proof verified alone"
while read -r name _; do
    grep "^$name " "$OUT/corpus.txt" > "$OUT/proofs/$name.corpus"
    if ! "$SKI_AIR" jet-prove "$OUT/avon/$name.term" "$OUT/jets/$name.jets" \
            "$OUT/avon/$name.txt" "$OUT/proofs/$name.proof" \
       || ! "$SKI_AIR" jet-verify "$OUT/proofs/$name.corpus" "$OUT/jets" "$name" \
            "$OUT/proofs/$name.proof"; then
        echo "FAIL $name: Avon's table did not prove and verify"
        fail=1
    fi
done < "$OUT/corpus.txt"

if [ "$fail" != 0 ]; then
    echo "JET WITNESS CHECK FAILED"
    exit 1
fi
echo "jet witness check passed: $count jetted witnesses identical, accepted, proved and verified"
