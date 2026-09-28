#!/usr/bin/env bash
# The probe witness's acceptance (docs/DESIGN.md §18.2): Avon's table binds
# a corpus row's output, byte for byte as lean-ski's prover writes it.
#
# For every row of lean-ski's corpus, with its outcome from the row's Joy
# program (below):
#
#   1. lean-ski's `lake exe jets emit` writes the term's jet table, and
#      `lake exe jets plan OUTCOME` the outcome's probe plan;
#   2. build/avon witness --jet-table --plan writes the probe table;
#   3. `ski-air probe-prove` runs the same term, jet table and plan, proves
#      and verifies it, and writes its table; Avon's must be byte-identical;
#   4. `lake exe jets check-probe` must ACCEPT Avon's table for the outcome
#      (Air.checkPA_decodes: the term decodes to it) and REJECT it for a
#      wrong one;
#   5. for the wrong outcomes -- `err`, and the right one's first number
#      less one -- Avon must exit nonzero: the term does not decode to them.
#
# Run from the repository root after `make`.  LEAN_SKI defaults to
# ~/lean-ski.  Nothing here runs in parallel.

set -euo pipefail

LEAN_SKI=${LEAN_SKI:-$HOME/lean-ski}
AVON=${AVON:-build/avon}
OUT=${OUT:-build/probe-witness}
ROOT=$(pwd)

# Each row's outcome, top of the stack first: its Joy program's value.
outcome_of() {
    case "$1" in
        compiled_up|interpreted_up) echo "val 6" ;;         # 1 2 + dup +
        compiled_uq|interpreted_uq) echo "val 6" ;;         # 3 [dup +] i
        compiled_ur|interpreted_ur) echo "val 1 2 1" ;;     # 1 2 over
        sumto_us)                   echo "val 6" ;;         # 3 sumto
        *)                          echo "" ;;
    esac
}

rm -rf "$OUT"
mkdir -p "$OUT/avon" "$OUT/ski-air" "$OUT/plans"
OUT=$(cd "$OUT" && pwd)
fail=0

echo "--- lean-ski: the corpus, its jet tables, the plans"
(cd "$LEAN_SKI" && lake build jets > /dev/null && lake env lean --run bench/Dump.lean > "$OUT/corpus.txt" \
    && lake exe jets emit "$OUT/jets")
(cd "$LEAN_SKI/bench/plonky3" && cargo build --release --quiet)
SKI_AIR="$LEAN_SKI/bench/plonky3/target/release/ski-air"

count=0 same=0 accepted=0 refused=0 rejected=0 wrongs=0
while read -r name _steps term; do
    outcome=$(outcome_of "$name")
    if [ -z "$outcome" ]; then
        echo "FAIL $name: no outcome recorded for this corpus row"
        fail=1
        continue
    fi
    count=$((count + 1))
    printf '%s\n' "$term" > "$OUT/avon/$name.term"
    (cd "$LEAN_SKI" && lake exe jets plan $outcome) > "$OUT/plans/$name.plan"

    if ! "$ROOT/$AVON" witness --jet-table="$OUT/jets/$name.jets" --plan="$OUT/plans/$name.plan" \
            "$OUT/avon/$name.term" > "$OUT/avon/$name.txt" 2> "$OUT/avon/$name.err"; then
        echo "FAIL $name [$outcome]: $(cat "$OUT/avon/$name.err")"
        fail=1
        continue
    fi
    echo "$name [$outcome]: $(cat "$OUT/avon/$name.err")"

    if "$SKI_AIR" probe-prove "$OUT/avon/$name.term" "$OUT/jets/$name.jets" \
            "$OUT/ski-air/$name.txt" "$OUT/ski-air/$name.proof" $outcome > "$OUT/ski-air/$name.log" \
       && cmp -s "$OUT/avon/$name.txt" "$OUT/ski-air/$name.txt"; then
        same=$((same + 1))
    else
        echo "FAIL $name: Avon's probe table differs from ski-air's (or ski-air failed)"
        fail=1
    fi

    if (cd "$LEAN_SKI" && lake exe jets check-probe "$OUT/avon/$name.txt" $outcome) | grep -q '^ACCEPT'; then
        accepted=$((accepted + 1))
    else
        echo "FAIL $name: check-probe does not accept Avon's table for $outcome"
        fail=1
    fi

    first=$(echo "$outcome" | awk '{print $2}')
    for wrong in "err" "val $((first - 1))"; do
        wrongs=$((wrongs + 1))
        (cd "$LEAN_SKI" && lake exe jets plan $wrong) > "$OUT/plans/$name.wrong.plan"
        if "$ROOT/$AVON" witness --jet-table="$OUT/jets/$name.jets" --plan="$OUT/plans/$name.wrong.plan" \
                "$OUT/avon/$name.term" > /dev/null 2> "$OUT/avon/$name.wrong.err"; then
            echo "FAIL $name: Avon wrote a table for the wrong outcome $wrong"
            fail=1
        else
            refused=$((refused + 1))
        fi
        if (cd "$LEAN_SKI" && lake exe jets check-probe "$OUT/avon/$name.txt" $wrong) | grep -q '^ACCEPT'; then
            echo "FAIL $name: check-probe accepted Avon's table for the wrong outcome $wrong"
            fail=1
        else
            rejected=$((rejected + 1))
        fi
    done
done < "$OUT/corpus.txt"

echo "$same of $count identical to ski-air's; $accepted of $count accepted"
echo "$refused of $wrongs wrong outcomes refused by Avon; $rejected of $wrongs rejected by check-probe"
[ "$same" = "$count" ] && [ "$accepted" = "$count" ] && [ "$refused" = "$wrongs" ] \
    && [ "$rejected" = "$wrongs" ] && [ "$count" -gt 0 ] || fail=1

if [ "$fail" != 0 ]; then
    echo "PROBE WITNESS CHECK FAILED"
    exit 1
fi
echo "probe witness check passed: $count probe tables identical and accepted; $wrongs wrong outcomes refused and rejected"
