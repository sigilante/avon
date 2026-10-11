#!/usr/bin/env bash
# The probe witness's acceptance: Avon's table binds a corpus row's
# output, byte for byte as lean-ski's prover writes it.
#
# For every row of lean-ski's corpus, with its outcome from the row's Joy
# program (below):
#
#   1. lean-ski's `lake exe jets emit` writes the term's jet table, and
#      `lake exe jets plan OUTCOME` the outcome's probe plan;
#   2. build/avon witness --jet-table --plan writes the probe table;
#   3. `ski-air probe-prove` runs the same term, jet table and plan, proves
#      and verifies it, and writes its table; Avon's must be byte-identical;
#   4. `lake exe jets check-probe --row NAME` must ACCEPT Avon's table for
#      the outcome, naming the row (Air.checkPA_decodes: the term decodes
#      to it), and REJECT it for each wrong outcome;
#   5. for the wrong outcomes Avon must refuse the plan with "does not
#      decode": `err`, the first number less one (a longer or shorter
#      plan), and one whose plan has the right outcome's length, so that
#      check-probe must read the markers, not only count segments;
#   6. forged tables must be refused: another row's term spliced onto the
#      table (NOT THE TERM OF the row), a start row moved and a field
#      pointer moved (REJECT); and another row's true table offered as
#      sumto_us's, lean-ski #2's case (NOT THE TERM OF sumto_us).
#
# check-probe certifies the term the table's first line names; this script
# binds that term to the corpus row twice: by comparing the line with it,
# and with check-probe's --row.
#
# Run from the repository root after `make`.  LEAN_SKI defaults to
# ~/lean-ski.  Nothing here runs in parallel.

set -euo pipefail

export LEAN_SKI=${LEAN_SKI:-$HOME/lean-ski}   # ski-air finds Lean through it
. tests/pins.sh
pin_check lean-ski "$LEAN_SKI" "$LEAN_SKI_PIN"
AVON=${AVON:-build/avon}
OUT=${OUT:-build/probe-witness}
ROOT=$(pwd)

EXPECTED_ROWS=7

# Each row's outcome, top of the stack first: its Joy program's value; and
# a wrong outcome whose plan has the same number of segments.
same_length_wrong() {
    case "$1" in
        "val 6")     echo "val 3 0" ;;      # 6 + 5 = 3 + 0 + 8 segments
        "val 1 2 1") echo "val 2 1 1" ;;
        *)           echo "" ;;
    esac
}

# check-probe's first line on a table offered as a row, for an outcome; it
# exits nonzero on anything but ACCEPT.
verdict_line() {
    local row=$1 table=$2; shift 2
    (cd "$LEAN_SKI" && lake exe jets check-probe --row "$row" "$table" "$@" 2>&1 || true) | head -n 1
}

# its first word: ACCEPT, REJECT, NOT (THE TERM OF), or another
verdict() {
    verdict_line "$@" | awk '{print $1}'
}

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
# SKI_AIR: a built ski-air to use instead of building lean-ski's own (a
# binary outside the checkout finds the Lean project through $LEAN_SKI)
if [ -z "${SKI_AIR:-}" ]; then
    (cd "$LEAN_SKI/bench/plonky3" && cargo build --release --quiet)
    SKI_AIR="$LEAN_SKI/bench/plonky3/target/release/ski-air"
fi

count=0 same=0 accepted=0 refused=0 rejected=0 wrongs=0 bound=0 forged=0 forgeries=0
while read -r name _steps term <&3; do
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

    # the table names this row's term: check-probe certifies that line
    if [ "$(head -n 1 "$OUT/avon/$name.txt")" = "$term" ]; then
        bound=$((bound + 1))
    else
        echo "FAIL $name: the table's term is not the corpus row's"
        fail=1
    fi

    line=$(verdict_line "$name" "$OUT/avon/$name.txt" $outcome)
    if [ "$line" != "${line#"ACCEPT $OUT/avon/$name.txt: corpus row $name decodes to $outcome ("}" ]; then
        accepted=$((accepted + 1))
    else
        echo "FAIL $name: check-probe on Avon's table for $outcome: $line"
        fail=1
    fi

    first=$(echo "$outcome" | awk '{print $2}')
    for wrong in "err" "val $((first - 1))" "$(same_length_wrong "$outcome")"; do
        wrongs=$((wrongs + 1))
        (cd "$LEAN_SKI" && lake exe jets plan $wrong) > "$OUT/plans/$name.wrong.plan"
        if "$ROOT/$AVON" witness --jet-table="$OUT/jets/$name.jets" --plan="$OUT/plans/$name.wrong.plan" \
                "$OUT/avon/$name.term" > /dev/null 2> "$OUT/avon/$name.wrong.err"; then
            echo "FAIL $name: Avon wrote a table for the wrong outcome $wrong"
            fail=1
        elif grep -q 'does not decode' "$OUT/avon/$name.wrong.err"; then
            refused=$((refused + 1))
        else
            echo "FAIL $name: Avon refused $wrong for another reason: $(cat "$OUT/avon/$name.wrong.err")"
            fail=1
        fi
        if [ "$(verdict "$name" "$OUT/avon/$name.txt" $wrong)" = REJECT ]; then
            rejected=$((rejected + 1))
        else
            echo "FAIL $name: check-probe did not REJECT Avon's table for the wrong outcome $wrong"
            fail=1
        fi
    done
done 3< "$OUT/corpus.txt"

# Forged tables, from sumto_us's, each offered as sumto_us's for val 6: the
# spliced term is not sumto_us's, the rest are REJECTed; and compiled_up's
# true table offered as sumto_us's is refused.
T="$OUT/avon/sumto_us.txt"
forge() {                       # forge NAME: the forged table on stdout
    case "$1" in
        spliced)                # another row's term on sumto's body
            head -n 1 "$OUT/avon/compiled_up.txt"; tail -n +2 "$T" ;;
        offered)                # compiled_up's own table, whole
            cat "$OUT/avon/compiled_up.txt" ;;
        start)                  # segment 1's probe row moved by one
            awk 'f==1 && n==1 {print $1+1; n++; next} f==1 {n++} /^starts /{f=1; n=0} {print}' "$T" ;;
        field)                  # the first field pointer moved by one
            awk 'g==1 && !d {print $1, $2+1; d=1; next} /^fields /{g=1} {print}' "$T" ;;
    esac
}
if [ -f "$T" ] && [ -f "$OUT/avon/compiled_up.txt" ]; then
    for f in spliced offered start field; do
        forgeries=$((forgeries + 1))
        forge "$f" > "$OUT/avon/forged_$f.txt"
        case $f in spliced|offered) want=NOT ;; *) want=REJECT ;; esac
        got=$(verdict sumto_us "$OUT/avon/forged_$f.txt" val 6)
        if cmp -s "$OUT/avon/forged_$f.txt" "$T"; then
            echo "FAIL forged $f: the forgery changed nothing"
            fail=1
        elif [ "$got" = "$want" ]; then
            forged=$((forged + 1))
        else
            echo "FAIL forged $f: check-probe said $got, not $want"
            fail=1
        fi
    done
fi

echo "$count corpus rows (expected $EXPECTED_ROWS); $bound tables name their row's term"
echo "$same of $count identical to ski-air's; $accepted of $count accepted"
echo "$refused of $wrongs wrong outcomes refused by Avon; $rejected of $wrongs rejected by check-probe"
echo "$forged of $forgeries forged or misoffered tables refused"
[ "$count" = "$EXPECTED_ROWS" ] && [ "$bound" = "$count" ] && [ "$same" = "$count" ] \
    && [ "$accepted" = "$count" ] && [ "$refused" = "$wrongs" ] && [ "$rejected" = "$wrongs" ] \
    && [ "$forgeries" = 4 ] && [ "$forged" = "$forgeries" ] || fail=1

if [ "$fail" != 0 ]; then
    echo "PROBE WITNESS CHECK FAILED"
    exit 1
fi
echo "probe witness check passed: $count probe tables identical and accepted, each naming its row; $wrongs wrong outcomes refused and rejected; $forgeries forged or misoffered tables refused"
