#!/usr/bin/env bash
# Y unfolded in one step, proved: lean/Fix.lean, checked against lean-ski,
# proves that a run mixing --fix's rewrite with weak steps stays
# convertible with the plain run, so a normal form it reaches is SKI's
# (AvonFix.fix_join, fix_normal), and Y's simulation up to lean-ski's Tr
# with Y a jet (AvonFix.fix_simulation), which applies to lean-ski's
# compiled sum and loop programs (sum_fixedJ, loop_fixedJ,
# sum_fix_simulation).  Every printed theorem must rest on Lean's
# standard axioms alone, never sorryAx.
#
# Run from the repository root.  LEAN_SKI defaults to ~/Code/ski/lean-ski.

set -euo pipefail

export LEAN_SKI=${LEAN_SKI:-$HOME/Code/ski/lean-ski}
. tests/pins.sh
pin_check lean-ski "$LEAN_SKI" "$LEAN_SKI_PIN"
OUT=${OUT:-build/fix-lean}

rm -rf "$OUT"
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)
ROOT=$(pwd)

THEOREMS="fix_join fix_normal simulationJ_steps fix_simulation fixed_of_fixedJ sum_fix_simulation loop_fixedJ sum_loop_recursive closure_spells_Y"
axioms_ok() {
    local t
    for t in $THEOREMS; do
        grep -qE "^'AvonFix\\.$t' depends on axioms: \\[propext(, Classical\\.choice)?(, Quot\\.sound)?\\]$" \
            "$OUT/lean.txt" || return 1
    done
}
if (cd "$LEAN_SKI" && lake env lean "$ROOT/lean/Fix.lean") > "$OUT/lean.txt" 2>&1 && axioms_ok; then
    echo "AvonFix: $THEOREMS checked"
    echo "PASS"
else
    echo "FAIL: lean/Fix.lean: $(head -c 400 "$OUT/lean.txt")"
    echo "FAIL"
    exit 1
fi
