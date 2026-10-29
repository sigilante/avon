#!/usr/bin/env bash
# Jets in a run, proved: lean/Jets.lean, checked against lean-ski, proves
# that a head run of head steps and head-first fires is never longer than
# the plain head run to a weak head normal form, so it ends, and that where
# it ends in one, that form is a weak reduct of the plain run's
# (AvonJets.jrun_le, jrun_whnf); and that a pin over Curry's Y fires
# head-first whenever its theorem goes through the knot (head_of_knot);
# and that a run mixing weak steps with fires of any jets, each convertible
# with its redex, at any position and in any order, stays convertible with
# the plain run, so a normal form it reaches is SKI's (jets_join,
# jets_normal), --fix's rewrite among them (fix_conv); and that Turing's
# fixed-point combinator, by lean-ski's abstraction, unfolds by reduction,
# head-first (turingU_abs, theta_head_first).
# Every printed theorem must rest on Lean's axioms alone, never sorryAx.
#
# Run from the repository root.  LEAN_SKI defaults to ~/Code/ski/lean-ski.

set -euo pipefail

export LEAN_SKI=${LEAN_SKI:-$HOME/Code/ski/lean-ski}
. tests/pins.sh
pin_check lean-ski "$LEAN_SKI" "$LEAN_SKI_PIN"
OUT=${OUT:-build/jets-lean}

rm -rf "$OUT"
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)
ROOT=$(pwd)

THEOREMS="jrun_le jrun_whnf head_of_knot jets_join jets_normal fix_conv turingU_abs theta_head_first"
axioms_ok() {
    local t
    for t in $THEOREMS; do
        grep -qE "^'AvonJets\\.$t' (depends on axioms: \\[propext(, Quot\\.sound)?\\]|does not depend on any axioms)$" \
            "$OUT/lean.txt" || return 1
    done
}
if (cd "$LEAN_SKI" && lake env lean "$ROOT/lean/Jets.lean") > "$OUT/lean.txt" 2>&1 && axioms_ok; then
    echo "AvonJets: $THEOREMS checked"
    echo "PASS"
else
    echo "FAIL: lean/Jets.lean: $(head -c 400 "$OUT/lean.txt")"
    echo "FAIL"
    exit 1
fi
