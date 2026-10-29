#!/usr/bin/env bash
# The word operations, proved: lean/Words.lean, checked against lean-ski,
# proves each numeral, list and bit-string operation's pinned term computes
# its function on every input, and Lean models of word_fire's, list_fire's
# and bits_walk's results sound (docs/LEAN-JETS.md), on Lean's axioms only, and prints the
# pins; the print must be src/word_pins.h, byte for byte.
#
# Run from the repository root.  LEAN_SKI defaults to ~/Code/ski/lean-ski.

set -euo pipefail

export LEAN_SKI=${LEAN_SKI:-$HOME/Code/ski/lean-ski}
. tests/pins.sh
pin_check lean-ski "$LEAN_SKI" "$LEAN_SKI_PIN"
OUT=${OUT:-build/words-lean}

rm -rf "$OUT"
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)
ROOT=$(pwd)
fail=0

# Every theorem the file prints, each the docs name, must rest on Lean's
# own axioms alone: propext and Quot.sound, never sorryAx or
# Lean.ofReduceBool.
THEOREMS="fireC_num fireC_arg listFireC_sound beq_fire bget_fire ideq_fire ideq_spec bget_spec ctors_compiled
    add_spec sub_spec mul_spec ifeq_spec ifle_spec div_spec rem_spec len_spec at_spec app_spec take_spec drop_spec beq_spec beqWalk_sound bgetWalk_sound ideqBits_sound"
axioms_ok() {
    local t
    for t in $THEOREMS; do
        grep -qE "^'AvonWords\.$t' (depends on axioms: \[propext(, Quot\.sound)?\]|does not depend on any axioms)$" "$OUT/lean.txt" || return 1
    done
}
if (cd "$LEAN_SKI" && lake env lean --run "$ROOT/lean/Words.lean" "$OUT/word_pins.h") > "$OUT/lean.txt" 2>&1 &&
    axioms_ok; then
    if cmp -s "$OUT/word_pins.h" src/word_pins.h; then
        echo "AvonWords: $(echo $THEOREMS) checked; src/word_pins.h is their print, byte for byte"
    else
        echo "FAIL: src/word_pins.h is not lean/Words.lean's print"
        fail=1
    fi
else
    echo "FAIL: lean/Words.lean: $(head -c 400 "$OUT/lean.txt")"
    fail=1
fi

if [ "$fail" -eq 0 ]; then echo "PASS"; else echo "FAIL"; exit 1; fi
