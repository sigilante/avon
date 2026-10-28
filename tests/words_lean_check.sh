#!/usr/bin/env bash
# The numeral words, proved: lean/Words.lean, checked against lean-ski,
# proves each numeral operation's pinned term computes the operation on
# every pair of Scott numerals (AvonWords.add_spec .. rem_spec) and
# word_fire's arithmetic the same values (AvonWords.fireC_num and fireC_arg,
# on lean-ski's axioms only), and prints the pins; the print must be
# src/word_pins.h, byte for byte.
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

if (cd "$LEAN_SKI" && lake env lean --run "$ROOT/lean/Words.lean" "$OUT/word_pins.h") > "$OUT/lean.txt" 2>&1 &&
    grep -qx "'AvonWords.fireC_num' depends on axioms: \[propext, Quot.sound\]" "$OUT/lean.txt" &&
    grep -qx "'AvonWords.fireC_arg' depends on axioms: \[propext, Quot.sound\]" "$OUT/lean.txt"; then
    if cmp -s "$OUT/word_pins.h" src/word_pins.h; then
        echo "AvonWords.fireC_num and fireC_arg checked; src/word_pins.h is their print, byte for byte"
    else
        echo "FAIL: src/word_pins.h is not lean/Words.lean's print"
        fail=1
    fi
else
    echo "FAIL: lean/Words.lean: $(head -c 400 "$OUT/lean.txt")"
    fail=1
fi

if [ "$fail" -eq 0 ]; then echo "PASS"; else echo "FAIL"; exit 1; fi
