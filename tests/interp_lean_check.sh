#!/usr/bin/env bash
# The interpreter jet's adequacy, proved: lean/Interp.lean, checked against
# lean-ski, proves the paper's step and fuel adequacy for the 618-atom whnfF
# the interpreter jet serves: whnfF <k> <M> reduces to the encoding of
# lean-ski's evalF k M (AvonInterp.whnfF_adequate, step_spec), every printed
# theorem on Lean's axioms alone.  Its printed pins -- whnfF and the
# constructors its theorem speaks of -- must be the conformance
# dictionary's terms under interp-whnff's names, byte for byte, every one
# of them printed; interpreters.tsv's whnfF core must be keyed by that
# whnfF, with those terms as its object and result constructors; and its
# nat line must name lean-ski's Scott Zero and Suc, encNat's.
#
# Run from the repository root.  LEAN_SKI defaults to ~/Code/ski/lean-ski.

set -euo pipefail

export LEAN_SKI=${LEAN_SKI:-$HOME/Code/ski/lean-ski}
. tests/pins.sh
pin_check lean-ski "$LEAN_SKI" "$LEAN_SKI_PIN"
OUT=${OUT:-build/interp-lean}

rm -rf "$OUT"
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)
ROOT=$(pwd)
C=tests/conformance
fail=0

THEOREMS="whnfF_adequate step_spec whnf_pin pins_compiled"
axioms_ok() {
    local t
    for t in $THEOREMS; do
        grep -qE "^'AvonInterp\\.$t' (depends on axioms: \\[propext(, Quot\\.sound)?\\]|does not depend on any axioms)$" \
            "$OUT/lean.txt" || return 1
    done
}
if (cd "$LEAN_SKI" && lake env lean --run "$ROOT/lean/Interp.lean" "$OUT/pins.tsv") > "$OUT/lean.txt" 2>&1 &&
    axioms_ok; then
    echo "AvonInterp: $THEOREMS checked"
else
    echo "FAIL: lean/Interp.lean: $(head -c 400 "$OUT/lean.txt")"
    exit 1
fi

lean_pin() { awk -F'\t' -v n="$1" '$1 == n { print $2 }' "$OUT/pins.tsv"; }
dict_term() { awk -F'\t' -v h="$1" '$1 == h { print $3 }' "$C/dictionary.tsv"; }
whnff_hash() { awk -F'\t' -v n="$1" '$1 == "interp-whnff" && $2 == n { print $3 }' "$C/dictionary_names.tsv"; }

for name in whnfF S K I App Just Nothing cons; do
    term=$(lean_pin "$name")
    hash=$(whnff_hash "$name")
    if [ -n "$term" ] && [ -n "$hash" ] && [ "$(dict_term "$hash")" = "$term" ]; then
        echo "$name: Lean's print is the dictionary's $hash"
    else
        echo "FAIL: $name: Lean's print is not the dictionary's term (${hash:-no hash})"
        fail=1
    fi
done

whnf=$(whnff_hash whnfF)
row=$(awk -F'\t' -v h="$whnf" '$1 == h && $2 == "interp-whnff.whnfF"' "$C/interpreters.tsv")
objs="S/$(whnff_hash S) K/$(whnff_hash K) I/$(whnff_hash I) App/$(whnff_hash App)"
outs="timeout/$(whnff_hash Nothing) value/$(whnff_hash Just)"
if [ -n "$row" ] && [ "$(printf '%s' "$row" | cut -f4)" = "$objs" ] &&
    [ "$(printf '%s' "$row" | cut -f5)" = "$outs" ]; then
    echo "interpreters.tsv: the whnfF core is keyed by $whnf, over Lean's constructors"
else
    echo "FAIL: interpreters.tsv has no whnfF core keyed by $whnf over Lean's constructors"
    fail=1
fi

zero=$(lean_pin Zero)
suc=$(lean_pin Suc)
if [ -n "$zero" ] && [ -n "$suc" ] &&
    awk -F'\t' '$1 == "nat" { print $2 "\t" $3 }' "$C/interpreters.tsv" |
    while IFS=$'\t' read -r hz hs; do
        [ "$(dict_term "$hz")" = "$zero" ] && [ "$(dict_term "$hs")" = "$suc" ] && echo ok
    done | grep -q ok; then
    echo "interpreters.tsv: its nat line is encNat's Zero and Suc"
else
    echo "FAIL: interpreters.tsv has no nat line of encNat's Zero and Suc"
    fail=1
fi

if [ "$fail" -eq 0 ]; then echo "PASS"; else echo "FAIL"; exit 1; fi
