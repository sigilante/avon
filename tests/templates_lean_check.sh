#!/usr/bin/env bash
# Templates, proved: lean/Templates.lean, checked against lean-ski, proves
# that tmpl.c's load check computes lean-ski's bracket abstraction
# (AvonTemplates.absC_eq) and that a template it accepts fires soundly: its
# key over the arguments weakly reduces to what tmpl_instance builds
# (AvonTemplates.template_fire), on Lean's axioms only.  Its replay of the
# loader, the model with the file's digests (SHA-256, in Lean), must count
# what Avon counts on every template set the tests ship, and on copies of
# one changed to reach each refusal: a key that is not the body's, an open
# body, wrong formals, an arity past the cap, a duplicate, an η-template,
# text after the body, a bare combinator.
#
# Run from the repository root after `make`.  LEAN_SKI defaults to
# ~/Code/ski/lean-ski.

set -euo pipefail

export LEAN_SKI=${LEAN_SKI:-$HOME/Code/ski/lean-ski}
. tests/pins.sh
pin_check lean-ski "$LEAN_SKI" "$LEAN_SKI_PIN"
AVON=${AVON:-build/avon}
OUT=${OUT:-build/templates-lean}

rm -rf "$OUT"
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)
AVON=$(cd "$(dirname "$AVON")" && pwd)/$(basename "$AVON")
ROOT=$(pwd)
fail=0

# The sets: the five the tests ship, and copies of nats, each changed once.
dirs=()
for d in bits listops lists nats quot; do dirs+=("$ROOT/tests/data/$d"); done
first=$(head -n 1 tests/data/nats/templates.tsv)
key=$(printf '%s' "$first" | cut -f1)
c=${key:10:1}
if [ "$c" = 0 ]; then flip="${key:0:10}1${key:11}"; else flip="${key:0:10}0${key:11}"; fi
tab=$'\t'
mutant() {   # name, then the line to append (or, for "key", none)
    local d="$OUT/nats-$1"
    mkdir -p "$d"
    cp tests/data/nats/template_terms.tsv tests/data/nats/main.txt "$d/"
    if [ "$1" = key ]; then
        { printf '%s\n' "$first" | sed "s/^$key/$flip/"; tail -n +2 tests/data/nats/templates.tsv; } \
            > "$d/templates.tsv"
    else
        { cat tests/data/nats/templates.tsv; printf '%s\n' "$2"; } > "$d/templates.tsv"
    fi
    dirs+=("$d")
}
mutant key ""
mutant open "$key${tab}m${tab}open${tab}3${tab}0,1,2${tab}\`\`v2 v0 v5"
mutant formals "$key${tab}m${tab}formals${tab}3${tab}0,1${tab}\`\`v2 v0 v1"
mutant wide "$key${tab}m${tab}wide${tab}65${tab}0${tab}v0"
mutant duplicate "$first"
mutant eta "$key${tab}m${tab}eta${tab}1${tab}0${tab}\`K v0"
mutant trailing "$first x"
mutant leaf "$key${tab}m${tab}leaf${tab}1${tab}0${tab}v0"

THEOREMS="template_fire absC_eq"
axioms_ok() {
    local t
    for t in $THEOREMS; do
        grep -qE "^'AvonTemplates\\.$t' depends on axioms: \\[propext(, Quot\\.sound)?\\]$" "$OUT/lean.txt" || return 1
    done
}
if (cd "$LEAN_SKI" && lake env lean --run "$ROOT/lean/Templates.lean" "${dirs[@]}") > "$OUT/lean.txt" 2>&1 &&
    axioms_ok; then
    echo "AvonTemplates: $THEOREMS checked"
else
    echo "FAIL: lean/Templates.lean: $(head -c 400 "$OUT/lean.txt")"
    exit 1
fi

for d in "${dirs[@]}"; do
    lean=$(grep -F "$d: " "$OUT/lean.txt" | sed "s|^$d: ||")
    avon=$("$AVON" reduce --strategy=share --templates="$d" --fuel=1 "$d/main.txt" 2>&1 >/dev/null |
        sed -n 's/^templates: \([0-9]* accepted, [0-9]* refused, [0-9]* skipped\),.*/\1/p')
    name=${d#"$ROOT/"}; name=${name#"$OUT/"}
    if [ -n "$avon" ] && [ "$lean" = "$avon" ]; then
        echo "$name: $avon, the replay and Avon alike"
    else
        echo "FAIL: $name: the replay counts '$lean', Avon '$avon'"
        fail=1
    fi
done

if [ "$fail" -eq 0 ]; then echo "PASS"; else echo "FAIL"; exit 1; fi
