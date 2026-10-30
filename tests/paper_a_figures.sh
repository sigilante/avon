#!/usr/bin/env bash
# Paper A's figures, measured at lean-ski's pin (docs/ZK-JETS.md, "Figures
# at the pin").
#
# Each statement is emitted by lean-ski's own tools from a stated witness
# (the release's witnesses are secret), at the release's heights:
#   split8:  a = b = 100, x = 200, log 17 18, with jets 17 18 14 14;
#   csplit8: a = b = 100, r = 165, seed 1, log 20 20, with jets 18 19 15 16;
#   p2pre:   lean-ski's three test vectors; the hidden hand-off's two stages.
# Avon writes every jetted and Poseidon2 table; ski-air proves and verifies
# them.  For each it prints rows, memory cells, prove time (ski-air's own
# figure), proof size, verify time (wall clock, with Lean's checks of the
# statement; in parentheses ski-air's own figure, which still includes
# Lean's comparison of the AIRs, so the proof's check alone is not timed)
# and the peak resident memory of the prover.
#
#   LEAN_SKI=~/lean-ski-at-pin tests/paper_a_figures.sh
#
# LEAN_SKI must be a lean-ski checkout at the pin (tests/pins.sh), built
# (`lake build composed skilark circuit p2run`, `cargo build --release` in
# bench/plonky3); this script runs lake and ski-air but builds nothing.
# MEMCAP_MB (default 4000) caps each step's resident memory: a step over
# it is killed and reported, not retried.  FREE_PCT (default 40) is the
# system-wide free memory each step waits for.  Run from the repository
# root, one copy at a time: the proofs are the machine's heaviest jobs.
set -euo pipefail

export LEAN_SKI=${LEAN_SKI:-$HOME/Code/ski/lean-ski}
. tests/pins.sh
pin_check lean-ski "$LEAN_SKI" "$LEAN_SKI_PIN"
LEAN_SKI=$(cd "$LEAN_SKI" && pwd)
AVON=${AVON:-build/avon}
AVON=$(cd "$(dirname "$AVON")" && pwd)/$(basename "$AVON")
OUT=${OUT:-build/paper-a}
MEMCAP_MB=${MEMCAP_MB:-4000}
FREE_PCT=${FREE_PCT:-40}
A="$LEAN_SKI/bench/plonky3/target/release/ski-air"
[ -x "$A" ] || { echo "no ski-air at $A: build it first" >&2; exit 1; }
rm -rf "$OUT"
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)

lake_ski() { (cd "$LEAN_SKI" && lake exe "$@" 2> /dev/null); }

# wait_free: until system-wide free memory is at least FREE_PCT percent.
wait_free() {
    command -v memory_pressure > /dev/null || return 0
    until [ "$(memory_pressure | awk '/free percentage/ { sub("%", "", $NF); print $NF }')" -ge "$FREE_PCT" ]; do
        sleep 20
    done
}

# capped LOG CMD...: run CMD with its output in LOG; kill it past MEMCAP_MB.
# Appends "wall SECONDS" and "peak MB" to LOG; returns CMD's status, 137
# when killed.
capped() {
    local log=$1; shift
    wait_free
    local t0 peak=0 kb pids
    t0=$(perl -MTime::HiRes=time -e 'printf "%.2f", time')
    "$@" > "$log" 2>&1 &
    local root=$!
    tree() { echo "$1"; for c in $(pgrep -P "$1"); do tree "$c"; done; }
    while kill -0 "$root" 2> /dev/null; do
        # the step may exit between the checks: ps then finds nothing
        pids=$(tree "$root" | paste -sd, -) || true
        kb=$(ps -o rss= -p "$pids" 2> /dev/null | awk '{ s += $1 } END { print s + 0 }') || kb=0
        [ $((kb / 1024)) -gt "$peak" ] && peak=$((kb / 1024))
        if [ "$peak" -gt "$MEMCAP_MB" ]; then
            for p in $(tree "$root"); do kill -9 "$p" 2> /dev/null || true; done
            wait "$root" 2> /dev/null || true
            echo "peak $peak" >> "$log"; echo "killed" >> "$log"
            return 137
        fi
        sleep 0.2
    done
    local rc=0
    wait "$root" || rc=$?
    echo "wall $(perl -MTime::HiRes=time -e "printf '%.2f', time - $t0")" >> "$log"
    echo "peak $peak" >> "$log"
    return $rc
}

field() { grep -oE "$2" "$1" | head -n 1 | grep -oE '[0-9][0-9.]*' | head -n 1; }
size() { stat -f %z "$1" 2> /dev/null || stat -c %s "$1"; }
row() { echo "| $* |"; }

echo "Paper A's figures at lean-ski $(git -C "$LEAN_SKI" rev-parse --short HEAD), Avon $(git rev-parse --short HEAD), $(date +%Y-%m-%d)"
echo
echo "| statement | circuit | rows | memory cells | prove | proof | verify | prover peak |"
echo "|---|---|---:|---:|---:|---:|---:|---:|"

# --- the split predicates, plain and jetted
skilark_case() {
    local name=$1 dir=$OUT/$1 src=$LEAN_SKI/release/skilark/$1/source.ski lp=$2 li=$3
    shift 3
    mkdir -p "$dir"
    lake_ski skilark "$@" "$dir" > "$dir/emit.log"
    lake_ski composed budget "$dir/public.txt" "$lp" "$li" "$dir/jets.public.txt" > /dev/null
    lake_ski skilark cjets "$src" "$dir/jets.public.txt" "$dir/jets.txt" > /dev/null

    if capped "$dir/plain.prove" "$A" composed-prove "$dir/public.txt" "$dir/witness.txt" "$dir/plain.proof"; then
        capped "$dir/plain.verify" "$A" composed-verify "$dir/public.txt" "$dir/plain.proof" || true
        grep -q '^VERIFIED' "$dir/plain.verify" || echo "FAIL: $name plain did not verify" >&2
        row "$name | plain | $(field "$dir/plain.prove" 'proved [0-9]+ rows') | $(field "$dir/plain.prove" '[0-9]+ memory cells') | $(field "$dir/plain.prove" 'in [0-9.]+ s') s | $(size "$dir/plain.proof") B | $(field "$dir/plain.verify" '^wall [0-9.]+') s | $(field "$dir/plain.prove" '^peak [0-9]+') MB"
    else
        row "$name | plain | | | over ${MEMCAP_MB} MB, not run | | | > ${MEMCAP_MB} MB"
    fi

    "$AVON" witness --statement="$dir/jets.public.txt" --jet-table="$dir/jets.txt" "$dir/witness.txt" \
        > "$dir/avon.txt" 2> "$dir/avon.err"
    if capped "$dir/jets.prove" "$A" compj-prove-table "$dir/jets.public.txt" "$dir/jets.txt" "$src" \
            "$dir/avon.txt" "$dir/jets.proof"; then
        capped "$dir/jets.verify" "$A" compj-verify "$dir/jets.public.txt" "$dir/jets.txt" "$src" "$dir/jets.proof" || true
        grep -q '^VERIFIED' "$dir/jets.verify" || echo "FAIL: $name jets did not verify" >&2
        row "$name | jets: $(field "$dir/avon.err" 'insts [0-9]+') instantiations, $(field "$dir/avon.err" 'pops [0-9]+') pops, $(field "$dir/avon.err" 'written [0-9]+') written | $(field "$dir/avon.err" 'rows [0-9]+') | $(field "$dir/avon.err" 'cells [0-9]+') | $(field "$dir/jets.prove" 'in [0-9.]+ s') s | $(size "$dir/jets.proof") B | $(field "$dir/jets.verify" '^wall [0-9.]+') s (AIRs and proof $(field "$dir/jets.verify" '; [0-9.]+ s\)') s) | $(field "$dir/jets.prove" '^peak [0-9]+') MB"
    else
        row "$name | jets | $(field "$dir/avon.err" 'rows [0-9]+') | $(field "$dir/avon.err" 'cells [0-9]+') | over ${MEMCAP_MB} MB, not run | | | > ${MEMCAP_MB} MB"
    fi
}

skilark_case split8 14 14 emit "$LEAN_SKI/release/skilark/split8/source.ski" 8 200 100 100 17 18
skilark_case csplit8 15 16 cemit "$LEAN_SKI/release/skilark/csplit8/source.ski" 8 8 1 200 100 100 165 20 20

# --- the Poseidon2 jet: three test vectors and the hidden hand-off
for k in 0 1 2; do
    d=$OUT/p2/v$k
    mkdir -p "$d"
    lake_ski composed emit-p2 "$d" "$k" > /dev/null
    "$AVON" witness --statement="$d/p2pre.public.txt" "$d/p2pre.witness.txt" > "$d/avon.txt" 2> "$d/avon.err"
    capped "$d/prove" "$A" compp-prove-table "$d/p2pre.public.txt" "$d/avon.txt" "$d/p.proof"
    capped "$d/verify" "$A" compp-verify "$d/p2pre.public.txt" "$d/p.proof" || true
    grep -q ': VERIFIED in' "$d/verify" || echo "FAIL: p2pre vector $k did not verify" >&2
    row "p2pre, vector $k | Poseidon2 jet, $(field "$d/avon.err" 'jet calls [0-9]+') call | $(field "$d/avon.err" 'rows [0-9]+') | $(field "$d/avon.err" 'cells [0-9]+') | $(field "$d/prove" 'in [0-9.]+ s') s | $(size "$d/p.proof") B | $(field "$d/verify" '^wall [0-9.]+') s (AIRs and proof $(field "$d/verify" 'VERIFIED in [0-9.]+ s') s) | $(field "$d/prove" '^peak [0-9]+') MB"
done

d=$OUT/p2/handoff
mkdir -p "$d"
lake_ski composed emit-handoff "$d" > /dev/null
for n in handoff1 handoff2; do
    "$AVON" witness --statement="$d/$n.public.txt" "$d/handoff.witness.txt" > "$d/$n.txt" 2> "$d/$n.err"
    capped "$d/$n.prove" "$A" compp-prove-table "$d/$n.public.txt" "$d/$n.txt" "$d/$n.proof"
    row "hand-off, stage ${n#handoff} | Poseidon2 jet, $(field "$d/$n.err" 'jet calls [0-9]+') call | $(field "$d/$n.err" 'rows [0-9]+') | $(field "$d/$n.err" 'cells [0-9]+') | $(field "$d/$n.prove" 'in [0-9.]+ s') s | $(size "$d/$n.proof") B | | $(field "$d/$n.prove" '^peak [0-9]+') MB"
done
capped "$d/chain" "$A" compp-chain "$d/handoff1.public.txt" "$d/handoff1.proof" "$d/handoff2.public.txt" "$d/handoff2.proof" || true
grep -q '^CHAIN OK' "$d/chain" || echo "FAIL: the hand-off's proofs did not verify as a chain" >&2

# --- a wrong preimage runs until the heights stop it
d=$OUT/p2/v0
awk 'NR == 1 { $0 = ($0 == "1") ? "0" : "1" } { print }' "$d/p2pre.witness.txt" > "$d/bad.txt"
"$A" compp-prove "$d/p2pre.public.txt" "$d/bad.txt" "$d/bad.proof" > "$d/bad.log" 2>&1 || true
echo
echo "A wrong preimage (vector 0, first bit flipped): $(grep -oE '[0-9]+ rows, [0-9]+ memory cells' "$d/bad.log" | head -n 1) before ski-air stops it at the statement's heights."

# --- the permutation in SKI, without the jet, under Avon's graph reduction
echo
echo "| vector | Poseidon2 in SKI: contractions | wall | peak |"
echo "|---|---:|---:|---:|"
for k in 0 1 2; do
    d=$OUT/p2run/$k
    mkdir -p "$d"
    lake_ski p2run "$k" "$d" > /dev/null
    if capped "$d/run" "$AVON" reduce "$d/p2.dag"; then
        row "$k | $(field "$d/run" 'NORMAL [0-9]+') | $(field "$d/run" '^wall [0-9.]+') s | $(field "$d/run" '^peak [0-9]+') MB"
    else
        row "$k | over ${MEMCAP_MB} MB, not run | | > ${MEMCAP_MB} MB"
    fi
done
