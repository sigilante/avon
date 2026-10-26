#!/usr/bin/env bash
# drivers_check.sh: `avon run --kernel` against the reference host's runs.
# Each line of tests/drivers/expected.tsv is a world: a kernel, its
# arguments, its environment (that and PATH, which a sanitizer reads),
# standard input from CASE.in and entropy from CASE.eny if there is one.
# BIN must write CASE.out and CASE.err byte for byte and exit with the
# status, under each strategy the line names.  tests/drivers/export.py
# writes the fixtures.  Empty arrays are spelled ${a[@]+"${a[@]}"}, which
# bash 3.2 needs under set -u.
#
#   tests/drivers_check.sh BIN       from the repository root

set -u
[ $# -eq 1 ] || { echo "usage: tests/drivers_check.sh BIN" >&2; exit 2; }
AVON=$1
D=tests/drivers
tmp=$(mktemp -d) || exit 2
trap 'rm -rf "$tmp"' EXIT
unhex() { printf '%s' "$1" | xxd -r -p; }
n=0 bad=0
while IFS=$'\t' read -r case kernel strategies status args env; do
    argv=()
    if [ "$args" != - ]; then
        IFS=, read -ra hs <<< "$args"
        for h in "${hs[@]}"; do argv+=("$(unhex "$h")"); done
    fi
    envv=()
    if [ "$env" != - ]; then
        IFS=, read -ra hs <<< "$env"
        for h in "${hs[@]}"; do envv+=("$(unhex "$h")"); done
    fi
    eny=()
    [ -f "$D/$case.eny" ] && eny=("--entropy=$D/$case.eny")
    IFS=, read -ra strats <<< "$strategies"
    for s in "${strats[@]}"; do
        n=$((n + 1))
        env -i PATH="$PATH" ${envv[@]+"${envv[@]}"} "$AVON" run --kernel --strategy="$s" \
            ${eny[@]+"${eny[@]}"} -- "$D/$kernel.skit" ${argv[@]+"${argv[@]}"} \
            < "$D/$case.in" > "$tmp/out" 2> "$tmp/err"
        got=$?
        if [ "$got" != "$status" ] || ! cmp -s "$tmp/out" "$D/$case.out" ||
           ! cmp -s "$tmp/err" "$D/$case.err"; then
            echo "drivers: $case ($s): status $got, want $status" >&2
            cmp "$tmp/out" "$D/$case.out" >&2
            cmp "$tmp/err" "$D/$case.err" >&2
            bad=$((bad + 1))
        fi
    done
done < "$D/expected.tsv"
echo "drivers: $((n - bad)) of $n runs agree with the reference host"
[ "$bad" -eq 0 ]
