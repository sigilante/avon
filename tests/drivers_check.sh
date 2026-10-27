#!/usr/bin/env bash
# drivers_check.sh: `avon run --kernel` against the reference host's runs.
# Each line of tests/drivers/expected.tsv is a world: a kernel, its
# arguments, its environment (that and PATH, which a sanitizer reads),
# standard input from CASE.in and entropy from CASE.eny if there is one.
# BIN must write CASE.out and CASE.err byte for byte and exit with the
# status, under each strategy the line names; and so must `avon boot
# --drivers`, the run in a pier, whose reopening then ends with the same
# status, writing nothing and reading nothing.  tests/drivers/export.py
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
      for how in run pier; do
        n=$((n + 1))
        if [ $how = run ]; then
            cmd=("$AVON" run --kernel --strategy="$s")
        else
            rm -rf "$tmp/pier"
            cmd=("$AVON" boot --drivers --pier="$tmp/pier" --strategy="$s")
        fi
        env -i PATH="$PATH" ${envv[@]+"${envv[@]}"} "${cmd[@]}" \
            ${eny[@]+"${eny[@]}"} -- "$D/$kernel.skit" ${argv[@]+"${argv[@]}"} \
            < "$D/$case.in" > "$tmp/out" 2> "$tmp/err"
        got=$?
        if [ "$got" != "$status" ] || ! cmp -s "$tmp/out" "$D/$case.out" ||
           ! cmp -s "$tmp/err" "$D/$case.err"; then
            echo "drivers: $case ($s, $how): status $got, want $status" >&2
            cmp "$tmp/out" "$D/$case.out" >&2
            cmp "$tmp/err" "$D/$case.err" >&2
            bad=$((bad + 1))
        fi
        [ $how = pier ] || continue
        # the finished run reopened: replayed to its end, nothing performed
        n=$((n + 1))
        env -i PATH="$PATH" ${envv[@]+"${envv[@]}"} "$AVON" boot --drivers --pier="$tmp/pier" \
            ${eny[@]+"${eny[@]}"} < /dev/null > "$tmp/out" 2> "$tmp/err"
        got=$?
        if [ "$got" != "$status" ] || [ -s "$tmp/out" ] || [ -s "$tmp/err" ]; then
            echo "drivers: $case ($s, reopened): status $got, want $status, and no output" >&2
            cat "$tmp/err" >&2
            bad=$((bad + 1))
        fi
      done
    done
done < "$D/expected.tsv"

# A crash: echo in a pier, killed while it waits on its second read, then
# reopened with the rest of its input.  The reopened run replays to that
# read, writing nothing again, and goes on: the two runs' output is the
# output of one run on the whole input.
abc() { head -c 64 /dev/zero | tr '\0' "$1"; }
for s in copy share; do
    n=$((n + 1))
    rm -rf "$tmp/cp" "$tmp/fifo"
    mkfifo "$tmp/fifo"
    "$AVON" boot --drivers --pier="$tmp/cp" --strategy="$s" -- "$D/echo.skit" \
        < "$tmp/fifo" > "$tmp/out1" 2> "$tmp/err1" &
    pid=$!
    exec 3> "$tmp/fifo"
    abc A >&3
    for _ in $(seq 200); do
        [ "$(wc -c < "$tmp/out1")" -ge 67 ] && break
        sleep 0.05
    done
    kill -9 "$pid" 2>/dev/null
    wait "$pid" 2>/dev/null
    exec 3>&-
    abc B | "$AVON" boot --drivers --pier="$tmp/cp" > "$tmp/out2" 2> "$tmp/err2"
    got=$?
    { printf 'hi\n'; abc A; } > "$tmp/want1"
    abc B > "$tmp/want2"
    if [ "$got" != 0 ] || ! cmp -s "$tmp/out1" "$tmp/want1" || ! cmp -s "$tmp/out2" "$tmp/want2" ||
       [ -s "$tmp/err1" ] || [ -s "$tmp/err2" ]; then
        echo "drivers: echo ($s), killed and reopened: status $got" >&2
        cat "$tmp/err1" "$tmp/err2" >&2
        bad=$((bad + 1))
    fi
done
echo "drivers: $((n - bad)) of $n runs agree with the reference host"
[ "$bad" -eq 0 ]
