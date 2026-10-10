#!/usr/bin/env bash
# smoke.sh: run every command of tests/smoke.tsv on one binary and compare
# its exit status, stdout and stderr with the recorded ones (AUDIT.md item
# 17).  `make smoke` runs it on build/avon, whose asserts are compiled out;
# the expectations are recorded from build/dbg/avon, under ASan and UBSan,
# so the release binary must behave as the checked one does.
#
#   tests/smoke.sh BIN              check BIN, from the repository root
#   tests/smoke.sh --record BIN     rewrite the expectations from BIN
#
# A line of smoke.tsv: name, exit status, SHA-256 of stdout, SHA-256 of
# stderr, and the command, run by sh with $AVON the binary and $R the
# repository root.  A command that makes files makes them in a directory
# of its own and removes it.

set -u
record=0
if [ "${1:-}" = "--record" ]; then record=1; shift; fi
[ $# -eq 1 ] || { echo "usage: tests/smoke.sh [--record] BIN" >&2; exit 2; }
R=$(pwd)
case $1 in /*) AVON=$1 ;; *) AVON=$R/$1 ;; esac
[ -x "$AVON" ] || { echo "smoke: $AVON is not executable" >&2; exit 2; }
MANIFEST=$R/tests/smoke.tsv
[ -f "$MANIFEST" ] || { echo "smoke: no $MANIFEST" >&2; exit 2; }
if command -v sha256sum >/dev/null; then sha() { sha256sum | cut -c1-64; }
else sha() { shasum -a 256 | cut -c1-64; }; fi

tmp=$(mktemp -d) || exit 2
trap 'rm -rf "$tmp"' EXIT
n=0 bad=0
while IFS=$'\t' read -r name want_rc want_out want_err cmd; do
    case $name in ''|'#'*) continue ;; esac
    n=$((n + 1))
    AVON=$AVON R=$R sh -c "$cmd" >"$tmp/out" 2>"$tmp/err"
    rc=$?
    out=$(sha <"$tmp/out") err=$(sha <"$tmp/err")
    if [ $record -eq 1 ]; then
        printf '%s\t%s\t%s\t%s\t%s\n' "$name" "$rc" "$out" "$err" "$cmd" >>"$tmp/new"
    elif [ "$rc" != "$want_rc" ] || [ "$out" != "$want_out" ] || [ "$err" != "$want_err" ]; then
        bad=$((bad + 1))
        echo "FAIL $name: exit $rc (want $want_rc)$([ "$out" = "$want_out" ] || echo ", stdout differs")$([ "$err" = "$want_err" ] || echo ", stderr differs")" >&2
        head -c 400 "$tmp/err" >&2
    fi
done < <(grep -v '^#' "$MANIFEST")

if [ $record -eq 1 ]; then
    { grep '^#' "$MANIFEST"; cat "$tmp/new"; } >"$tmp/all" && cat "$tmp/all" >"$MANIFEST"
    echo "smoke: recorded $n commands from $AVON"
    exit 0
fi
echo "smoke: $((n - bad))/$n commands as recorded, on $AVON"
[ $bad -eq 0 ]
