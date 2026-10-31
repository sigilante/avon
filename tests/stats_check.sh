#!/usr/bin/env bash
# stats_check.sh: run build/stats/avon, the build counting what becomes of
# template instances' cells (src/sstats.h), on every program of tests/data/
# with its templates and data jets, as build/avon runs it.  Each run must
# exit 0, print what build/avon prints, and report its counts: the counting
# reads the arena and must change nothing.  tests/data/lists makes list
# words, which the counting once read as jets (a bus error).
#
#   tests/stats_check.sh            from the repository root, after
#                                   `make build/avon stats`

set -u
REL=build/avon
STATS=build/stats/avon
for b in "$REL" "$STATS"; do
    [ -x "$b" ] || { echo "stats-check: no $b; run make build/avon stats" >&2; exit 2; }
done
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
fail=0 n=0
for d in tests/data/*/; do
    d=${d%/}
    main=$(ls "$d"/main.* 2>/dev/null | head -1)
    [ -n "$main" ] || continue
    n=$((n + 1))
    "$REL" reduce --whnf --templates="$d" --data "$main" > "$tmp/rel" 2> /dev/null
    rel=$?
    "$STATS" reduce --whnf --templates="$d" --data "$main" > "$tmp/stats" 2> "$tmp/err"
    st=$?
    if [ "$st" -ne "$rel" ] || ! cmp -s "$tmp/rel" "$tmp/stats" || ! grep -q '^sstats: ' "$tmp/err"; then
        echo "stats-check: $d: exit $st against $rel, or another output, or no report" >&2
        fail=1
    fi
done
if [ "$fail" = 0 ]; then
    echo "stats-check: $n programs, each as build/avon runs it, with its counts"
else
    exit 1
fi
