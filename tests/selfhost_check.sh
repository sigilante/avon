#!/usr/bin/env bash
# Stage 8's corpus acceptance (docs/DESIGN.md §20.3): every bracket
# abstraction skijack performs compiling its corpus, run in Avon through the
# compiler's core as a term -- tests/selfhost/abstract.ascii.ski, compiled
# by skijack -- gives Python's result, hash for hash; and so does the
# compiler jet, every fire checked against the term.
#
#   1. tests/selfhost/export.py records the outermost bracket abstractions
#      of compiling the compiler's own source and every corpus program that
#      compiles, each distinct call once;
#   2. build/avon selfhost runs each through the term, then through the
#      jet with --jet-check=1, and compares the decoded result's hash.
#
# Run from the repository root after `make`.  SKIJACK defaults to
# ~/skijack (its python/ package is the compiler that records the calls).

set -euo pipefail

SKIJACK=${SKIJACK:-$HOME/skijack}
AVON=${AVON:-build/avon}
OUT=${OUT:-build/selfhost}

rm -rf "$OUT"
mkdir -p "$OUT"
PYTHONPATH="$SKIJACK/python" python3 tests/selfhost/export.py "$OUT" --corpus
fail=0
for calls in own corpus; do
    echo "--- $calls: the compiler term"
    "$AVON" selfhost "$OUT" "$OUT/$calls.tsv" || fail=1
    echo "--- $calls: the compiler jet, every fire checked"
    "$AVON" selfhost --jets --jet-check=1 "$OUT" "$OUT/$calls.tsv" || fail=1
done
if [ "$fail" != 0 ]; then
    echo "SELFHOST CHECK FAILED"
    exit 1
fi
echo "selfhost check passed: the compiler term and its jet give every abstraction of the corpus's compilation, and of their own"
