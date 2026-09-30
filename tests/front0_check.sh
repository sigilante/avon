#!/usr/bin/env bash
# The SKIjack-0 front end's acceptance (docs/DESIGN.md §20.3; skijack
# docs/SKIJACK-0.md §5): skijack's front end, a SKIjack-0 program compiled
# by Python, run in Avon's share mode,
#
#   1. compiles its own source to Python's terms, hash for hash: the fixed
#      point from source text;
#   2. compiles RANDOM random programs as skijack's spec0 does;
#   3. accepts or refuses every edge program as spec0 does;
#
# and then all three again with the front end's supercombinator templates
# (docs/DESIGN.md §6.9), which Avon checks against the terms before using,
# and with the templates and data jets (§6.10): the same terms, from fewer
# contractions.
#
# Run from the repository root after `make`.  SKIJACK defaults to
# ~/skijack, on a branch with python/skijack/selfhost/.

set -euo pipefail

SKIJACK=${SKIJACK:-$HOME/skijack}
AVON=${AVON:-build/avon}
RANDOM_PROGRAMS=${RANDOM_PROGRAMS:-1000}

if [ ! -f "$SKIJACK/python/skijack/selfhost/run0.py" ]; then
    echo "no SKIjack-0 front end in $SKIJACK (python/skijack/selfhost/run0.py)"
    exit 1
fi
fail=0
for mode in "" "--templates" "--templates --data"; do
    echo "--- the front end${mode:+, with $mode}"
    # shellcheck disable=SC2086
    PYTHONPATH="$SKIJACK/python" python3 -m skijack.selfhost.run0 \
        --avon "$AVON" --edges --random "$RANDOM_PROGRAMS" $mode || fail=1
done
if [ "$fail" = 0 ]; then
    echo "front0 check passed: the front end compiles its own source, and every program checked, as Python does: as SKI, with templates, and with templates and data jets"
else
    echo "FRONT0 CHECK FAILED"
    exit 1
fi
