#!/usr/bin/env bash
# The full language's front end, by milestone (docs/WORKLIST.md, Stage 8;
# docs/DESIGN.md §20.3): skijack's front1, a SKIjack-0 program compiled by
# Python, run in Avon's share mode,
#
#   1. compiles the corpus programs of every milestone through MILESTONE to
#      the expander's terms, hash for hash;
#   2. accepts or refuses every edge program, run0's and each milestone's,
#      as the expander does, but where aviary's environment decides (M5's);
#   3. compiles RANDOM random SKIjack-0 programs and RANDOM random programs
#      of the full language as the expander does;
#   4. compiles its own source to Python's terms: the fixed point;
#
# and then all four again with the front end's supercombinator templates
# (§6.9), with the templates and data jets (§6.10), and with those and Y
# unfolded in one step (§6.11): the same terms, from fewer contractions.
#
# Run from the repository root after `make`.  SKIJACK defaults to
# ~/skijack (master since skijack #8).

set -euo pipefail

SKIJACK=${SKIJACK:-$HOME/skijack}
AVON=${AVON:-build/avon}
RANDOM_PROGRAMS=${RANDOM_PROGRAMS:-200}
MILESTONE=${MILESTONE:-M4}

if [ ! -f "$SKIJACK/python/skijack/selfhost/run1.py" ]; then
    echo "no full-language front end in $SKIJACK (python/skijack/selfhost/run1.py)"
    exit 1
fi
fail=0
for mode in "" "--templates" "--templates --data" "--templates --data --fix"; do
    echo "--- the front end${mode:+, with $mode}"
    # shellcheck disable=SC2086
    PYTHONPATH="$SKIJACK/python" python3 -m skijack.selfhost.run1 \
        --avon "$AVON" --corpus --expect "$MILESTONE" --edges \
        --random "$RANDOM_PROGRAMS" --random1 "$RANDOM_PROGRAMS" $mode || fail=1
done
if [ "$fail" = 0 ]; then
    echo "front1 check passed through $MILESTONE: the front end compiles its own source, its milestones' corpus programs and every program checked, as the expander does: as SKI, with templates, with data jets, and with Y unfolded"
else
    echo "FRONT1 CHECK FAILED"
    exit 1
fi
