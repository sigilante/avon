#!/usr/bin/env bash
# Frame traces against the pure-S paper's hider census (docs/DESIGN.md §22),
# in the order that localizes a mismatch:
#
#   1. enumeration: avon enum N gives the census's closed terms, in its order;
#   2. traces: every closed f of size 1..N, avon's trace of f X equals the
#      census's run line for line, and its exit;
#   3. verdicts: the census through avon (tests/hider/client.py) gives the
#      census's classify(f), verdict, exit and trail;
#   4. the five named cases.
#
# Run from the repository root after `make`.  HIDER_SCRIPTS names the
# paper's scripts/ directory; HIDER_N the largest size (default 12).

set -euo pipefail
AVON=${AVON:-build/avon}
N=${HIDER_N:-12}
SCRIPTS=${HIDER_SCRIPTS:-"$HOME/Documents/Davis2026 Universality of the Pure S Calculus/scripts"}
if [ ! -f "$SCRIPTS/fixed_points_hider.py" ]; then
    echo "no hider census at $SCRIPTS (fixed_points_hider.py)"
    exit 1
fi
export HIDER_SCRIPTS="$SCRIPTS"
P="python3 tests/hider/parity.py"
$P enum "$N" --avon "$AVON"
$P trace "$N" --avon "$AVON"
$P verdict "$N" --avon "$AVON"
$P named --avon "$AVON"
echo "hider check passed: enumeration, traces, verdicts and the named cases as the census has them"
