#!/usr/bin/env bash
# Frame traces against the pure-S paper's hider census (docs/DESIGN.md §22),
# in the order that localizes a mismatch:
#
#   1. enumeration: avon enum N gives the census's closed terms, in its order;
#   2. traces: every closed f of size 1..N, avon's trace of f X equals the
#      census's run line for line, and its exit; then sizes 1..10 at short
#      horizons, where runs end on the horizon's edge (an OPEN at step H-1);
#   3. verdicts: the census through avon (tests/hider/client.py) gives the
#      census's classify(f), verdict, exit and trail;
#   4. the streaming census (avon enum into avon, as client.py census runs)
#      gives the same, term by term;
#   5. the five named cases.
#
# Run from the repository root after `make`.  HIDER_SCRIPTS names the
# paper's scripts/ directory, in a starlings checkout at its pin
# (tests/pins.sh); HIDER_N the largest size (default 12).

set -euo pipefail
AVON=${AVON:-build/avon}
N=${HIDER_N:-12}
SCRIPTS=${HIDER_SCRIPTS:-}
if [ -z "$SCRIPTS" ] || [ ! -f "$SCRIPTS/fixed_points_hider.py" ]; then
    echo "no hider census at '$SCRIPTS': set HIDER_SCRIPTS to the paper's scripts/"
    exit 1
fi
. tests/pins.sh
# the census and what it imports
pin_check starlings "$SCRIPTS" "$STARLINGS_PIN" fixed_points.py fixed_points_hider.py \
    verify_murmuration_i.py ../starling_machines.py
export HIDER_SCRIPTS="$SCRIPTS"
P="python3 tests/hider/parity.py"
$P enum "$N" --avon "$AVON"
$P trace "$N" --avon "$AVON"
for H in 1 2 3 4 5 6 7 8 10 13 21; do $P trace 10 "$H" --avon "$AVON"; done
$P verdict "$N" --avon "$AVON"
$P stream "$N" --avon "$AVON"
$P named --avon "$AVON"
echo "hider check passed: enumeration, traces, verdicts and the named cases as the census has them"
