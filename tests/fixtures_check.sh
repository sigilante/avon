#!/usr/bin/env bash
# fixtures_check.sh: every fixture another repository's exporter writes
# regenerates byte for byte at the pinned revisions (tests/pins.sh,
# AUDIT.md item 16).  The exporters run on a copy of tests/ and jets/, so
# the checkout is never written:
#
#   tests/fixtures/       export.py: the paper's targets and the corpus
#   tests/data/           export.py: data jets' templates and words
#   tests/kernel/         export.py and entropy_export.py: kernels, pills
#   tests/selfhost/       export.py: the compiler core's terms and calls
#   tests/conformance/    skijack.export: the conformance corpus
#   tests/workloads/skilark/   skilark.export: SKIlark's workloads
#   jets/                 birds.py (with aviary's tests) and joy.py
#
# Run from the repository root.  SKIJACK and SKILARK name checkouts at
# their pins (defaults ~/skijack, ~/Code/ski/skilark); AVIARY an aviary
# checkout that holds its pin (default ~/Code/urbit/aviary), whence
# birds.py reads tests/fixtures_birds.py as of the pin.  The aviary_kernel
# Python imports must be aviary's at its pin.

set -euo pipefail
SKIJACK=${SKIJACK:-$HOME/skijack}
SKILARK=${SKILARK:-$HOME/Code/ski/skilark}
AVIARY=${AVIARY:-$HOME/Code/urbit/aviary}
export AVIARY
. tests/pins.sh
pin_check skijack "$SKIJACK" "$SKIJACK_PIN"
pin_check skilark "$SKILARK" "$SKILARK_PIN"
pin_aviary_kernel

R=$(pwd)
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
cp -Rp tests jets "$T"/
mkdir "$T/aviary-tests"
git -C "$AVIARY" show "$AVIARY_PIN:tests/fixtures_birds.py" > "$T/aviary-tests/fixtures_birds.py"
SJ="$SKIJACK/python"

echo "--- exporting"
(cd "$T" && SKIJACK_ARTIFACT_DIR="$SJ/tests/artifact" SKIJACK_PYTHON="$SJ" \
    python3 tests/fixtures/export.py > /dev/null)
(cd "$T" && PYTHONPATH="$SJ" python3 tests/data/export.py > /dev/null)
(cd "$T" && PYTHONPATH="$SJ" python3 tests/kernel/export.py > /dev/null)
(cd "$T" && PYTHONPATH="$SJ" python3 tests/kernel/entropy_export.py > /dev/null)
(cd "$T" && PYTHONPATH="$SJ" python3 tests/selfhost/export.py "$T/out/selfhost" > /dev/null)
(cd "$SJ" && python3 -m skijack.export "$T/out/conformance" > /dev/null)
(cd "$SKILARK" && PYTHONPATH="$SJ:." python3 -m skilark.export "$T/out/skilark" > /dev/null)
(cd "$T" && PYTHONPATH="$SJ" python3 jets/birds.py "$T/aviary-tests" > /dev/null)
(cd "$T" && PYTHONPATH="$SJ:$SKILARK" python3 jets/joy.py > /dev/null)

# every committed file of DIR, against the export's copy in OUT
fail=0 files=0
same() {
    local dir=$1 out=$2 f
    for f in $(git -C "$R" ls-files "$dir"); do
        case $f in *.py|*.ascii.ski|*/__pycache__/*) continue ;; esac
        files=$((files + 1))
        if ! cmp -s "$R/$f" "$out/${f#"$dir"/}"; then
            echo "FAIL: $f is not what the pinned exporter writes" >&2
            fail=1
        fi
    done
}
for d in tests/fixtures tests/data tests/kernel; do same "$d" "$T/$d"; done
same jets "$T/jets"
same tests/selfhost "$T/out/selfhost"
same tests/conformance "$T/out/conformance"
same tests/workloads/skilark "$T/out/skilark"
[ $fail -eq 0 ] || exit 1
echo "fixtures check passed: $files files, each as the pinned exporters write it"
