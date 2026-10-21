# pins.sh: the revisions the checks that need another repository run
# against, sourced by those checks and read by .github/workflows/pinned.yml.
# Every fixture here regenerates byte for byte from them
# (tests/fixtures_check.sh).  A check accepts a checkout at its pin, or at
# a descendant of it whose commits and tracked changes touch only
# documentation (see not_docs); it refuses any other, unless
# AVON_UNPINNED=1.  To move a pin, run the checks it serves at the new
# commit and change it here.

SKIJACK_PIN=72150ea6c44f78d43d54bf344a6168023a296ef0     # sigilante/SKIjack, public
SKILARK_PIN=8a988a13b73f819b82723162640605c7e195f55b     # sigilante/SKIlark, public
AVIARY_PIN=ec4b418c527408c3a513bee2735e6b0f862accda      # sigilante/aviary, public
LEAN_SKI_PIN=b7fae43a6e8d345a4bb2a350d0f38c570d2d897b    # sigilante/lean-ski, private: paper-v8
STARLINGS_PIN=0b2779ed732ed37d1eea4751ed897015e12d4cdc   # sigilante/starlings, private

# not_docs: the file names on stdin that are not documentation.
# Documentation is *.md, *.tex and *.txt, but for the .txt names lean-ski
# gives its statements, witnesses and corpora, which the checks read.
not_docs() {
    local f
    while IFS= read -r f; do
        case $f in
            *public*.txt|*witness*.txt|*corpus*.txt) echo "$f" ;;
            *.md|*.tex|*.txt) ;;
            *) echo "$f" ;;
        esac
    done
}

# pin_check NAME DIR PIN [PATH...]: DIR is a git checkout at PIN, or at a
# descendant of PIN whose commits since change only documentation, and has
# no tracked changes but to documentation (in PATH..., when given), or the
# check stops.  Renames count on both sides, so no file leaves the check
# by being renamed to documentation.
pin_check() {
    local name=$1 dir=$2 pin=$3 head dirty="" past="" changed
    shift 3
    head=$(git -C "$dir" rev-parse HEAD 2>/dev/null) || head="no git checkout"
    if changed=$(git -C "$dir" diff --no-renames --name-only HEAD -- "$@" 2>/dev/null); then
        dirty=$(printf '%s\n' "$changed" | not_docs)
    fi
    if [ "$head" != "$pin" ] && git -C "$dir" merge-base --is-ancestor "$pin" HEAD 2>/dev/null \
       && changed=$(git -C "$dir" diff --no-renames --name-only "$pin" HEAD) \
       && [ -z "$(printf '%s\n' "$changed" | not_docs)" ]; then
        past=" (${head:0:12}: documentation only since)"
    fi
    if { [ "$head" = "$pin" ] || [ -n "$past" ]; } && [ -z "$dirty" ]; then
        echo "$name at its pin, ${pin:0:12}$past"
        return 0
    fi
    echo "$name in $dir is at $head${dirty:+, with tracked changes}; the pin is $pin (tests/pins.sh)" >&2
    if [ "${AVON_UNPINNED:-0}" = 1 ]; then
        echo "AVON_UNPINNED=1: running anyway, unpinned" >&2
        return 0
    fi
    exit 1
}

# pin_aviary_kernel: the aviary_kernel Python imports is aviary's at
# AVIARY_PIN, file for file.  skijack compiles through it.  AVIARY names an
# aviary checkout (default ~/Code/urbit/aviary) to compare against.
pin_aviary_kernel() {
    local dir aviary=${AVIARY:-$HOME/Code/urbit/aviary} f bad=""
    dir=$(python3 -c 'import aviary_kernel, os; print(os.path.dirname(aviary_kernel.__file__))' 2>/dev/null) || {
        echo "no aviary_kernel importable" >&2; exit 1; }
    for f in $(git -C "$aviary" ls-tree --name-only "$AVIARY_PIN" aviary_kernel/ 2>/dev/null | grep '\.py$'); do
        git -C "$aviary" show "$AVIARY_PIN:$f" | cmp -s - "$dir/${f#aviary_kernel/}" || bad="$bad ${f#aviary_kernel/}"
    done
    [ -n "$(git -C "$aviary" ls-tree --name-only "$AVIARY_PIN" aviary_kernel/ 2>/dev/null)" ] || bad=" (no aviary checkout at $aviary)"
    if [ -z "$bad" ]; then
        echo "aviary_kernel at its pin, ${AVIARY_PIN:0:12}"
        return 0
    fi
    echo "aviary_kernel in $dir differs from aviary $AVIARY_PIN in:$bad (tests/pins.sh)" >&2
    if [ "${AVON_UNPINNED:-0}" = 1 ]; then
        echo "AVON_UNPINNED=1: running anyway, unpinned" >&2
        return 0
    fi
    exit 1
}
