"""Joy's word list as jets, from SKIlark.

    PYTHONPATH=~/skijack/python:~/skilark python3 jets/joy.py

The census ranks by what a corpus calls, and SKIlark's corpus is eight
programs; the words a Joy machine makes primitive are jetted whether or
not these programs lean on them.  From every SKIlark form (phase 1's
kernel, the interpreted and the compiled front ends) this takes the terms
of:

  the word constructors  Dup Swap Pop Qcons Cat Unit Dip Do Lit, the
                         basis's Quote and Ifz, Joy's arithmetic,
                         comparison and truth words, Add Sub Mul ... Branch
                         Ifte, its list words, Uncons Null Small Stack
                         Unstack, the derived word in a quotation, Def, its
                         text words, Ord Chr, and Typeof and Not; the
                         kernel's literals are one, Lit, of an item, where
                         stage 5's Quote Truth Glyph Text were four more
  their compiled bodies  wDup wSwap ... wIfte (the compiled form's words)
  the primitives         add mul cat wordOf
  the derived words      over nip tuck rot sip kComb yComb

Writes jets/joy.tsv (a dictionary export) and jets/joy_names.tsv (form,
word, hash).
"""

from __future__ import annotations

import pathlib
import sys

from aviary_kernel.terms import pretty
from skijack.dictionary import from_expansion

from skilark.export import runs

HERE = pathlib.Path(__file__).resolve().parent

CTORS = ["Dup", "Swap", "Pop", "Qcons", "Cat", "Unit", "Dip", "Do", "Ifz",
         "Lit", "Quote", "Add", "Sub", "Mul", "Div", "Rem", "Eql", "Lt",
         "Truth", "Branch", "Ifte", "Uncons", "Null", "Small", "Stack",
         "Unstack", "Def", "Glyph", "Text", "Ord", "Chr", "Typeof", "Not"]
# the compiled form keeps wIfz only for programs on naturals, its list words
# only for programs on lists, its text words only for programs with
# characters and wNot only for programs with not; none of them is exported,
# and a Def compiles to its body
NOT_COMPILED = {"Ifz", "Uncons", "Null", "Small", "Stack", "Unstack", "Def",
                "Glyph", "Text", "Ord", "Chr", "Not"}
WORDS = (CTORS + ["w" + c for c in CTORS if c not in NOT_COMPILED]
         + ["add", "mul", "cat", "wordOf"]
         + ["over", "nip", "tuck", "rot", "sip", "kComb", "yComb"])


def main() -> int:
    rows, names = {}, []
    for form, run, _ in runs():
        d = from_expansion(run.e)
        have = set(d.names())
        for w in WORDS:
            if w not in have:
                continue
            e = d[w]
            rows.setdefault(e.hash, (e.size, pretty(e.term)))
            names.append((f"joy-{form}", w, e.hash))
    (HERE / "joy.tsv").write_text("".join(
        f"{h}\t{n}\t{t}\n" for h, (n, t) in sorted(rows.items())))
    (HERE / "joy_names.tsv").write_text("".join(
        f"{f}\t{w}\t{h}\n" for f, w, h in names))
    found = {w for _, w, _ in names}
    print(f"{len(names)} words across the forms, {len(rows)} distinct terms; "
          f"absent everywhere: {sorted(set(WORDS) - found) or 'none'}")
    return 0


if __name__ == "__main__":
    sys.setrecursionlimit(1_000_000)
    sys.exit(main())
