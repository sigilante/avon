"""Joy's word list as jets (docs/DESIGN.md §6.8), from SKIlark.

    PYTHONPATH=~/skijack/python:~/skilark python3 jets/joy.py

The census ranks by what a corpus calls, and SKIlark's corpus is eight
programs; the words a Joy machine makes primitive are jetted whether or
not these programs lean on them.  From every SKIlark form (phase 1's
kernel, the interpreted and the compiled front ends) this takes the terms
of:

  the word constructors  Dup Swap Pop Qcons Cat Unit Dip Do Ifz Lit Quote Add
  their compiled bodies  wDup wSwap ... wAdd (the compiled form's words)
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
         "Lit", "Quote", "Add"]
WORDS = (CTORS + ["w" + c for c in CTORS]
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
