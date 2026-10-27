"""Fixtures for tests/test_data.c: data jets.

    PYTHONPATH=~/skijack/python python3 tests/data/export.py

For each program here, NAME.ascii.ski, writes NAME/: its templates
(templates.tsv, template_terms.tsv), its numeral operations (words.tsv,
when it names any), and each of its names main, lazy, long, out, eqB,
trGet and eqId that it defines as NAME.txt, printed: main, lazy and long
applied to the atoms Tt Ff (each checks itself and is True, Ff, the second
of `False | True`), the rest bare: out for its normal form, eqB, trGet and
eqId for the bit-string operations' terms.
"""

from __future__ import annotations

import pathlib
import sys

from aviary_kernel.terms import pretty

import skijack
from skijack.templates import templates, write, write_words

HERE = pathlib.Path(__file__).resolve().parent


def main() -> int:
    sys.setrecursionlimit(100000)
    for src in sorted(HERE.glob("*.ascii.ski")):
        name = src.name.split(".")[0]
        out = HERE / name
        out.mkdir(exist_ok=True)
        exp = skijack.compile(src.read_text(), lexicon="ascii")
        write(templates(exp), out / "templates.tsv", out / "template_terms.tsv")
        write_words(exp, out / "words.tsv")
        for nm in ("main", "lazy", "long", "out", "eqB", "trGet", "eqId"):
            if nm in exp.terms:
                tail = " Tt Ff" if nm in ("main", "lazy", "long") else ""
                (out / f"{nm}.txt").write_text(pretty(exp.terms[nm]) + tail + "\n")
        print(name, sorted(p.name for p in out.iterdir()))
    return 0


if __name__ == "__main__":
    sys.exit(main())
