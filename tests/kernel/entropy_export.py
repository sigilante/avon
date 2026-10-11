"""The entropy kernel's fixtures.

    PYTHONPATH=~/skijack/python python3 tests/kernel/entropy_export.py

Compiles entropy.ascii.ski and writes, as SKIT, its pill (`K kernel`),
the events [1 5] (ask once), [2 7] (ask twice), [3 0] (turn greedy), [0
[5 0]] (a forged reply, which the pier must refuse), the same with a tag
that reaches 0 only past the probes' fuel, the bare I (no cell), and the
peek paths 0 to 3.  tests/test_entropy.c runs them.
"""

from __future__ import annotations

import pathlib
import sys

from aviary_kernel.terms import App, Atom

import skijack
from skijack.export import jam
from skijack.probe import Prober

HERE = pathlib.Path(__file__).resolve().parent


def main() -> int:
    src = (HERE / "entropy.ascii.ski").read_text()
    e = skijack.compile(src, lexicon="ascii", check=False)
    pr = Prober(e)
    pair = e.terms["pair"]

    def cell(a, b):
        return App(App(pair, a), b)

    n = pr.nat
    S, K, I = Atom("S"), Atom("K"), Atom("I")
    two = App(App(S, App(App(S, App(K, S)), K)), I)          # Church 2
    c65536 = App(App(App(two, two), two), two)              # 2^16
    slow_zero = App(App(two, App(c65536, I)), n(0))         # 0, but only after ~400,000 steps
    terms = {
        "entropy.pill": App(Atom("K"), e.terms["kernel"]),
        "entropy.ask5": cell(n(1), n(5)),
        "entropy.ask7twice": cell(n(2), n(7)),
        "entropy.greedy": cell(n(3), n(0)),
        "entropy.forged": cell(n(0), cell(n(5), n(0))),
        "entropy.slowzero": cell(slow_zero, cell(n(5), n(0))),
        "entropy.notacell": I,
        "entropy.path0": n(0),
        "entropy.path1": n(1),
        "entropy.path2": n(2),
        "entropy.path3": n(3),
    }
    for name, term in terms.items():
        (HERE / f"{name}.skit").write_bytes(jam(term))
    print(f"{len(terms)} terms written to {HERE}")
    return 0


if __name__ == "__main__":
    sys.setrecursionlimit(1_000_000)
    sys.exit(main())
