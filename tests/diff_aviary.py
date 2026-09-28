#!/usr/bin/env python3
"""Differential: Avon's copy strategy against aviary_kernel.reduce, the
reference host (docs/DESIGN.md §1, §10.3).

Random {S,K,I} terms with the inert atoms X and Z, reduced to weak head
normal form and to full normal form under a fuel cap.  For every term the
status, the contraction count and the printed term reached must agree
exactly -- including the state a FUEL run stops in.  share mode is checked
against copy by tests/test_reduce.c.

    python3 tests/diff_aviary.py [N] [SEED]     (from the repository root)

Requires aviary-kernel and a built build/avon; AVON=build/dbg/avon runs
the sanitized binary instead.
"""

import os
import random
import subprocess
import sys

from aviary_kernel.environment import Environment
from aviary_kernel.reduce import reduce
from aviary_kernel.terms import App, Atom, pretty

LEAVES = ["S", "K", "I", "X", "Z"]      # X and Z are not aviary birds (§4.3)
FUELS = [3, 17, 400]
# aviary measures size as a tree walk after every contraction, which is
# exponential on a shared graph; cap it, and skip the runs the cap stops
# (SIZE is never a conformance target, DESIGN.md §3.3)
MAX_SIZE = 20000
OMEGA = App(App(App(Atom("S"), Atom("I")), Atom("I")),
            App(App(Atom("S"), Atom("I")), Atom("I")))


def gen(rnd, depth):
    if depth == 0 or rnd.random() < 0.25:
        return OMEGA if rnd.random() < 0.02 else Atom(rnd.choice(LEAVES))
    return App(gen(rnd, depth - 1), gen(rnd, depth - 1))


def avon(terms, whnf, fuel):
    cmd = [os.environ.get("AVON", "build/avon"), "batch", "--strategy=copy", f"--fuel={fuel}",
           "--budget=100000000"] + (["--whnf"] if whnf else [])
    out = subprocess.run(cmd, input="\n".join(terms) + "\n", text=True,
                         capture_output=True, check=True).stdout
    return out.splitlines()


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    rnd = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 7)
    env = Environment()
    terms = [gen(rnd, rnd.randint(1, 9)) for _ in range(n)]
    printed = [pretty(t) for t in terms]
    bad = 0
    for fuel, whnf in [(f, w) for f in FUELS for w in (True, False)]:
        got = avon(printed, whnf, fuel)
        assert len(got) == n, (len(got), n)
        tally = {}
        for t, src, line in zip(terms, printed, got):
            r = reduce(t, env, whnf_only=whnf, max_steps=fuel,
                       max_size=MAX_SIZE)
            tally[r.status.name] = tally.get(r.status.name, 0) + 1
            if r.status.name == "SIZE":
                continue
            want = f"{r.status.name} {r.steps} {pretty(r.term)}"
            if line != want:
                bad += 1
                if bad <= 10:
                    print(f"MISMATCH ({'whnf' if whnf else 'nf'}) {src}\n"
                          f"  avon   {line[:200]}\n  aviary {want[:200]}")
        mode = "whnf" if whnf else "normal form"
        print(f"fuel {fuel:>3}, {mode:>11}: {n} terms, statuses {tally}"
              " (SIZE skipped)" if "SIZE" in tally else
              f"fuel {fuel:>3}, {mode:>11}: {n} terms, statuses {tally}")
    print(f"{bad} mismatches")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    sys.setrecursionlimit(100000)
    main()
