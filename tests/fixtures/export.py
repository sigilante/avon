#!/usr/bin/env python3
"""Regenerate the paper-target fixtures (docs/DESIGN.md §1, §16).

Writes t0.ski, t1.ski, t2.ski -- the printed forms of

    T0  whnfF 3 <I K>
    T1  whnfF 120 <UQ <I K>>
    T2  whnfF 500 <whnfF 3 <I K>>

as tower_harness.py builds them -- and t0.whnf, the reference host's status,
contraction count and reduced term for T0.  T1's and T2's reduced terms are
not written: their tree unfoldings run past 85 million characters (§4.1).

Also writes corpus.tsv: every distinct term skijack compiles from its corpus,
one per line as "program<TAB>name<TAB>printed term", first name wins when
several name one term (§6.2).  Programs that fail Stage A are skipped and
listed.

    python3 tests/fixtures/export.py

Requires aviary-kernel, tower_harness.py from artifact-metacircular-ski
(SKIJACK_ARTIFACT_DIR, default ~/skijack/python/tests/artifact), and the
skijack package (SKIJACK_PYTHON, default ~/skijack/python).
"""

import os
import pathlib
import sys
import threading

HERE = pathlib.Path(__file__).resolve().parent
ARTIFACT = os.path.expanduser(os.environ.get(
    "SKIJACK_ARTIFACT_DIR", "~/skijack/python/tests/artifact"))
SKIJACK = os.path.expanduser(os.environ.get("SKIJACK_PYTHON", "~/skijack/python"))


def main():
    sys.path.insert(0, ARTIFACT)
    sys.path.insert(0, SKIJACK)
    import tower_harness as T
    from aviary_kernel.terms import App, pretty

    t = App(T.I, T.K)
    targets = {
        "t0": (T.A(T.WP, T.natP(3), T.encP(t)), 340),
        "t1": (T.A(T.WP, T.natP(120), T.encP(T.A(T.UP, T.encP(t)))), 91_556),
        "t2": (T.A(T.WP, T.natP(500),
                   T.encP(T.A(T.WP, T.natP(3), T.encP(t)))), 504_930),
    }
    for name, (term, paper) in targets.items():
        (HERE / f"{name}.ski").write_text(pretty(term) + "\n")
        print(f"{name}.ski  {paper:>9,} contractions in the paper")

    r = T.fast_reduce(targets["t0"][0], T.env, max_steps=10 ** 8)
    assert r.steps == 340, r.steps
    (HERE / "t0.whnf").write_text(f"{r.status.name} {r.steps}\n{pretty(r.term)}\n")
    print("t0.whnf")

    import skijack
    from skijack import corpus
    seen, rows, skipped = set(), [], []
    stems = sorted({p.name.split(".")[0] for p in corpus.DIR.glob("*.ascii.ski")})
    for stem in stems:
        try:
            e = skijack.compile(corpus.read(stem, "ascii"), lexicon="ascii")
        except Exception as ex:                     # Stage A refusals
            skipped.append(f"{stem} ({type(ex).__name__})")
            continue
        for name, term in sorted(e.terms.items()):
            s = pretty(term)
            if s not in seen:
                seen.add(s)
                rows.append(f"{stem}\t{name}\t{s}\n")
    (HERE / "corpus.tsv").write_text("".join(rows))
    print(f"corpus.tsv   {len(rows)} distinct terms from "
          f"{len(stems) - len(skipped)} programs; skipped {', '.join(skipped)}")


if __name__ == "__main__":
    sys.setrecursionlimit(10 ** 7)
    threading.stack_size(1 << 29)
    th = threading.Thread(target=main)
    th.start()
    th.join()
