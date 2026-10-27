"""Self-hosting fixtures.

    PYTHONPATH=~/skijack/python python3 tests/selfhost/export.py OUTDIR [--corpus]

`abstract.ascii.ski` (this directory) is the compiler's core written in
SKIjack: bracket abstraction, aviary's algorithm with eta, over encoded
terms.  skijack compiles every equation by bracket abstraction
(aviary_kernel.abstraction.expand abstracts each formal in turn), so a
compilation is a sequence of calls [x] body -> result.  This records the
outermost calls skijack makes

- compiling `abstract.ascii.ski` itself: the fixed point, that the
  compiler term reproduces every abstraction of its own compilation
  (OUTDIR/own.tsv);
- with --corpus, compiling every program of skijack's corpus that
  compiles, each distinct call once (OUTDIR/corpus.tsv),

and writes the compiler's terms: `abs`, the constructors of its term
type (`TS TK TI TV TA`, application fields `Ap`) and of `nat` (`Zero
Suc`), the event constructor `Abs` (as `AbsEvent.skit`: a file system
that ignores case would make `Abs.skit` and `abs.skit` one file), and
`pill.skit`, the compiler in a
pill: `K kernel`, whose event `Abs x t` has the effect `Out ([vx] t)`.
A call is a line `x <TAB> body <TAB> result-hash <TAB> result`: its atoms
renamed v0, v1, ... in order of appearance, the binder first, so `x` is
the binder's number; the result's skijack-1 hash, and (in own.tsv) the
result printed.
"""

from __future__ import annotations

import pathlib
import sys

import aviary_kernel.abstraction as AB
from aviary_kernel.terms import App, Atom, pretty

import skijack
from skijack import corpus
from skijack.dictionary import structural_hash
from skijack.export import jam

HERE = pathlib.Path(__file__).resolve().parent


def recording():
    """Patch bracket abstraction to record its outermost calls: aviary's,
    and skijack's own reference to it, by which its expander abstracts each
    formal over a body whose references are still atoms (skijack #36)."""
    import skijack.expand as SX
    calls, depth = [], [0]
    real = AB.bracket_abstract

    def rec(x, body):
        depth[0] += 1
        try:
            r = real(x, body)
        finally:
            depth[0] -= 1
        if depth[0] == 0:
            calls.append((x, body, r))
        return r
    AB.bracket_abstract = rec
    SX._bracket_abstract = rec

    def restore():
        AB.bracket_abstract = real
        SX._bracket_abstract = real
    return calls, restore


def renamed(x, body, result):
    names = {x: 0}

    def go(t, grow):
        if isinstance(t, Atom):
            if t.name in ("S", "K", "I"):
                return t
            if t.name not in names:
                if not grow:
                    raise ValueError(f"the result has a new atom {t.name}")
                names[t.name] = len(names)
            return Atom(f"v{names[t.name]}")
        return App(go(t.fn, grow), go(t.arg, grow))
    return go(body, True), go(result, False)


def lines(calls, with_text):
    out, seen = [], set()
    for x, body, result in calls:
        b, r = renamed(x, body, result)
        key = pretty(b)
        if key in seen:
            continue
        seen.add(key)
        row = ["0", key, structural_hash(r)]
        if with_text:
            row.append(pretty(r))
        out.append("\t".join(row) + "\n")
    return out


def main(argv) -> int:
    if not argv or argv[0].startswith("-"):
        print(__doc__, file=sys.stderr)
        return 2
    outdir = pathlib.Path(argv[0])
    outdir.mkdir(parents=True, exist_ok=True)
    src = (HERE / "abstract.ascii.ski").read_text()

    calls, restore = recording()
    try:
        e = skijack.compile(src, lexicon="ascii")
    finally:
        restore()
    for name in ("abs", "TS", "TK", "TI", "TV", "TA", "Ap", "Zero", "Suc"):
        (outdir / f"{name}.skit").write_bytes(jam(e.terms[name]))
    # `Abs` and `abs` are one file name where file names ignore case
    (outdir / "AbsEvent.skit").write_bytes(jam(e.terms["Abs"]))
    # the compiler in a pill: K kernel, a kernel whatever the subject
    (outdir / "pill.skit").write_bytes(jam(App(Atom("K"), e.terms["kernel"])))
    own = lines(calls, True)
    (outdir / "own.tsv").write_text("".join(own))
    print(f"own: {len(calls)} calls, {len(own)} distinct")

    if "--corpus" in argv:
        calls, restore = recording()
        compiled = 0
        try:
            stems = sorted({p.name.split(".")[0] for p in corpus.DIR.glob("*.ascii.ski")})
            for stem in stems:
                try:
                    skijack.compile(corpus.read(stem, "ascii"), lexicon="ascii")
                    compiled += 1
                except Exception:           # Stage A refusals, as export.py's
                    continue
        finally:
            restore()
        rows = lines(calls, False)
        (outdir / "corpus.tsv").write_text("".join(rows))
        print(f"corpus: {compiled} programs, {len(calls)} calls, {len(rows)} distinct")
    return 0


if __name__ == "__main__":
    sys.setrecursionlimit(1_000_000)
    sys.exit(main(sys.argv[1:]))
