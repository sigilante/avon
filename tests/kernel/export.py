"""Kernel fixtures for Avon's stage 7 (docs/DESIGN.md §9, §20).

    PYTHONPATH=~/skijack/python python3 tests/kernel/export.py

Runs skijack's reference loop over two kernels and writes what it saw, so
tests/test_kernel.c can do the same with Avon and compare:

- `kernel-events` (skijack's corpus), the sequence
  `test_examples::test_a_runtime_can_poke_the_kernel_with_events_it_builds`
  runs: Tick, Poke 5, Tick, a peek, and `load` of an old state onto the
  first kernel's battery, then Tick;
- `install.ascii.ski` (this directory): a kernel whose `Run d` event takes
  a quoted program d -- what the compiler emitted for `double` and
  `triple` -- makes it live with `UQ` and applies it to the state: Tick,
  Run <double>, Run <triple>, Tick.  It is compiled without Stage B,
  which cannot type a decoded term: installed code is untyped, as a Nock
  formula run with `.*` is.

Each pull is `(n@k) k arg`, `n@k` the Scott pair selectors `hd` and `tl`
as the ABI compiles an axis, reduced by the reference host (`run_level0`,
copy semantics, weak head normal form).  Writes SKIT files and
`expected.tsv`, `name <TAB> value` lines: each poke's contractions, the
state it leaves (a numeral), its effects' constructor and the effect's
payload; the peek's; the load's.  Also `pill.skit`, `K kernel`: a pill
whose value, applied to any subject, is the events kernel.
"""

from __future__ import annotations

import pathlib
import sys

from aviary_kernel.terms import App, Atom

import skijack
from skijack import corpus
from skijack.export import jam
from skijack.parser import parse
from skijack.probe import Prober
from skijack.run import peel, run_level0

HERE = pathlib.Path(__file__).resolve().parent
POKE, PEEK, LOAD, STATE = 4, 10, 11, 3
MAX = 200_000


def axis(n, t, hd, tl):
    for bit in bin(n)[3:]:
        t = App(tl if bit == "1" else hd, t)
    return t


class Loop:
    def __init__(self, e, src, lx="ascii"):
        self.e = e
        self.pr = Prober(e)
        self.decl = {d.name: d for d in parse(src, lx).decls if hasattr(d, "ctors")}
        self.hd, self.tl = e.terms["hd"], e.terms["tl"]

    def pull(self, arm, k, arg):
        return App(App(axis(arm, k, self.hd, self.tl), k), arg)

    def state(self, k):
        return self.pr.read_nat(axis(STATE, k, self.hd, self.tl))

    def inject(self, k, event):
        out = run_level0(self.pull(POKE, k, event), MAX)
        assert out.whnf
        k2 = App(self.tl, out.term)
        ctor, fields = peel(App(self.hd, out.term), self.decl["effects"])
        effect = "-"
        if fields:
            name, payload = peel(fields[0], self.decl["effect"])
            effect = f"{name}:{self.pr.read_nat(payload[0])}"
        return out.steps, k2, self.state(k2), ctor, effect


def main() -> int:
    rows = []

    def record(prefix, result):
        steps, _k, state, ctor, effect = result
        rows.extend([(f"{prefix}.steps", steps), (f"{prefix}.state", state),
                     (f"{prefix}.effects", ctor), (f"{prefix}.effect", effect)])

    # the events kernel, as skijack's test runs it
    src = (corpus.DIR / "kernel-events.ascii.ski").read_text()
    e = skijack.compile(src, lexicon="ascii")
    L = Loop(e, src)
    k0 = e.terms["kernel"]
    poke5 = App(e.terms["Poke"], L.pr.nat(5))
    terms = {"events.kernel": k0, "events.tick": e.terms["Tick"],
             "events.poke5": poke5, "events.zero": e.terms["Zero"],
             "hd": e.terms["hd"], "tl": e.terms["tl"],
             "pill": App(Atom("K"), k0)}
    r1 = L.inject(k0, e.terms["Tick"]); record("events.poke1", r1)
    r2 = L.inject(r1[1], poke5); record("events.poke2", r2)
    r3 = L.inject(r2[1], e.terms["Tick"]); record("events.poke3", r3)
    peek = run_level0(L.pull(PEEK, r3[1], e.terms["Zero"]), MAX)
    rows += [("events.peek.steps", peek.steps),
             ("events.peek.value", L.pr.read_nat(L.pull(PEEK, r3[1], e.terms["Zero"])))]
    k4 = L.pull(LOAD, k0, axis(STATE, r2[1], L.hd, L.tl))
    rows.append(("events.load.state", L.state(k4)))
    record("events.load.poke", L.inject(k4, e.terms["Tick"]))
    assert (r1[0], r2[0], r3[0]) == (61, 108, 135)       # test_examples's

    # the install kernel
    isrc = (HERE / "install.ascii.ski").read_text()
    ie = skijack.compile(isrc, lexicon="ascii", check=False)
    IL = Loop(ie, isrc)
    j0 = ie.terms["kernel"]
    run2 = App(ie.terms["Run"], ie.terms["qdouble"])
    run3 = App(ie.terms["Run"], ie.terms["qtriple"])
    terms.update({"install.kernel": j0, "install.tick": ie.terms["Tick"],
                  "install.rundouble": run2, "install.runtriple": run3,
                  "install.uq": ie.terms["UQ"], "install.qdouble": ie.terms["qdouble"],
                  "install.double": ie.terms["double"]})
    j1 = IL.inject(j0, ie.terms["Tick"]); record("install.poke1", j1)
    j2 = IL.inject(j1[1], run2); record("install.poke2", j2)
    j3 = IL.inject(j2[1], run3); record("install.poke3", j3)
    j4 = IL.inject(j3[1], ie.terms["Tick"]); record("install.poke4", j4)
    assert (j1[2], j2[2], j3[2], j4[2]) == (1, 2, 6, 7)

    for name, term in terms.items():
        (HERE / f"{name}.skit").write_bytes(jam(term))
    (HERE / "expected.tsv").write_text("".join(f"{k}\t{v}\n" for k, v in rows))
    print(f"{len(terms)} terms, {len(rows)} expectations written to {HERE}")
    return 0


if __name__ == "__main__":
    sys.setrecursionlimit(1_000_000)
    sys.exit(main())
