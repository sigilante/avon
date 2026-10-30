"""What word cells would buy lean-ski's split predicates (docs/ZK-WORDS.md §1).

Builds the closed term each verifier runs on an honest witness -- split8's
`vsplitB x bits` and csplit8's `vcsplitB x bits` -- encoded as lean-ski's
bench/Skilark.lean encodes them (xTerm, xcTerm, boolsT, splitBits, cbits),
compiles it with skijack, and runs it in Avon three ways: plain share mode,
with the source's templates, and with templates and words (--data).
csplit8 is run at its shipped weight bound, 64, and at larger bounds, to
show how the run grows with the values its arithmetic handles.

    python3 tests/zkwords/measure.py [--bounds=64,512,4096]

SKIJACK (default ~/skijack), LEAN_SKI (default ~/Code/ski/lean-ski) and
AVON (default build/avon) name the checkouts and the binary.  Run from the
repository root.  Nothing is written outside a temporary directory.
"""

import os
import pathlib
import re
import subprocess
import sys
import tempfile
import threading

HOME = pathlib.Path.home()
SKIJACK = pathlib.Path(os.environ.get("SKIJACK", HOME / "skijack"))
LEAN_SKI = pathlib.Path(os.environ.get("LEAN_SKI", HOME / "Code/ski/lean-ski"))
AVON = os.environ.get("AVON", "build/avon")
WORDS = pathlib.Path("tests/data/nats/words.tsv")
sys.path.insert(0, str(SKIJACK / "python"))

from aviary_kernel.terms import pretty           # noqa: E402
from skijack.expand import expand_program         # noqa: E402
from skijack.parser import parse                  # noqa: E402
from skijack import templates as T                # noqa: E402


def bits_of(k, v):
    """v's k bits, least significant first (lean-ski's bitsOf)."""
    return [(v >> i) & 1 for i in range(k)]


def weights(n, seed, bound):
    """skilark.zk.weights: a linear congruential sequence (lean-ski's weightsOf)."""
    ws, s = [], seed
    for _ in range(n):
        s = (s * 1103515245 + 12345) % 2 ** 31
        ws.append(1 + s % (bound - 1))
    return ws


class Src:
    """A term in source syntax, numerals named `nnK` so none nests deeply."""

    def __init__(self):
        self.top = 0

    def num(self, d):
        self.top = max(self.top, d)
        return f"(Num nn{d})"

    def quot(self, items):
        body = f"(QUnit {items[-1]})"
        for t in reversed(items[:-1]):
            body = f"(QCons {t} {body})"
        return f"(Quot {body})"

    def numerals(self):
        return "nn0 := Zero\n" + "".join(f"nn{i} := Suc nn{i - 1}\n"
                                         for i in range(1, self.top + 1))


def bools(bits):
    """lean-ski's boolsT: the last alone, each before it paired with the rest."""
    bt = ["K" if b else "(K I)" for b in bits]
    t = bt[-1]
    for b in reversed(bt[:-1]):
        t = f"(\\pf. pf {b} {t})"
    return t


def split8(a, b, x=200, k=8):
    s = Src()

    def go(ds):
        if len(ds) == 1:
            return s.quot([s.num(ds[0])])
        return s.quot([go(ds[1:]), s.num(ds[0])])

    xs = f"(Push {go(bits_of(k, x))} Empty)"
    bits = [u for p in zip(bits_of(k, a), bits_of(k, b)) for u in p]
    return "split8", f"vsplitB {xs} {bools(bits)}", s


def csplit8(a, b, r, bound, x=200, k=8, m=8):
    s = Src()
    ws = weights(k + m, 1, bound)
    c = sum(w * d for w, d in zip(ws, bits_of(k, a) + bits_of(m, r)))

    def go_w(rs):
        if len(rs) == 1:
            return s.quot([s.num(rs[0])])
        return s.quot([go_w(rs[1:]), s.num(rs[0])])

    cw = s.quot([s.num(c), go_w(ws[k:])])

    def go_x(ps):
        w, d = ps[0]
        if len(ps) == 1:
            return s.quot([cw, s.num(w), s.num(d)])
        return s.quot([go_x(ps[1:]), s.num(w), s.num(d)])

    xs = f"(Push {go_x(list(zip(ws[:k], bits_of(k, x))))} Empty)"
    bits = [u for p in zip(bits_of(k, a), bits_of(k, b)) for u in p] + bits_of(m, r)
    return "csplit8", f"vcsplitB {xs} {bools(bits)}", s, c


def build(source, main, s, out):
    """Compile source plus `mainW := main` into out: main.txt and the templates."""
    result = {}

    def work():
        text = open(source).read() + "\n" + s.numerals() + f"\nmainW := {main}\n"
        exp = expand_program(parse(text, "ascii"))
        (out / "main.txt").write_text(pretty(exp.terms["mainW"]) + "\n")
        T.write(T.templates(exp), out / "templates.tsv", out / "template_terms.tsv")
        result["atoms"] = exp.sizes["mainW"]

    sys.setrecursionlimit(10 ** 7)
    threading.stack_size(1 << 29)
    t = threading.Thread(target=work)
    t.start()
    t.join()
    (out / "words.tsv").write_text(WORDS.read_text())
    return result["atoms"]


def run(out, *opts):
    p = subprocess.run([AVON, "reduce", "--strategy=share", *opts, str(out / "main.txt")],
                       capture_output=True, text=True, check=True)
    text = p.stdout + p.stderr
    steps = int(re.search(r"NORMAL (\d+)", text).group(1))
    ops = re.search(r"(\d+) numeral operations among", text)
    answer = p.stdout.strip().splitlines()[-1]
    return steps, int(ops.group(1)) if ops else 0, answer


def main(argv):
    bounds = [64, 512, 4096]
    for a in argv:
        if a.startswith("--bounds="):
            bounds = [int(v) for v in a.split("=", 1)[1].split(",")]
    root = LEAN_SKI / "bench/plonky3/skilark"
    cases = [(root / "split8/source.ski", *split8(100, 100), None)]
    for bound in bounds:
        name, main_t, s, c = csplit8(100, 100, 165, bound)
        cases.append((root / "csplit8/source.ski", f"{name} (weights < {bound}, c = {c})",
                      main_t, s, bound))
    print("| statement | atoms | answer | plain | templates | templates + words | operations fired |")
    print("|---|---:|---|---:|---:|---:|---:|")
    with tempfile.TemporaryDirectory() as tmp:
        for i, (source, name, main_t, s, _) in enumerate(cases):
            out = pathlib.Path(tmp) / str(i)
            out.mkdir()
            atoms = build(source, main_t, s, out)
            plain, _, ans = run(out)
            tmpl, _, ans_t = run(out, f"--templates={out}")
            data, fired, ans_d = run(out, f"--templates={out}", "--data")
            assert ans == ans_t == ans_d, (name, ans, ans_t, ans_d)
            print(f"| {name} | {atoms:,} | `{ans}` | {plain:,} | {tmpl:,} | {data:,} | {fired} |")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
