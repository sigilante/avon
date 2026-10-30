"""The drivers' fixtures: kernels, worlds, and what the reference host does.

    PYTHONPATH=~/skijack/python python3 tests/drivers/export.py [--no-inline]

Compiles each NAME.ascii.ski here with checking off (a card list holds
cells of different types, which skijack's Stage B has no type for) and
writes its kernel as NAME.skit.  Then, for each world below, runs the
kernel under skijack.drivers.run_kernel, the reference host, and writes
CASE.in (standard input), CASE.eny (entropy, if the world has it),
CASE.out and CASE.err (what the reference wrote), and a line of
expected.tsv:

    case  kernel  strategies  status  args  env

`strategies` lists the strategies the case holds for: every case holds
for copy mode, whose step count is the reference host's, and a case that
prints no step count holds for share mode too.  `args` and `env` are
comma lists, `-` for none, of hex: an argument, or NAME=VALUE, neither
ending in a newline, which the shell's `$( )` would drop.  The
kernel's name, argument 0, is its path from the repository root, as
tests/drivers_check.sh passes it.  The check runs from there.
"""

from __future__ import annotations

import pathlib
import sys

import skijack
from skijack.drivers import World, run_kernel
from skijack.export import jam

HERE = pathlib.Path(__file__).resolve().parent
INLINE = "--no-inline" not in sys.argv[1:]   # skijack's inlining pass; --no-inline turns it off

#: case, kernel, strategies, world
CASES = [
    ("echo", "echo", "copy,share", World(stdin=b"hello, world\n" * 10)),
    ("echo-bytes", "echo", "copy,share", World(stdin=bytes(range(256)))),
    ("echo-empty", "echo", "copy,share", World()),
    ("show", "show", "copy,share",
     World(argv=[b"", b"arg1"], env={b"HOME": b"/home/k"})),
    ("show-unset", "show", "copy,share", World()),
    ("show-empty", "show", "copy,share", World(env={b"HOME": b""})),
    ("bits", "bits", "copy,share",
     World(entropy=bytes(16) + bytes([0b1011, 0]) + bytes(14))),
    ("bits-none", "bits", "copy,share", World()),
    ("steps", "steps", "copy", World()),
]


def hexes(items) -> str:
    return ",".join(x.hex() for x in items) or "-"


def main() -> int:
    kernels = {}
    for src in sorted(HERE.glob("*.ascii.ski")):
        name = src.name.split(".")[0]
        e = skijack.compile(src.read_text(), lexicon="ascii", check=False, inline=INLINE)
        kernels[name] = e.terms["kernel"]
        (HERE / f"{name}.skit").write_bytes(jam(kernels[name]))
    lines = []
    for case, name, strategies, w in CASES:
        args = list(w.argv[1:])
        w.argv = [f"tests/drivers/{name}.skit".encode()] + args
        r = run_kernel(kernels[name], w)
        (HERE / f"{case}.in").write_bytes(w.stdin)
        if w.entropy is not None:
            (HERE / f"{case}.eny").write_bytes(w.entropy)
        (HERE / f"{case}.out").write_bytes(r.stdout)
        (HERE / f"{case}.err").write_bytes(r.stderr)
        env = [k + b"=" + v for k, v in w.env.items()]
        lines.append(f"{case}\t{name}\t{strategies}\t{r.status}\t{hexes(args)}\t{hexes(env)}\n")
    (HERE / "expected.tsv").write_text("".join(lines))
    print(f"{len(kernels)} kernels and {len(lines)} worlds written to {HERE}")
    return 0


if __name__ == "__main__":
    sys.setrecursionlimit(1_000_000)
    sys.exit(main())
