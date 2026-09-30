"""Run the Reduceron ports in Avon (docs/BENCHMARK.md).

    python3 run.py --avon ../../../build/avon --skijack ~/skijack [--reps 5]

Compiles each port with skijack, writes its supercombinator templates, and
reduces ``main Tt Ff`` to weak head normal form in share mode, as SKI and
with ``--templates``, best of ``--reps`` user CPU, interleaved.  Every port's
main is a check that returns True, the second constructor of ``bool``, so
the expected answer is ``Ff``.
"""

import argparse, os, pathlib, resource, subprocess, sys, tempfile

HERE = pathlib.Path(__file__).resolve().parent
PROGS = ("ordlist", "queens2", "taut", "clausify", "permsort")


def build(skijack: pathlib.Path, prog: str, out: pathlib.Path) -> None:
    sys.path.insert(0, str(skijack / "python"))
    sys.setrecursionlimit(1_000_000)
    import skijack as sj
    from aviary_kernel.terms import pretty
    from skijack.templates import templates, write
    exp = sj.compile((HERE / f"{prog}.ascii.ski").read_text(), lexicon="ascii")
    out.mkdir(parents=True, exist_ok=True)
    (out / "main.ski").write_text(pretty(exp.terms["main"]) + " Tt Ff\n")
    write(templates(exp), out / "templates.tsv", out / "template_terms.tsv")


def run(avon: str, d: pathlib.Path, tmpl: bool):
    args = [avon, "reduce", "--whnf"] + ([f"--templates={d}"] if tmpl else []) + [str(d / "main.ski")]
    u0 = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime
    out = subprocess.run(args, capture_output=True, text=True, check=True)
    u = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime - u0
    status, steps = out.stdout.split("\n")[0].split()
    inst = out.stderr.split("; ")[1].split()[0] if tmpl else "0"
    return steps, int(inst), out.stdout.split("\n")[1], u


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--avon", required=True)
    ap.add_argument("--skijack", type=pathlib.Path, default=pathlib.Path.home() / "skijack")
    ap.add_argument("--reps", type=int, default=5)
    ap.add_argument("--only", default=",".join(PROGS))
    a = ap.parse_args()
    progs = a.only.split(",")
    tmp = pathlib.Path(tempfile.mkdtemp(prefix="reduceron-"))
    for p in progs:
        build(a.skijack, p, tmp / p)
    best, seen, ok = {}, {}, True
    for _ in range(a.reps):
        for p in progs:
            for tmpl in (False, True):
                steps, inst, res, u = run(a.avon, tmp / p, tmpl)
                if res != "Ff":
                    print(f"{p}: answer {res}, expected Ff", file=sys.stderr)
                    ok = False
                seen[p, tmpl] = (steps, inst)
                best[p, tmpl] = min(best.get((p, tmpl), float("inf")), u)
    print("program\tmode\tsteps\tinstantiations\tuser_s")
    for p in progs:
        for tmpl in (False, True):
            steps, inst = seen[p, tmpl]
            print(f"{p}\t{'templates' if tmpl else 'ski'}\t{steps}\t{inst}\t{best[p, tmpl]:.2f}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
