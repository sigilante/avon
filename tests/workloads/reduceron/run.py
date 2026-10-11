"""Run the Reduceron ports in Avon (docs/BENCHMARK.md).

    python3 run.py --avon ../../../build/avon --skijack ~/skijack [--reps 5]

Compiles each port with skijack, writes its supercombinator templates and
numeral operations, and reduces ``main Tt Ff`` to weak head normal form in
share mode four ways---as SKI, with ``--templates``, with ``--templates
--data`` (data jets), and with ``--templates --data --fix`` (Y unfolded in
one step)---best of ``--reps`` user CPU, interleaved.  Every count is its
own column: contractions and the instantiations, dispatches, numeral
operations and unfoldings among them.  With
``--inline`` the ports are compiled with skijack's inlining pass.  Every port's
main is a check that returns True, the second constructor of ``bool``, so
the expected answer is ``Ff``.
"""

import argparse, os, pathlib, resource, subprocess, sys, tempfile

HERE = pathlib.Path(__file__).resolve().parent
PROGS = ("ordlist", "queens2", "taut", "clausify", "permsort")


def build(skijack: pathlib.Path, prog: str, out: pathlib.Path, inline: bool = False) -> None:
    sys.path.insert(0, str(skijack / "python"))
    sys.setrecursionlimit(1_000_000)
    import skijack as sj
    from aviary_kernel.terms import pretty
    from skijack.templates import templates, write, write_words
    exp = sj.compile((HERE / f"{prog}.ascii.ski").read_text(), lexicon="ascii", inline=inline)
    out.mkdir(parents=True, exist_ok=True)
    (out / "main.ski").write_text(pretty(exp.terms["main"]) + " Tt Ff\n")
    write(templates(exp), out / "templates.tsv", out / "template_terms.tsv")
    write_words(exp, out / "words.tsv")


MODES = {"ski": [], "templates": ["--templates={d}"],
         "data": ["--templates={d}", "--data"],
         "fix": ["--templates={d}", "--data", "--fix"]}


def run(avon: str, d: pathlib.Path, mode: str):
    args = ([avon, "reduce", "--whnf"] + [x.format(d=d) for x in MODES[mode]]
            + [str(d / "main.ski")])
    u0 = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime
    out = subprocess.run(args, capture_output=True, text=True, check=True)
    u = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime - u0
    status, steps = out.stdout.split("\n")[0].split()
    counts = {"inst": 0, "disp": 0, "fused": 0, "ops": 0, "fix": 0}
    for line in out.stderr.splitlines():
        if line.startswith("templates:"):
            counts["inst"] = int(line.split("; ")[1].split()[0])
        if line.startswith("data:"):
            tail = line.split("; ")[2].split()
            counts["disp"], counts["ops"] = int(tail[0]), int(tail[4])
            counts["fused"] = int(tail[2].strip("("))
        if line.startswith("fix:"):
            counts["fix"] = int(line.split()[1])
    return int(steps), counts, out.stdout.split("\n")[1], u


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--avon", required=True)
    ap.add_argument("--skijack", type=pathlib.Path, default=pathlib.Path.home() / "skijack")
    ap.add_argument("--reps", type=int, default=5)
    ap.add_argument("--only", default=",".join(PROGS))
    ap.add_argument("--inline", action="store_true",
                    help="compile with skijack's inlining pass (skijack RUNTIME-DESIGN.md §10)")
    a = ap.parse_args()
    progs = a.only.split(",")
    tmp = pathlib.Path(tempfile.mkdtemp(prefix="reduceron-"))
    for p in progs:
        build(a.skijack, p, tmp / p, a.inline)
    best, seen, ok = {}, {}, True
    for _ in range(a.reps):
        for p in progs:
            for mode in MODES:
                steps, counts, res, u = run(a.avon, tmp / p, mode)
                if res != "Ff":
                    print(f"{p} {mode}: answer {res}, expected Ff", file=sys.stderr)
                    ok = False
                seen[p, mode] = (steps, counts)
                best[p, mode] = min(best.get((p, mode), float("inf")), u)
    print("program\tmode\tsteps\tinstantiations\tdispatches\tfused\tnumeral_ops\tunfoldings\tuser_s")
    for p in progs:
        for mode in MODES:
            steps, c = seen[p, mode]
            print(f"{p}\t{mode}\t{steps}\t{c['inst']}\t{c['disp']}\t{c['fused']}\t{c['ops']}"
                  f"\t{c['fix']}\t{best[p, mode]:.2f}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
