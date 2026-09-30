"""EXPERIMENT (branch experiment-knot): what the gap to the Reduceron is
made of (docs/BENCHMARK.md, "What the gap is made of").

    python3 measure.py --avon ../../../../build/avon --skijack ~/skijack [--reps 3]

Runs each port with data jets four ways -- as it is, with avon's
experimental --knot (every Y g in the loaded term rewritten to the cycle
n = g n), as a hand-made variant (small helpers inlined; Taut's names and
Queens2's tags as numerals), and the variant with --knot -- and prints the
best user time, the steps, and the time as a multiple of the Reduceron's.
Every run must answer True (Ff).
"""

import argparse, math, pathlib, resource, subprocess, sys, tempfile

HERE = pathlib.Path(__file__).resolve().parent
PORTS = HERE.parent
REDUCERON = {"ordlist": 0.98, "queens2": 1.29, "taut": 0.57, "clausify": 0.73, "permsort": 1.62}
VARIANT = {"ordlist": "ordlist_inl", "queens2": "queens2_int", "taut": "taut_int_inl",
           "clausify": "clausify_inl", "permsort": "permsort_inl"}


def build(skijack, src, out):
    sys.path.insert(0, str(skijack / "python"))
    sys.setrecursionlimit(1_000_000)
    import skijack as sj
    from aviary_kernel.terms import pretty
    from skijack.templates import templates, write, write_words
    exp = sj.compile(src.read_text(), lexicon="ascii")
    out.mkdir(parents=True, exist_ok=True)
    (out / "main.ski").write_text(pretty(exp.terms["main"]) + " Tt Ff\n")
    write(templates(exp), out / "templates.tsv", out / "template_terms.tsv")
    write_words(exp, out / "words.tsv")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--avon", required=True)
    ap.add_argument("--skijack", type=pathlib.Path, default=pathlib.Path.home() / "skijack")
    ap.add_argument("--reps", type=int, default=3)
    a = ap.parse_args()
    tmp = pathlib.Path(tempfile.mkdtemp(prefix="gap-"))
    for p, v in VARIANT.items():
        build(a.skijack, PORTS / f"{p}.ascii.ski", tmp / p)
        build(a.skijack, HERE / f"{v}.ascii.ski", tmp / v)
    cfg = {"as is": (0, []), "+knot": (0, ["--knot"]), "variant": (1, []), "variant+knot": (1, ["--knot"])}
    best, steps = {}, {}
    for _ in range(a.reps):
        for p in REDUCERON:
            for c, (var, extra) in cfg.items():
                d = tmp / (VARIANT[p] if var else p)
                u0 = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime
                r = subprocess.run([a.avon, "reduce", "--whnf", f"--templates={d}", "--data", *extra,
                                    str(d / "main.ski")], capture_output=True, text=True, check=True)
                u = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime - u0
                if r.stdout.split("\n")[1] != "Ff":
                    sys.exit(f"{p} {c}: answer {r.stdout.split(chr(10))[1]}")
                best[p, c] = min(best.get((p, c), float("inf")), u)
                steps[p, c] = int(r.stdout.split()[1])
    print("program\tconfiguration\tsteps\tuser_s\ttimes_reduceron")
    g = {c: [] for c in cfg}
    for p in REDUCERON:
        for c in cfg:
            x = best[p, c] / REDUCERON[p]
            g[c].append(x)
            print(f"{p}\t{c}\t{steps[p, c]}\t{best[p, c]:.2f}\t{x:.2f}")
    for c, v in g.items():
        print(f"geomean\t{c}\t\t\t{math.exp(sum(map(math.log, v)) / len(v)):.2f}")


if __name__ == "__main__":
    main()
