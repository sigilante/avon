"""Parity of avon's frame traces with the paper's hider census
(docs/DESIGN.md §22), in the order that localizes a mismatch:

    trace N [H]     every closed f of size 1..N (default 12): avon's trace of
                    f X equals the oracle's run, line for line -- L and the
                    X-headed positions against the oracle's hist, and d, D,
                    the event and the front arity against the definitions --
                    and the exit equals the oracle's.

    verdict N       every closed f of size 1..N: the census through avon
                    (tests/hider/client.py) gives the oracle's classify(f) --
                    the same verdict, exit and trail.

    named           the five named cases, each through both.

    enum N          avon enum n gives the census's closed(n), in its order,
                    for every n <= N.

    python3 tests/hider/parity.py trace 12 --avon build/avon
"""

import argparse
import subprocess
import sys
import threading
import time

import client
import oracle


def avon_blocks(avon, terms, H, extra=()):
    """avon batch --trace-frame over the terms; yields (lines, end) per term."""
    p = subprocess.Popen([avon, "batch", "--trace-frame", f"--fuel={H}", *extra],
                         stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1 << 20)

    def feed():
        for t in terms:
            p.stdin.write(t + "\n")
        p.stdin.close()
    threading.Thread(target=feed, daemon=True).start()
    cur = None
    for line in p.stdout:
        if line.startswith(">"):
            cur = []
        elif line.startswith("."):
            yield cur, line.split()
        elif line.startswith("!"):
            yield cur, ["!"]
        elif line[0].isdigit():
            cur.append(line.split())
        # '$' ends a block
    p.wait()


def parse_line(f):
    n, L, pos, d, D, ev, fa = f
    return (int(L), () if pos == "-" else tuple(int(x) for x in pos.split(",")),
            None if d == "-" else int(d), None if D == "-" else int(D), ev, int(fa))


def mode_trace(avon, N, H):
    HD = oracle.load()
    if HD is None:
        print("no oracle at", oracle.SCRIPTS); return 2
    t0 = time.time()
    terms = [f for n in range(1, N + 1) for f in HD.closed(n)]
    texts = [oracle.text((f, HD.X), HD.X) for f in terms]
    bad = 0
    for k, (got, end) in enumerate(avon_blocks(avon, texts, H)):
        f = terms[k]
        want, kind, st = oracle.lines(HD, HD.spine(f) + [HD.X], H)
        hist, hkind, hst = oracle.hist(HD, HD.spine(f) + [HD.X], H)
        why = None
        if end == ["!"]:
            why = "avon gave no trace"
        elif [parse_line(x) for x in got] != want:
            i = next((i for i, (a, b) in enumerate(zip([parse_line(x) for x in got], want)) if a != b),
                     min(len(got), len(want)))
            why = f"line {i}: avon {got[i] if i < len(got) else None}, definitions {want[i] if i < len(want) else None}"
        elif [(L, pos) for L, pos, *_ in want[:len(hist)]] != [(L, tuple(L - i for i in th)) for L, th in hist]:
            why = "the definitions disagree with the oracle's hist"
        elif kind != hkind or end[3] != kind:
            why = f"exit: avon {end[3]}, oracle {hkind}"
        elif int(end[2]) != (st + 1 if kind == "OPEN" else st):
            why = f"steps: avon {end[2]}, oracle exit at {st}"
        if why:
            bad += 1
            if bad <= 10:
                print(f"DIFFER {HD.show(f)}: {why}")
        if (k + 1) % 100000 == 0:
            print(f"  {k + 1} terms, {bad} differ, {time.time() - t0:.0f}s", flush=True)
    print(f"trace parity, sizes 1..{N}, horizon {H}: {len(terms) - bad} of {len(terms)} agree "
          f"({time.time() - t0:.0f}s)")
    return 0 if bad == 0 else 1


def mode_verdict(avon, N):
    HD = oracle.load()
    if HD is None:
        print("no oracle at", oracle.SCRIPTS); return 2
    t0 = time.time()
    av = client.Avon(avon, HD)
    bad = total = 0
    counts = {}
    for n in range(1, N + 1):
        for f in HD.closed(n):
            if len(HD._CLS) > 3000000:
                HD.clear_memos()
            key, r, tr, _info = HD.classify(f)
            got = client.classify(av, HD, f)
            total += 1
            counts[key] = counts.get(key, 0) + 1
            if got != (key, r, tr):
                bad += 1
                if bad <= 10:
                    print(f"DIFFER {HD.show(f)}: avon {got}, oracle {(key, r, tr)}")
            if total % 100000 == 0:
                print(f"  {total} terms, {bad} differ, {time.time() - t0:.0f}s", flush=True)
    av.close()
    print(f"verdict parity, sizes 1..{N}: {total - bad} of {total} agree, {av.runs} avon runs "
          f"({time.time() - t0:.0f}s)")
    print("  verdicts:", dict(sorted(counts.items())))
    return 0 if bad == 0 else 1


R10 = "S(S(SS))(S(SS))(SS)S"


def mode_named(avon):
    HD = oracle.load()
    if HD is None:
        print("no oracle at", oracle.SCRIPTS); return 2
    av = client.Avon(avon, HD)
    P = lambda s: HD.parse(s.replace("r10", "(" + R10 + ")"))

    def level0(f):
        """the trace lines of f X's run: (n, ev, fa, D)"""
        got, end = next(avon_blocks(avon, [oracle.text((f, HD.X), HD.X)], 600))
        return [(int(x[0]), x[5], int(x[6]), x[4]) for x in got], end

    fails = 0

    def check(name, ok, detail):
        nonlocal fails
        fails += not ok
        print(f"  {'ok  ' if ok else 'FAIL'} {name}: {detail}")

    cases = [
        ("r10", R10, "RIDE>FROZEN-c", lambda tr: tr[-1] == "L1:FROZEN-c", 0, None),
        ("S(S(S r10))S", "S(S(Sr10))S", "RIDE>HALT-X", None, 1, 1),
        ("S(S(S(SS)(S r10)))S", "S(S(S(SS)(Sr10)))S", "RIDE>OPEN", None, 1, 2),
        ("T(0,2)", "S(SS)(SS)(SS(SS(S(SS)(SS))))S", "RIDE>FROZEN-c",
         lambda tr: tr == ["L0:RIDE", "L1:RIDE", "L2:RIDE", "L3:FROZEN-c"], 0, None),
    ]
    for name, src, want, trail_ok, ysteps, arity in cases:
        f = P(src)
        key, r, tr, _ = HD.classify(f)
        got = client.classify(av, HD, f)
        lines, _ = level0(f)
        ys = [(n, fa) for n, ev, fa, _D in lines if ev == "y"]
        detail = f"oracle {key} {tr}; avon {got[0]} {got[2]}; level-0 y-steps {ys}"
        ok = got == (key, r, tr) and key == want and (trail_ok is None or trail_ok(tr))
        ok = ok and len(ys) == ysteps and (arity is None or (ys and ys[0] == (1, arity)))
        check(name, ok, detail)
    # S a X S, a = S(SS)(S r10): a ride that is not a level
    a = P("S(SS)(Sr10)")
    t = HD.ap(HD.S, a, HD.X, HD.S)
    got, end = next(avon_blocks(avon, [oracle.text(t, HD.X)], 600))
    ys = [x for x in got if x[5] == "y"]
    Ds = sorted({x[4] for x in got})
    check("S a X S", len(ys) == 1 and Ds == ["0"],
          f"y-steps at {[x[0] for x in ys]}, D values {Ds}, exit {end[3]}")
    av.close()
    return 0 if fails == 0 else 1


def mode_enum(avon, N):
    HD = oracle.load()
    if HD is None:
        print("no oracle at", oracle.SCRIPTS); return 2
    bad = 0
    for n in range(1, N + 1):
        out = subprocess.run([avon, "enum", str(n)], capture_output=True, text=True,
                             check=True).stdout.split("\n")[:-1]
        if [HD.parse(x.replace(" ", "")) for x in out] != HD.closed(n):
            bad += 1
            print(f"DIFFER size {n}")
    print(f"enumeration, sizes 1..{N}: {N - bad} of {N} in the census's order")
    return 0 if bad == 0 else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["trace", "verdict", "named", "enum"])
    ap.add_argument("N", type=int, nargs="?", default=12)
    ap.add_argument("H", type=int, nargs="?", default=600)
    ap.add_argument("--avon", default="build/avon")
    a = ap.parse_args()
    if a.mode == "verdict":
        return mode_verdict(a.avon, a.N)
    if a.mode == "named":
        return mode_named(a.avon)
    if a.mode == "enum":
        return mode_enum(a.avon, a.N)
    return mode_trace(a.avon, a.N, a.H)


if __name__ == "__main__":
    sys.exit(main())
