"""The hider census driven by avon's frame traces (docs/DESIGN.md §22).

The census's run/descend/classify (fixed_points_hider.py), with each head
run done by avon --trace-frame instead of in Python.  Every decision the
census makes is made here the way it makes it, on the oracle's own objects
and with the oracle's own functions: the frames avon dumps are rebuilt as
the oracle's tuples (S the string 'S', X the oracle's passenger), sharing
by node as its tuples share by identity, and FROZEN is decided by the
oracle's certified_frozen -- the fold lookup, unchanged.  So avon supplies
the run, and only the run.
"""

import subprocess

H, CONF, MAXLEVEL = 600, 150, 4


class Avon:
    """One avon batch process, a term at a time."""

    def __init__(self, avon, HD, H=H, conf=CONF):
        self.HD = HD
        self.p = subprocess.Popen(
            [avon, "batch", "--trace-frame=summary", f"--fuel={H}", f"--records={conf}",
             "--frame-dump=records,halt"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
        self.runs = 0

    def close(self):
        self.p.stdin.close()
        self.p.wait()

    def run(self, line):
        """The block for one term: (status, steps, kind, confirmed, frames)
        with frames {step: [items]} rebuilt as the oracle's objects."""
        HD = self.HD
        self.p.stdin.write(line + "\n")
        self.p.stdin.flush()
        self.runs += 1
        node = {}
        end = None
        conf = []
        frames = {}
        for raw in self.p.stdout:
            t = raw.split()
            if not t:
                continue
            c = t[0]
            if c == "$":
                break
            if c == "!":
                raise RuntimeError("avon gave no trace for " + line[:200])
            if c == ".":
                end = (t[1], int(t[2]), t[3])
            elif c == "C":
                conf = [int(x) for x in t[1:]]
            elif c == "d":
                i, rhs = t[1].split("=")
                if rhs == "S":
                    node[int(i)] = HD.S
                elif rhs == "X":
                    node[int(i)] = HD.X
                else:
                    l, r = rhs.split(".")
                    node[int(i)] = (node[int(l)], node[int(r)])
            elif c == "f":
                frames[int(t[1])] = [node[int(x)] for x in t[2:]]
        return end, conf, frames


def dag(u, HD):
    """A term of the oracle's objects as avon's DAG form, shared nodes once."""
    ids = {}
    parts = []
    stack = [(u, False)]
    while stack:
        x, done = stack.pop()
        k = id(x)
        if k in ids:
            continue
        if isinstance(x, tuple) and not done:
            stack.append((x, True))
            stack.append((x[1], False))
            stack.append((x[0], False))
            continue
        n = len(ids)
        if isinstance(x, tuple):
            parts.append(f"{n}={ids[id(x[0])]}.{ids[id(x[1])]}")
        else:
            parts.append(f"{n}={'X' if x is HD.X else 'S'}")
        ids[k] = n
    return "dag " + " ".join(parts) + f" @{ids[id(u)]}"


def run(av, HD, fr):
    """fixed_points_hider.run on the frame fr, the head run done by avon."""
    if len(fr) < 3:                          # no step: the census's first check
        if any(HD.xheaded(it) for it in fr):
            return "HALT-X", 0, []
        memo = {}
        return "HALT-B", 0, [(it, True) for it in fr if HD.contains_x(it, memo)]
    (status, steps, kind), conf, frames = av.run(dag(HD.ap(HD.S, *fr), HD))
    if kind == "HALT-X":
        return "HALT-X", steps, []
    if kind == "HALT-B":
        final = frames[steps]
        memo = {}
        return "HALT-B", steps, [(it, True) for it in final if HD.contains_x(it, memo)]
    if kind == "OPEN":
        return "OPEN", steps - 1, []
    assert kind == "FUEL", kind
    mints = []
    for n in conf:
        frn = frames[n]
        L = len(frn)
        pos = [L - i for i, it in enumerate(frn) if HD.xheaded(it)]
        deep = [p for p in pos if p <= L - 3]
        if deep:
            return ("FROZEN-c" if HD.certified_frozen(frn, min(deep)) else "FROZEN-u"), n, []
        if any(p == L - 1 for p in pos):
            return ("FROZEN-c" if HD.certified_frozen(frames[n + 1], L - 2) else "FROZEN-u"), n, []
        m = frames[n + 1][-(L - 2)]
        mints.append((m, HD.certified_frozen(frames[n + 1], L - 2)))
    return "RIDE", None, mints


def descend(av, HD, items, level, trail):
    """fixed_points_hider.descend, word for word, its runs through avon."""
    if level > MAXLEVEL:
        return None, trail + ["depth-bound"]
    for m, cert in items:
        if not cert:
            trail = trail + ["uncertified-mint"]
            continue
        v, info, sub = run(av, HD, HD.spine(m) if isinstance(m, tuple) else [m])
        if v in ("HALT-X", "OPEN", "FROZEN-c"):
            return v, trail + ["L%d:%s" % (level, v)]
        if v in ("HALT-B", "RIDE"):
            r, tr = descend(av, HD, sub, level + 1, trail + ["L%d:%s" % (level, v)])
            if r:
                return r, tr
            trail = tr
        else:
            trail = trail + ["L%d:%s" % (level, v)]
    return None, trail


def classify(av, HD, f):
    """fixed_points_hider.classify through avon: (key, exit, trail)."""
    HD.KEEP.clear()
    v, info, sub = run(av, HD, HD.spine(f) + [HD.X])
    if v in ("HALT-B", "RIDE"):
        r, tr = descend(av, HD, sub, 1, ["L0:%s" % v])
        return v + (">" + r if r else ">NONE"), r, tr
    return v, v, [v]


def census(avon, N):
    """The census of every closed f of size 1..N through avon: the
    verdict counts, with progress every 10**5 terms."""
    import time
    import oracle
    HD = oracle.load()
    t0 = time.time()
    av = Avon(avon, HD)
    counts = {}
    total = 0
    for n in range(1, N + 1):
        for f in HD.closed(n):
            if len(HD._CLS) > 3000000:
                HD.clear_memos()
            key, _r, _tr = classify(av, HD, f)
            counts[key] = counts.get(key, 0) + 1
            total += 1
            if total % 100000 == 0:
                print(f"  {total} terms: {dict(sorted(counts.items()))} [{time.time() - t0:.0f}s]", flush=True)
    av.close()
    print(f"census through avon, sizes 1..{N}: {dict(sorted(counts.items()))} "
          f"({total} terms, {av.runs} avon runs, {time.time() - t0:.0f}s)")


if __name__ == "__main__":
    import sys
    census(sys.argv[2] if len(sys.argv) > 2 else "build/avon", int(sys.argv[1]) if len(sys.argv) > 1 else 12)
