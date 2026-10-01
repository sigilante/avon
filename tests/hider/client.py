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
import threading

H, CONF, MAXLEVEL = 600, 150, 4

#: the census options of avon batch
OPTS = ("--trace-frame=summary", f"--fuel={H}", f"--records={CONF}", "--frame-dump=census,halt")


def read_block(lines, HD, what=""):
    """One term's block from avon's output lines: (status, steps, kind), the
    confirmed records' facts [(n, L, lowest X-headed position or 0,
    X-headed at L-1)], and the frames the census reads, {step: [items]},
    rebuilt as the oracle's objects."""
    S, X = HD.S, HD.X
    node = {}
    end = None
    conf = []
    frames = {}
    for raw in lines:
        c = raw[0]
        if c == "d":                            # d <id>=S|X|<l>.<r>
            i, _, rhs = raw[2:-1].partition("=")
            if rhs == "S":
                node[int(i)] = S
            elif rhs == "X":
                node[int(i)] = X
            else:
                l, _, r = rhs.partition(".")
                node[int(i)] = (node[int(l)], node[int(r)])
        elif c == "$":
            break
        elif c == ".":
            t = raw.split()
            end = (t[1], int(t[2]), t[3])
        elif c == "K":
            t = raw.split()
            conf.append((int(t[1]), int(t[2]), 0 if t[3] == "-" else int(t[3]), t[4] == "1"))
        elif c == "f":
            t = raw.split()
            frames[int(t[1])] = [node[int(x)] for x in t[2:]]
        elif c == "!":
            raise RuntimeError("avon gave no trace for " + what[:200])
    return end, conf, frames


class Avon:
    """One avon batch process, a term at a time."""

    def __init__(self, avon, HD, H=H, conf=CONF):
        self.HD = HD
        self.p = subprocess.Popen(
            [avon, "batch", "--trace-frame=summary", f"--fuel={H}", f"--records={conf}",
             "--frame-dump=census,halt"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
        self.lines = iter(self.p.stdout)
        self.runs = 0

    def close(self):
        self.p.stdin.close()
        self.p.wait()

    def run(self, line):
        """The block for one term: (status, steps, kind), the confirmed
        records' facts [(n, L, lowest X-headed position or 0, X-headed at
        L-1)], and the frames the census reads, {step: [items]} rebuilt as
        the oracle's objects."""
        self.p.stdin.write(line + "\n")
        self.p.stdin.flush()
        self.runs += 1
        return read_block(self.lines, self.HD, line)


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
    return decide(HD, av.run(dag(HD.ap(HD.S, *fr), HD)))


def decide(HD, block):
    """The rest of fixed_points_hider.run, on the block of avon's run."""
    (status, steps, kind), conf, frames = block
    if kind == "HALT-X":
        return "HALT-X", steps, []
    if kind == "HALT-B":
        final = frames[steps]
        memo = {}
        return "HALT-B", steps, [(it, True) for it in final if HD.contains_x(it, memo)]
    if kind == "OPEN":
        return "OPEN", steps - 1, []
    assert kind == "FUEL", kind
    # the census's loop over the confirmed records, its decisions on the
    # positions avon reports: the deep items are those at or below L-3, so
    # the lowest X-headed position is min(deep) when there are any
    mints = []
    for n, L, low, ym1 in conf:
        if low and low <= L - 3:
            return ("FROZEN-c" if HD.certified_frozen(frames[n], low) else "FROZEN-u"), n, []
        if ym1:
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
    return finish(av, HD, v, sub)


def finish(av, HD, v, sub):
    """classify's last step: the descent, from the level-0 run's outcome."""
    if v in ("HALT-B", "RIDE"):
        r, tr = descend(av, HD, sub, 1, ["L0:%s" % v])
        return v + (">" + r if r else ">NONE"), r, tr
    return v, v, [v]


def verdicts(avon, HD, N, NMIN=1):
    """(key, exit, trail) for every closed f of size NMIN..N, in the
    census's order, through avon.

    The level-0 runs depend on nothing, so they stream: avon enum's terms,
    each with X, go into one avon batch from a thread while this one reads
    the blocks in order and decides; the descents, each depending on a
    verdict, go one at a time through a second avon.  A term that is S or
    S a, whose frame f X is shorter than three, is run by avon too and
    halts at once with its X-headed item, as the census's first check has
    it."""
    lev0 = subprocess.Popen([avon, "batch", *OPTS], stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE, text=True, bufsize=1 << 20)

    def feed():
        for n in range(NMIN, N + 1):
            e = subprocess.Popen([avon, "enum", str(n)], stdout=subprocess.PIPE,
                                 stderr=subprocess.DEVNULL, text=True, bufsize=1 << 20)
            for line in e.stdout:
                lev0.stdin.write(line[:-1] + " X\n")
            e.wait()
        lev0.stdin.close()
    threading.Thread(target=feed, daemon=True).start()
    av = Avon(avon, HD)                         # the descents
    lines = iter(lev0.stdout)
    for raw in lines:
        if raw[0] != ">":
            continue
        if len(HD._CLS) > 3000000:
            HD.clear_memos()
        HD.KEEP.clear()
        v, _info, sub = decide(HD, read_block(lines, HD))
        yield finish(av, HD, v, sub)
    lev0.wait()
    av.close()
    verdicts.descents = av.runs


def census(avon, N, NMIN=1):
    """The census of every closed f of size NMIN..N through avon: the
    verdict counts, with progress every 10**5 terms."""
    import time
    import oracle
    HD = oracle.load()
    t0 = time.time()
    counts = {}
    total = 0
    for key, _r, _tr in verdicts(avon, HD, N, NMIN):
        counts[key] = counts.get(key, 0) + 1
        total += 1
        if total % 100000 == 0:
            print(f"  {total} terms: {dict(sorted(counts.items()))} [{time.time() - t0:.0f}s]", flush=True)
    print(f"census through avon, sizes {NMIN}..{N}: {dict(sorted(counts.items()))} "
          f"({total} terms, {total + verdicts.descents} avon runs, {time.time() - t0:.0f}s)")
    return counts


if __name__ == "__main__":
    # client.py N [AVON] [NMIN]: the census of sizes NMIN..N (NMIN 1)
    import sys
    census(sys.argv[2] if len(sys.argv) > 2 else "build/avon",
           int(sys.argv[1]) if len(sys.argv) > 1 else 12,
           int(sys.argv[3]) if len(sys.argv) > 3 else 1)
