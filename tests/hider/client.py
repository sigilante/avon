"""The hider census driven by avon's frame traces.

The census's run/descend/classify (fixed_points_hider.py), with each head
run done by avon --trace-frame instead of in Python.  Every decision the
census makes is made here the way it makes it, on the oracle's own objects
and with the oracle's own functions: the frames avon dumps are rebuilt as
the oracle's tuples (S the string 'S', X the oracle's passenger), sharing
by node as its tuples share by identity, and FROZEN is decided by the
oracle's certified_frozen---the fold lookup, unchanged.  Avon supplies the
run: its exit, its confirmed records, and the positions at each.  Every
position a decision rests on is checked against the dumped frames before
the certificate is asked (decide); the exits and record times are Avon's
reduction, equal to the census's on sizes 1 to 12.
"""

import subprocess
import threading

H, CONF, MAXLEVEL = 600, 150, 4

#: the census options of avon batch
OPTS = ("--trace-frame=summary", f"--fuel={H}", f"--records={CONF}", "--frame-dump=census,halt")
#: the defect count's options
DEFECT_OPTS = ("--trace-frame=summary", f"--fuel={H}", f"--defect={CONF}")


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
    else:
        raise RuntimeError("avon ended inside a block" + (" for " + what[:200] if what else ""))
    if end is None:
        raise RuntimeError("avon's block has no end line" + (" for " + what[:200] if what else ""))
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
        try:
            self.p.stdin.write(line + "\n")
            self.p.stdin.flush()
        except OSError as ex:
            raise RuntimeError(f"avon batch died before {line[:200]}: {ex!r}") from ex
        self.runs += 1
        for raw in self.lines:              # to the block's start
            if raw[0] == ">":
                return read_block(self.lines, self.HD, line)
        raise RuntimeError("avon batch ended before " + line[:200])


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
    # the lowest X-headed position is min(deep) when there are any.  Each
    # position a decision rests on is checked on the dumped frames first:
    # frame n+1 keeps frame n's positions 1..L-3, and since every later
    # length exceeds a record's, no later step touches them, so `clean`
    # (positions 1..clean hold no X-headed item) only grows.
    mints = []
    clean = 0
    for n, L, low, ym1 in conf:
        if low and low <= L - 3:
            fr = frames[n]
            if (len(fr) != L or not HD.xheaded(fr[-low])
                    or any(HD.xheaded(fr[-p]) for p in range(clean + 1, low))):
                raise RuntimeError(f"avon's lowest X-headed position {low} at step {n} "
                                   "disagrees with its frame")
            return ("FROZEN-c" if HD.certified_frozen(fr, low) else "FROZEN-u"), n, []
        nxt = frames[n + 1]
        if (len(nxt) < L - 2 or any(HD.xheaded(nxt[-p]) for p in range(clean + 1, L - 2))
                or HD.xheaded(nxt[-(L - 2)]) != ym1):
            raise RuntimeError(f"avon's record facts at step {n} disagree with its frame")
        clean = max(clean, L - 3)
        if ym1:     # y X-headed at L-1 in frame n: y.z, at L-2 in frame n+1, is
            return ("FROZEN-c" if HD.certified_frozen(nxt, L - 2) else "FROZEN-u"), n, []
        m = nxt[-(L - 2)]
        mints.append((m, HD.certified_frozen(nxt, L - 2)))
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


def level0(avon, opts, N, NMIN, failed):
    """One avon batch with opts, fed f X for every closed f of size
    NMIN..N, in the census's order, by avon enum from a thread: (the
    process, the thread).  What goes wrong in the feeding is appended to
    failed."""
    lev0 = subprocess.Popen([avon, "batch", *opts], stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE, text=True, bufsize=1 << 20)

    def feed():
        try:
            for n in range(NMIN, N + 1):
                e = subprocess.Popen([avon, "enum", str(n)], stdout=subprocess.PIPE,
                                     text=True, bufsize=1 << 20)
                for line in e.stdout:
                    lev0.stdin.write(line[:-1] + " X\n")
                if e.wait() != 0:
                    failed.append(f"avon enum {n} exited {e.returncode}")
                    break
        except Exception as ex:                 # a dead batch: a broken pipe
            failed.append(f"feeding avon batch: {ex!r}")
        finally:
            try:
                lev0.stdin.close()
            except OSError:
                pass
    feeder = threading.Thread(target=feed, daemon=True)
    feeder.start()
    return lev0, feeder


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
    failed = []                                 # what went wrong in the feeder
    lev0, feeder = level0(avon, OPTS, N, NMIN, failed)
    av = Avon(avon, HD)                         # the descents
    lines = iter(lev0.stdout)
    count = 0
    for raw in lines:
        if raw[0] != ">":
            continue
        if len(HD._CLS) > 3000000:
            HD.clear_memos()
        HD.KEEP.clear()
        v, _info, sub = decide(HD, read_block(lines, HD))
        count += 1
        yield finish(av, HD, v, sub)
    feeder.join()
    if lev0.wait() != 0:
        failed.append(f"avon batch exited {lev0.returncode}")
    av.close()
    if av.p.returncode != 0:
        failed.append(f"avon batch (descents) exited {av.p.returncode}")
    want = sum(catalan(n - 1) for n in range(NMIN, N + 1))
    if count != want:
        failed.append(f"{count} terms classified, {want} expected")
    if failed:
        raise RuntimeError("the census through avon is incomplete: " + "; ".join(failed))
    verdicts.descents = av.runs


def catalan(n):
    """The number of closed S-terms of size n+1."""
    c = 1
    for k in range(n):
        c = c * 2 * (2 * k + 1) // (k + 2)
    return c


#: the fields of avon's D line, as fixed_points_fold.py's mode defect names them
DEFECT_FIELDS = ("steps", "D decreases", "y-steps", "D = 0 after a y-step",
                 "confirmed records after the first y-step", "with D >= 1")


def defects(avon, N, NMIN=1):
    """The defect count of every closed f of size NMIN..N, in the census's
    order: the six fields of avon's D line for f X's level-0 run, followed
    while one X-headed item persists and is not at the x-seat."""
    failed = []
    lev0, feeder = level0(avon, DEFECT_OPTS, N, NMIN, failed)
    count = 0
    got = None
    for raw in lev0.stdout:
        c = raw[0]
        if c == ">":
            got = None
        elif c == "D":
            got = tuple(int(x) for x in raw.split()[1:])
        elif c == "!":
            failed.append(f"avon gave no trace for term {count + 1}")
            break
        elif c == "$":
            if got is None or len(got) != len(DEFECT_FIELDS):
                failed.append(f"no D line for term {count + 1}")
                break
            count += 1
            yield got
    if failed:
        lev0.kill()                             # unread output would block the feeder
    feeder.join()
    if lev0.wait() != 0 and not failed:
        failed.append(f"avon batch exited {lev0.returncode}")
    want = sum(catalan(n - 1) for n in range(NMIN, N + 1))
    if not failed and count != want:
        failed.append(f"{count} terms counted, {want} expected")
    if failed:
        raise RuntimeError("the defect count through avon is incomplete: " + "; ".join(failed))


def defect(avon, N, NMIN=1):
    """The paper's defect check (fixed_points_fold.py, mode defect) through
    avon, sizes NMIN..N: the totals, in its words, with progress every
    10**5 terms."""
    import time
    t0 = time.time()
    tot = [0] * len(DEFECT_FIELDS)
    runs = 0
    for got in defects(avon, N, NMIN):
        runs += 1
        tot = [a + b for a, b in zip(tot, got)]
        if runs % 100000 == 0:
            print(f"  {runs} terms, {tot[0]} steps, D decreases {tot[1]} [{time.time() - t0:.0f}s]",
                  flush=True)
    steps, dec, ys, zero, recs, recs_d = tot
    print(f"defect through avon, sizes {NMIN}..{N}: {runs} runs, {steps} steps; D decreases: {dec}; "
          f"y-steps: {ys}; D = 0 after a y-step: {zero}; confirmed records after the first "
          f"y-step: {recs}, with D >= 1: {recs_d} ({time.time() - t0:.0f}s)")
    return runs, tot


def census(avon, N, NMIN=1):
    """The census of every closed f of size NMIN..N through avon: the
    verdict counts, with progress every 10**5 terms."""
    import time
    import oracle
    HD = oracle.load()
    if HD is None:
        raise SystemExit(f"no hider census at {oracle.SCRIPTS} (set HIDER_SCRIPTS)")
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
    # client.py defect N [AVON] [NMIN]: the defect check of sizes NMIN..N
    import sys
    argv = sys.argv[1:]
    run_ = census
    if argv and argv[0] == "defect":
        run_ = defect
        argv = argv[1:]
    run_(argv[1] if len(argv) > 1 else "build/avon",
         int(argv[0]) if argv else 12,
         int(argv[2]) if len(argv) > 2 else 1)
