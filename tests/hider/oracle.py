"""The paper's hider census, imported as the oracle (docs/DESIGN.md §22).

HIDER_SCRIPTS names the directory of fixed_points_hider.py (default: the
paper's scripts/).  Nothing here re-derives a verdict: the census's own
functions are used as they are.
"""

import os
import sys

SCRIPTS = os.environ.get("HIDER_SCRIPTS", os.path.expanduser(
    "~/Documents/Davis2026 Universality of the Pure S Calculus/scripts"))


def load():
    """The oracle module, or None when the paper's scripts are absent."""
    if not os.path.exists(os.path.join(SCRIPTS, "fixed_points_hider.py")):
        return None
    root = os.path.dirname(SCRIPTS)
    for p in (root, SCRIPTS):
        if p not in sys.path:
            sys.path.insert(0, p)
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 100000))
    argv = sys.argv
    sys.argv = [argv[0]]
    try:
        import fixed_points_hider as HD
    finally:
        sys.argv = argv
    return HD


def text(t, X):
    """A tuple term printed for avon: S, the passenger X, application left
    to right, an argument that is an application parenthesized."""
    out = []
    stack = [(t, False)]
    while stack:
        u, paren = stack.pop()
        if isinstance(u, str):
            if u == ")":
                out.append(")")
                continue
            out.append(u)
            continue
        if u is X:
            out.append("X")
            continue
        f, x = u
        if paren:
            out.append("(")
            stack.append((")", False))
        stack.append((x, isinstance(x, tuple)))
        stack.append((" ", False))
        stack.append((f, False))
    return "".join(out)


def hist(HD, frame, H):
    """The oracle's run loop (fixed_points_hider.run), to its first exit:
    (L, th) before each step, then the exit and its step."""
    fr = list(frame)
    out = []
    for st in range(H):
        if len(fr) < 3:
            return out, ("HALT-X" if any(HD.xheaded(it) for it in fr) else "HALT-B"), st
        if HD.xheaded(fr[0]):
            return out, "OPEN", st
        L = len(fr)
        th = tuple(i for i, it in enumerate(fr) if HD.xheaded(it))
        out.append((L, th))
        x, y, z = fr[0], fr[1], fr[2]
        fr = HD.spine(x) + [z, (y, z)] + fr[3:]
    return out, "FUEL", H


def args_of(u, X):
    """spine(u): the arguments of u's head, S or X."""
    a = []
    while isinstance(u, tuple):
        a.append(u[1])
        u = u[0]
    a.reverse()
    return a


def observe(HD, fr):
    """The trace line's fields from a frame, by the definitions
    (docs/RUNTIME.md): L, positions front first, d, D, event, front arity."""
    L = len(fr)
    th = [i for i, it in enumerate(fr) if HD.xheaded(it)]
    pos = [L - i for i in th]
    d = D = None
    if len(th) == 1:
        p = th[0]
        d = L - p - 1

        def sigma(u):
            return sum(1 for v in args_of(u, HD.X) if HD.xheaded(v))
        D = sum(1 for u in fr[:p] if sigma(u) >= 1) + sum(1 for u in fr[p + 1:] if sigma(u) >= 2)
    ev = "-"
    if pos:
        q = pos[0]
        ev = "o" if q == L else "y" if q == L - 1 else "z" if q == L - 2 else "-"
    return L, tuple(pos), d, D, ev, len(args_of(fr[0], HD.X))


def lines(HD, frame, H):
    """Every trace line the definitions give, the OPEN line included, and
    the exit: what avon --trace-frame must print."""
    fr = list(frame)
    out = []
    for st in range(H):
        if len(fr) < 3:
            return out, ("HALT-X" if any(HD.xheaded(it) for it in fr) else "HALT-B"), st
        out.append(observe(HD, fr))
        if HD.xheaded(fr[0]):
            return out, "OPEN", st
        x, y, z = fr[0], fr[1], fr[2]
        fr = HD.spine(x) + [z, (y, z)] + fr[3:]
    return out, "FUEL", H
