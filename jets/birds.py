"""The bird dictionary (docs/DESIGN.md §6.8): Smullyan's birds as jets.

    PYTHONPATH=~/skijack/python python3 jets/birds.py [AVIARY_TESTS]

A compiler to SKI emits birds, so they recur across programs; a jet
matches one encoding only, so each bird is listed in every encoding a
compiler in use produces:

  aviary     aviary's bracket abstraction, with eta (SPEC.md §8); what
             SKIjack and SKIlark emit, since skijack.expand calls it
  aviary-sk  the same, strict S/K: I as S K K (aviary's expand_sk)
  curry      Curry's abstraction without eta: [x](E x) = S [x]E I
  rathman    Rathman's chart, fully expanded (aviary's test oracle)
  cl         combinatorylogic.com's composites, expanded through aviary

Every encoding is checked by reduction: applied to fresh atoms it reaches
the bird's rule (Y: its head reaches the argument).  S, K and I encoded
as themselves are left out: a leaf is no jet key.  Writes
jets/birds.tsv (a dictionary export: hash, atoms, term) and
jets/birds_names.tsv (encoding, bird, hash).  AVIARY_TESTS, default
~/urbit/aviary/tests, holds fixtures_birds.py; without it the rathman and
cl families are skipped.
"""

from __future__ import annotations

import importlib.util
import pathlib
import sys

from aviary_kernel.abstraction import expand, expand_sk
from aviary_kernel.birds import BIRDS, _r
from aviary_kernel.environment import Environment
from aviary_kernel.reduce import Status, reduce
from aviary_kernel.terms import App, Atom, pretty, size, substitute
from skijack.dictionary import structural_hash

HERE = pathlib.Path(__file__).resolve().parent
S, K, I = Atom("S"), Atom("K"), Atom("I")


def _free(term, x):
    if isinstance(term, Atom):
        return term.name == x
    return _free(term.fn, x) or _free(term.arg, x)


def curry(x, body):
    """Curry's abstraction, no eta: [x]x = I, [x]E = K E, [x](E F) = S."""
    if isinstance(body, Atom) and body.name == x:
        return I
    if not _free(body, x):
        return App(K, body)
    return App(App(S, curry(x, body.fn)), curry(x, body.arg))


def _pure(term):
    if isinstance(term, Atom):
        return term.name in ("S", "K", "I")
    return _pure(term.fn) and _pure(term.arg)


def verify(bird, term, env):
    """term applied to fresh atoms behaves as the bird's rule."""
    xs = [Atom(f"x{i}") for i in range(bird.arity)]
    run = term
    for x in xs:
        run = App(run, x)
    if bird.name == "Y":            # Y x = x (Y x): the head reaches x
        r = reduce(run, env, whnf_only=True, max_steps=10_000)
        head = r.term
        while isinstance(head, App):
            head = head.fn
        return r.status is Status.WHNF and head == xs[0]
    want = substitute(bird.rule, {f: x for f, x in zip(bird.formals, xs)})
    r = reduce(run, env, max_steps=100_000)
    return r.status is Status.NORMAL and r.term == want


def fixtures(tests_dir):
    path = pathlib.Path(tests_dir) / "fixtures_birds.py"
    if not path.exists():
        return {}, {}
    spec = importlib.util.spec_from_file_location("fixtures_birds", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.RATHMAN_SK, mod.CL_ORACLE


def encodings(env, rathman, cl):
    for bird in BIRDS:
        base = expand(Atom(bird.name), env)
        yield "aviary", bird, base
        yield "aviary-sk", bird, expand_sk(Atom(bird.name), env)
        if bird.name != "Y":        # Y's rule names Y: no abstraction
            body = bird.rule
            for f in reversed(bird.formals):
                body = curry(f, body)
            yield "curry", bird, body
        if bird.name in rathman:
            yield "rathman", bird, _r(rathman[bird.name])
        if bird.name in cl:
            yield "cl", bird, expand(_r(cl[bird.name]), env)


def main(argv):
    tests_dir = argv[0] if argv else pathlib.Path.home() / "urbit/aviary/tests"
    rathman, cl = fixtures(tests_dir)
    env = Environment()
    rows, names, bad = {}, [], []
    for kind, bird, term in encodings(env, rathman, cl):
        if not _pure(term) or not verify(bird, term, env):
            bad.append((kind, bird.name))
            continue
        if isinstance(term, Atom):      # S, K, I themselves: no jet key
            continue
        h = structural_hash(term)
        rows.setdefault(h, (size(term), pretty(term)))
        names.append((kind, bird.name, h))
    (HERE / "birds.tsv").write_text("".join(
        f"{h}\t{n}\t{t}\n" for h, (n, t) in sorted(rows.items())))
    (HERE / "birds_names.tsv").write_text("".join(
        f"{k}\t{b}\t{h}\n" for k, b, h in names))
    print(f"{len(BIRDS)} birds, {len(names)} encodings checked, "
          f"{len(rows)} distinct terms")
    for kind, name in bad:
        print(f"  rejected: {kind} {name}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
