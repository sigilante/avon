"""Reduceron's Clausify.hs in strict Python, for the port's expected answer:
``python3 clausify_ref.py [N]`` prints the clause count, the clauses and
their display sum for N conjuncts (default 80): 1 [([0], [])] 0."""
import sys
sys.setrecursionlimit(100000)
def Sym(s): return ("Sym", s)
def Neg(p): return ("Neg", p)
def Con(p, q): return ("Con", p, q)
def Dis(p, q): return ("Dis", p, q)
def negin(p):
    if p[0] == "Neg":
        q = p[1]
        if q[0] == "Con": return Dis(negin(Neg(q[1])), negin(Neg(q[2])))
        if q[0] == "Dis": return Con(negin(Neg(q[1])), negin(Neg(q[2])))
        if q[0] == "Neg": return negin(q[1])
        return p
    if p[0] == "Dis": return Dis(negin(p[1]), negin(p[2]))
    if p[0] == "Con": return Con(negin(p[1]), negin(p[2]))
    return p
def disin(p):
    if p[0] == "Con": return Con(disin(p[1]), disin(p[2]))
    if p[0] == "Dis": return din(disin(p[1]), disin(p[2]))
    return p
def din(p, r):
    if p[0] == "Con": return Con(din(p[1], r), din(p[2], r))
    return din2(p, r)
def din2(p, q):
    if q[0] == "Con": return Con(din(p, q[1]), din(p, q[2]))
    return Dis(p, q)
def spl(a, p):
    # a is reversed: the Haskell list is a[::-1]
    if p[0] == "Con": return spl(spl(a, p[1]), p[2])
    a.append(p); return a
def ins(x, ys):
    if not ys: return [x]
    y = ys[0]
    if x == y: return ys
    if x <= y: return [x] + ys
    return [y] + ins(x, ys[1:])
def clause(ca, p):
    c, a = ca
    if p[0] == "Dis": return clause(clause(ca, p[1]), p[2])
    if p[0] == "Sym": return (ins(p[1], c), a)
    return (c, ins(p[1][1], a))
def union(xs, ys):
    return xs + [y for y in ys if y not in xs]
def uniq(xs):
    acc = []
    for x in reversed(xs):
        acc = union([x], acc)
    return acc
a = Sym(0)
def eqv(p, q): return Con(Dis(Neg(p), q), Dis(Neg(q), p))
p = eqv(eqv(a, eqv(a, a)), eqv(eqv(a, eqv(a, a)), eqv(a, eqv(a, a))))
f = a
for _ in range(int(sys.argv[1]) if len(sys.argv) > 1 else 80): f = Con(p, f)
cs = [clause(([], []), q) for q in spl([], disin(negin(f)))[::-1]]
cs = [(c, x) for (c, x) in cs if not set(c) & set(x)]
r = uniq(cs)
print(len(r), r, sum(sum(c) + sum(x) for c, x in r))
