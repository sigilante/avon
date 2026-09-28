# Avon: the native runtime, planned

> **Status (2026-09-27).** Design note written 2026-09-16. The compiler it targets is now implemented as `python/skijack`; the runtime it plans is not built, and `avon/bench/` reproduces the measurements it rests on. Where this note and the compiler differ, the compiler and its tests are authoritative. §17 and §18 (added 2026-09-27) fit Avon to the proof system in `lean-ski`: a third strategy whose runs the circuit proves, and the licence a jet needs inside a proof. §20 (added 2026-09-27) takes Vere's relation to Nock as the model: Avon's C never compiles, but Avon runs a compiler, and §0's job list grows by two items. §6.5, §7 and §8 (revised 2026-09-27) follow Vere's `+mock` jet: the interpreter jet is the level-1 interpreter and serves scry, and residual jets keep fuel exact inside it. §21 compares Vere and NockApp from their sources. §9 and §20.1 (revised 2026-09-27) fix the kernel as a door `[battery state]` pulled by axis, and the pill as one term. This note now lives in the Avon repository as `docs/DESIGN.md`; `skijack/avon/DESIGN.md` links to it, and paths below stay relative to the skijack repository.

*2026-09-16. The build plan for the C runtime named in `RUNTIME-DESIGN.md`
§3a. Its constraints come from three places: the reference host
(`aviary_kernel.reduce`, which is where the paper's counts come from), the
compiler (`python/skijack`, which is what produces the terms), and the
paper's measured targets. §1 reports a measurement that changes one of
`RUNTIME-DESIGN.md`'s stated acceptance criteria, and most of what follows
is downstream of it. Nothing here is built; `avon/` is empty.*

## 0. What Avon is, and what it is not

**Avon's C does not compile; Avon runs a compiler.** Its C has no lexer, no
parser, no expander, no Stage A checker, and no dictionary builder. Vere
holds no Hoon compiler either: the compiler is a Nock term inside Arvo, and
Vere runs it. Avon stands to SKI as Vere stands to Nock, so the SKIjack
compiler becomes a term Avon runs, and Python `skijack` becomes the
bootstrap cross-compiler that builds the first pill. Python stays the
oracle. The nockasm discipline still holds, with one move: the line between
expansion and execution is the compiled term, and the expander now sits on
the term's side of it (§20).

Avon's whole job list:

1. reduce closed `{S,K,I}` terms fast, with fuel and a size cap;
2. read a value out of a reduced term the way the paper does, by probing
   with fresh marker atoms;
3. serialize terms and reduced states;
4. recognize known terms and run native code for them (jets), including the
   interpreter;
5. serve a scry namespace and the blocking resume loop;
6. boot a kernel from a pill: apply a term to an initial subject, then
   pull `poke`, `peek` and `load` from the door it reduces to (§9, §20.1);
7. emit the witness a zero-knowledge proof of a run needs (§17);
8. install compiled code: decode a term the running compiler produced as
   data into live nodes, and match jets on it (§20.2).

Items 1 to 3 are a runtime. Items 4 to 8 make it *this* runtime.

**Avon is SKIM-class technology rebuilt in C, and should say so first.**
A machine that reduces combinator graphs with sharing, an explicit spine
stack and a fixed set of recognized combinators executed natively is
Turner 1979 and SKIM 1980, the latter in microcode (§14).
Nothing in stages 1 to 3 below is a new idea and none of it should be
presented as one. What is not inherited is narrow and worth stating
exactly: the **interpreter jet** of §7, which accelerates a term that is
itself a reducer and is licensed by a theorem rather than by a benchmark;
the **two-strategy conformance contract** of §1, which exists because the
artifact being reproduced is a published set of counts; and the **scry
loop** of §8, which has no antecedent in that literature at all. A
systems paper that claimed the reducer as novel would be correctly
dismissed, and this note is written so that one cannot.

The input alphabet is `S`, `K`, `I`, application, and **opaque atoms** —
anything else, inert, never contracted. Opaque atoms exist because the
paper's verification discipline reads values by applying terms to fresh
markers, and Avon must be able to do that too.

## 1. The measurement that fixes the acceptance test

`RUNTIME-DESIGN.md` §4 asks for two things that cannot both hold: a graph
reducer with sharing, and "output must reproduce every count in the paper
exactly: T0 340, T1 91,556, T2 504,930."

They conflict because `aviary_kernel.reduce` is not a graph reducer. It is a
*substitution* reducer: `_try_contract` substitutes the arguments into the
combinator's body and builds fresh application nodes, and nothing is ever
mutated. Subterms are shared in *representation* (the same Python object
appears twice after `S x y z → x z (y z)`), which is what keeps the tower's
memory finite, but no reduction *work* is shared: when the first copy of a
duplicated redex is contracted, the second copy is untouched and gets
contracted again. The paper's counts are therefore term-rewriting counts.

A reducer that overwrites the redex root in place — Turner's machine, the
one §3a asks for — contracts a duplicated redex once. Both strategies,
transcribed onto a common node representation (`avon/bench/strategies.py`)
and run on the paper's three targets:

| target | paper / substitution | copy (no update) | share (update in place) | share + hash-consing |
|---|---|---|---|---|
| T0 `whnfF 3 <I K>` | 340 | **340** | 323 | 293 |
| T1 `whnfF 120 <UQ <I K>>` | 91,556 | **91,556** | 63,326 | 53,244 |
| T2 `whnfF 500 <whnfF 3 <I K>>` | 504,930 | **504,930** | 313,860 | 262,801 |

Three things this establishes.

- **Sharing changes the counts and not the values.** A differential run of
  the sharing reducer against `aviary` on 2,986 random `{S,K,I}` terms
  reduced to full normal form gave 0 mismatches, and the sharing reducer
  never took more steps than `aviary` on any of them. Values are safe;
  counts are not.
- **A copying reducer reproduces the paper exactly.** The copy column is
  not fitted to those numbers: it is the reference's own strategy on a
  different representation —
  keep the current position as a flat `(head, args)` pair with no parent
  pointers, contract by building the body fresh, never mutate — and it
  lands on 340, 91,556, 504,930 with no tuning.
- **Sharing-mode counts are not a function of the term.** They depend on how
  much sharing the input carried: hash-consing the *loaded* term alone moves
  T2 from 313,860 to 308,871. A count that depends on the representation
  cannot be a conformance target.

### 1.1 The contract, restated

Avon ships **two strategies in one binary**, selected per run:

- `--strategy=copy` (the *faithful* strategy): no update in place, no
  hash-consing, jets off. Reproduces the reference host's contraction counts
  exactly. This is what the conformance harness runs, and it is how Avon
  earns the right to be called an implementation of the paper's artifact.
- `--strategy=share` (the default for work): update in place. Same values,
  fewer contractions, and its counts are reported as *its own*, in a
  published table beside the reference counts, never in place of them.

A third strategy, `--strategy=witness`, exists for proofs: the circuit's
machine executed literally, with the `copy` counts and a trace the prover
consumes. §17 gives it; neither strategy above can stand in for it.

What is conformance, precisely:

| claim | conformance target? |
|---|---|
| decoded value of every corpus target | yes, always, in both strategies |
| full normal form, when one is reached | yes, in both strategies |
| the weak head normal form reached | yes in `copy`; never in `share`, where update in place also reduces shared redexes inside the arguments, so the term differs while its normal form and decoded value do not |
| object-level step counts (the fuel a term consumes) | yes — they are computed by the term, so every correct reducer agrees |
| host contraction counts | yes in `copy`, never in `share` |
| `SIZE` outcomes | no: the reference samples its size guard every 512 steps and measures a different quantity (see §3.3) |
| wall-clock, node counts | reported, never asserted |

This is the same honesty §5 of `RUNTIME-DESIGN.md` already asks for about
jets, applied one level down: the speed comes from somewhere, and the note
says where.

## 2. Representation

**Node.** Eight bytes, two 32-bit words, tag in the top two bits of the
first:

```c
typedef struct { uint32_t l, r; } av_node;     /* tag = l >> 30 */

#define AV_APP  0u   /* l = left index,   r = right index            */
#define AV_IND  1u   /* l = target index, r = unused   (share mode)  */
#define AV_LEAF 2u   /* l = tag only,     r = atom id (0=S, 1=K, 2=I) */
#define AV_JET  3u   /* l = jet id,       r = fallback term index    */
```

Indices, not pointers: the arena can be `realloc`'d without a fixup pass,
a snapshot is a `write(2)`, and a node is half the size it would be at 64
bits. The ceiling is 2³⁰ nodes ≈ 8.6 GB of heap, which is far past anything
these programs need.

Atom ids 0, 1, 2 are `S`, `K`, `I`, and their three leaf nodes are interned
at node indices 0, 1, 2, so both the leaf test and the arity lookup are
integer compares. Atom ids ≥ 3 are opaque atoms, with names in a side table
that the wire format carries (§4.2).

**Arena.** One flat array, bump-allocated. Measured working sets, for
sizing: T2 builds 647,236 nodes in copy mode and 320,899 in share mode —
about 5 MB and 2.5 MB. The compiled interpreter is 618 atoms, hence 1,235
nodes as a tree and 348 as a DAG; the unquoter is 43 atoms, 85 nodes as a
tree, 62 as a DAG. Nothing here is large. A 64 MB default arena with
doubling growth is generous.

**Reclamation.** Bump allocate; collect by stop-and-copy (Cheney) from the
roots — the spine stack, the current root, the subject, the fact store, the
jet dashboard's registered terms. Reasons to prefer it over the reference
counting `RUNTIME-DESIGN.md` §3a proposes first: it costs no per-node count
field (the node stays at 8 bytes), it is O(live) rather than O(garbage),
and it compacts, which matters for a structure this pointer-chasing. The
note is right that the graph is acyclic — `S f g x → f x (g x)` builds its
new children out of nodes strictly below the redex root, so update in place
cannot create a cycle — so refcounting *would* be sound; it is a fallback,
not the plan. (Hash-consing during reduction breaks that acyclicity
argument: see §2.1.)

**Sharing on load.** The loader preserves the DAG when the input format
carries it (§4.2). It changes no `copy`-mode count and lowers `share`-mode
counts, which is the point.

### 2.1 Hash-consing: measured, and off by default

`RUNTIME-DESIGN.md` §3a wants a `(left,right) → index` table so that equal
applications are one node, "which is also what makes jet lookup O(1)". Both
halves of that need revising.

Consing every node built during reduction buys 16% of T2's contractions
(313,860 → 262,801) and 18% of its nodes, at the cost of one hash probe per
allocation — 306,384 probes for T2. In C a probe is comparable in cost to
the contraction it is trying to avoid, so this is close to a wash and has to
be measured on the target, not assumed. Two further costs: the table is a
GC root set that must be rebuilt on every collection, and a cons that
returns a node which happens to be an *ancestor* of the redex makes the
graph cyclic, after which the term can no longer be printed or serialized as
a tree. No corpus run produced such a cycle — the bench script walks the
reachable graph after every run and reports back edges, and there are none
— but nothing rules one out, and a runtime that can silently produce
an unprintable state is worse than one that is 16% slower.

Decision: `--hash-cons` is a flag, default off, benchmarked in stage 1,
and never on in `copy` mode. Jet lookup does not need it (§6).

## 3. The reducer

### 3.1 Two loops, one file

Both are iterative with an explicit stack; neither recurses, so spine depth
costs heap and not C stack. Measured peak spine depth on T0–T2 is 16, which
says the initial stack can be small (64 K entries) and grow by doubling.

`share`: walk down `l` pointers pushing application nodes; at a leaf with
arity `k` and at least `k` frames, overwrite the redex root — `I x` and
`K x y` become `AV_IND` to `x`; `S f g x` becomes an `AV_APP` of two fresh
nodes — pop `k` frames, continue from the root. Indirections are followed
on every load and short-circuited when walked. **The short-circuit is
required, not an optimization.** Without it, `S f g x` reads an `x` that a
previous contraction turned into an indirection, the new node points
through it, and chains grow by one link per contraction: stage 1 measured
`S I I (S I I)` going quadratic, 1 s for 10⁵ steps. Resolving each argument
as a contraction reads it, and rewriting a spine node's left pointer past an
indirection as the walk passes, restores 10⁸ steps in 0.4 s.

`copy`: hold the position as a head plus a flat argument vector, contract by
constructing the combinator body and re-decomposing it (`nargs + rest`,
exactly as `_try_contract` does), and never touch a parent. Descending into
an argument for full normal form pushes a frame that rebuilds on the way
out.

Full normal form is the outer loop in both: reduce the head to WHNF, then
each argument left to right, then rebuild. `whnf_only` stops at the top
position only, which is what the paper's targets use.

### 3.2 Fuel

One counter, checked **before** each contraction, matching the reference.
`FUEL` is a status, not an error. Note the distinction Avon must keep
visible in its output: *host fuel* is a property of the run, *object fuel*
is the numeral inside a level-1 term and is consumed by the term itself, so
only the first is Avon's.

A proved run has two further budgets, rows and memory cells, which count
different things from host fuel and are fixed by the caller in public
(§17.2).

### 3.3 The size cap

The reference computes a DAG node count of the whole term every 512
contractions. Avon measures live nodes after a collection: when an
allocation finds the arena full, it collects, and reports `SIZE` if the
survivors exceed `max_nodes`. That is close to the reference's quantity
but sampled at different moments, so the size cap is a resource guard,
never a conformance target, and conformance runs set it out of reach (the
harness uses 10⁹ today). The collector grows the arena whenever the live
set passes half of it, so memory stays within about twice the live set.

### 3.4 Status

`WHNF`, `NORMAL`, `FUEL`, `SIZE`, `INTERRUPTED`. Same five the reference has,
same names, so the harness can compare them as strings.

## 4. Term I/O

### 4.1 Printed form

`aviary_kernel.terms.pretty`: left-associative juxtaposition, parentheses
only around a right-nested application. Avon must produce this byte for
byte for any term small enough to print, and parse it back. This is
`RUNTIME-DESIGN.md` §4 item 2, and it is what lets terms move between the
two runtimes without a third format.

The hazard is that printing is a *tree* walk and reduced states are DAGs
whose unfoldings are exponential — the whole reason the paper's harness
counts DAG nodes. So the printer takes a node budget and refuses past it,
loudly. Printing a reduced tower state is not a thing Avon offers; §4.2 is.

### 4.2 Bitstrings, and a sharing format

Tromp's encoding, as §3d fixes it: `S̃ = 00`, `K̃ = 01`, application
`1 M̃ Ñ`, plus a third leaf code for `I`. Two open ends in that note, which
this plan closes as decisions to take rather than leaving implicit:

- the third code for `I` versus expanding `I` to `S K K` is a **version
  decision**. **Taken in stage 2 (container version 1):** the third code,
  `10`, with applications moving to `11`, since expanding `I` changes atom
  counts and the paper's counts are about atoms.
- opaque atoms have no encoding at all in Tromp's scheme. Since the
  conformance harness needs to ship probe markers, the term file format is
  a small container: a header with the atom-name table, then the bitstring
  with atom ids in an extended leaf code. **Taken in stage 2:** `10` is
  followed by `w` bits, `w` the bit length of the atom count, where 0 is
  `I` and `k` is the `k`-th atom. With no atoms `w` is 0, so a pure term
  pays nothing and its code is exactly `00 / 01 / 10 / 11`. The table lists
  atoms in the order a pre-order walk first meets them, and `cue` refuses
  any other order, an unused or duplicate entry, nonzero padding, and bits
  past the term, so `cue(x) = t` implies `jam(t) = x`. The layout is in
  `include/avon.h`.

The bitstring does not preserve sharing. For snapshots of reduced states
Avon writes its own image — the arena and the root — which is a `write(2)`
of a flat array, and uses the bitstring only for interchange. **Built in
stage 2** (`src/snap.c`), with §19's rules: save copies one term's graph
out of the live arena (as of stage 4; stage 2 collected the arena in
place, which also wrote the jet dashboard into the image), so the image
holds that graph and nothing else; it writes the image, syncs it, and only
then writes a sidecar holding the root, the node count and a SHA-256 over
image and root. Load checks that checksum before reading anything, then every
node — tags, indices, one interned leaf per atom, S, K, I at 0, 1, 2 — and
that the graph is acyclic, since a cycle would hang the reducer. An image
carrying a valid checksum and a bad structure is still refused. A snapshot is
not a proof witness: it carries indirections, jet nodes and the
collector's moves, and the circuit's memory table has none of them
(§17.1).

### 4.3 Atom hygiene, and a trap worth naming

The Python oracle reduces in an `Environment` where **53 bird names are live
combinators** — `B`, `C`, `W`, `Y`, `T`, `M`, `U` and the rest all have
arities and rules. Avon has three. A term containing an atom named `W` is
inert in Avon and contracts in Python. Today nothing collides — the markers
are `X1…Xn`, `Z`, `S_`, and the harness's `\x00`-prefixed names, none of
which is a bird — but nothing prevents it either.

So: the exporter asserts that no atom in an exported term or marker set is a
bird name, and Avon's loader rejects any atom whose name is in the bird
table unless `--allow-bird-atoms` is passed. A conformance divergence should
never be able to come from this.

## 5. Structural hash

`python/skijack/dictionary.py` already fixes it: a Merkle hash, leaf hashes
its name, application hashes `"(" + h(fn) + " " + h(arg) + ")"`, `sha256`
truncated to 16 hex digits, published with the version prefix
`skijack-1:`. Avon computes the same values, in one bottom-up pass, with a
vendored public-domain `sha256.c` (~200 lines, no dependency).

It is computed **at load time only** — once per dictionary entry and once
per candidate node in the loaded program — and never on the reduction hot
path. §6 is why that suffices.

**Built in stage 4** (`src/jets.c`): it matches skijack's string on all
282 rows of the corpus dictionary (`tests/test_jets.c`).

The hash is for **dispatch, not commitment**. Sixty-four bits admit a
collision after about 2³² work, which is harmless when a wrong match only
wastes a jet check and fatal when a verifier trusts it. Nothing a proof
relies on is keyed by it: a proof binds terms by the circuit's own field
fingerprints (`lean-ski`'s `zk/`, with a proved collision bound), and a jet
inside a proof is licensed by recomputing the term it stands for (§18.1),
not by its hash.

## 6. Jets

### 6.1 What the key is

**The subterm, and nothing else.** The key is the Merkle hash of §5 over
that node's tree — leaf names and application structure — published with
the `skijack-1:` prefix. Not the name it was compiled from, not the type
declaration it came out of, not the subject it will be applied to, not its
arity.

The subject cannot be in the key and does not need to be, and the reason is
the same fact that makes bracket abstraction the whole compiler: **after
abstraction there are no variables left.** Every subterm of a compiled
program is a closed `{S,K,I}` term, so its behaviour is a function of
itself alone; there is no environment for it to mean something different
in. A subject reaches a supercombinator as an *argument*: the use site
is the application node `(sc subject)`, and the supercombinator is that
node's left child,
hashed on its own. (The corpus programs have no subject argument at all yet
— the standard subject is unbuilt — so this is a statement about what will
not change when it exists.)

This is where Avon and Vere differ, and it is worth being precise about
why. A Nock formula's meaning depends on the subject it runs against, so
Vere cannot key on code alone: it matches a *core* — a battery plus a claim
about the payload — and registers it under a parent in the dashboard.
Nothing here needs that. Putting the subject in the key would also be
actively wrong: the subject grows every time the program gains an unrelated
equation, and every jet would miss the moment it did. The battery is hashed and
the payload is not, for the same reason, one level down.

### 6.2 What a loader actually finds

Measured, on the compiled interpreter (`avon/bench/coverage.py`):

- **whnfF, 618 atoms, 348 distinct nodes: 40 of them are dictionary rows**,
  35 of those above the size floor below. The supercombinators survive intact and
  nested — `sp` is a subterm of `step`, `step` of `whnfF`, `rb` of `stepS`,
  `rb1` of `rb` — so one bottom-up hashing pass at load time finds the whole
  hierarchy, not just the top. On `wfN` (1,066 atoms, 621 nodes) 118 nodes
  match a row and 54 are above the floor, the scry ones among them.
- **A hash names a term, not a name.** In that one program `whnfF`, `loop`
  and `whnfF.loop` are one hash; so are `Just` and `suc`, and `Nothing`,
  `nil` and `zero`. In `wfN`, `SteppedN`, `RValN` and `resS` are one term.
  So the dashboard is `hash → (arity, native fn)`, several names may point
  at one row, and the names are commentary.
- **And one name is not one hash across programs.** `sp` over a
  four-constructor object type and `sp` over a five-constructor one are
  different terms with different hashes, which is exactly why
  `DESIDERATA.md` §5 wants a table per object type and why the registry
  refuses to give one name two terms. Keying on the term makes that fall
  out instead of having to be enforced.
- **Matching needs a size floor.** `K` is `Nothing`, `nil` and `zero` at
  once, and occurs five times inside `whnfF`; `I` as an *object-type
  constructor* is three atoms and occurs eight times inside `wfN`. Lift
  already has this floor (`MIN_LIFT_SIZE = 3`); jets take the same one, and
  should take a higher one, since a jet below a handful of atoms cannot pay
  for its own dispatch.
- **Quotation changes the key, as it must.** `<whnfF>` is a Scott datum: a
  different tree, a different hash, no match. A jet for a function does not
  fire on the encoding of that function, and the encoding boundary is
  exactly where it should stop.

### 6.3 Dispatch is a tag test, not a hash lookup

The obvious design — hash every node as it is built, probe a dashboard —
is what `RUNTIME-DESIGN.md` §3a describes, and it is not necessary here.
The hashes of §6.1 are computed once, bottom up, over the loaded program —
one pass over the DAG, so 348 hashes for the 618-atom interpreter, not
1,235 — and after that the structure is already marked. That means:

> The loader matches the dictionary's hashes against the loaded program
> once, wraps each match in an `AV_JET` node, and from then on jet dispatch
> is a tag test on the head node. No hashing during reduction at all.

As built (stage 4), the match returns a fresh copy of the program with the
wrappers in it, sharing no node with its input or the dashboard, which is
what lets share mode's rule of §6.5 hold.

Under §20 code also arrives mid-run, when the running compiler emits it.
Each install is a load in this sense: it hashes the new term and wraps its
matches before the term runs. The rule becomes *no hashing except at load
and install*.

An `AV_JET` node carries a jet id and the index of the term it stands for.
With fewer arguments than the jet's arity it behaves as that term; with
enough, native code runs. This is Turner's built-in combinator set under
another name, which is the same observation §2 of the runtime note already
makes.

A wrapped node keeps its wrapper for as long as nothing rebuilds it, and
neither strategy rebuilds a subterm it is not contracting: a supercombinator sitting
inside a larger term is passed along by reference until it reaches head
position with its arguments, which is when the jet fires. Wrappers are lost
when reduction copies the term apart — `S` distributing over a jetted
subterm produces unwrapped children. That is exactly Vere
losing a battery match, it is not a correctness problem, and it is a further
reason the surface pushes work into supercombinators pulled by projection (`DESIDERATA.md`
§3, Tier 2) rather than large open terms.

### 6.4 The mechanism is old; the licence is not

Matching a term against a table of known combinators and running native
code for it is Turner's extended combinator set and SKIM's microcode
(§14), not a new mechanism, and the parts of §6.1 to §6.3 that are about
*how* to match are engineering choices inside a forty-six-year-old
design. The theorem changes what the mechanism is *for*. Turner's
recognized combinators are an optimization of a reduction the calculus
performs anyway; the interpreter jet performs a structural recognition
that no term can perform for itself (Proposition 3.1), so it is not a
faster path to an operation the language has — it is the only place that
operation exists.

That distinction earns exactly one operational rule, and it is already in
§12: a jet may never quote on behalf of a running term. Everything else
about jets here is Turner's, plus bookkeeping.

### 6.5 Jets and counts

A jet that instantiates a supercombinator's body skips contractions, so
the count of a run that uses one is not the reference's. A supercombinator
jet can keep the count instead, because a supercombinator cannot look at
its arguments.

**Residual jets.** Let `g` be a jet root of arity `k`. Reduce
`g X₁ … Xₖ` in `copy` mode, with fresh atoms `Xᵢ`, until it halts: at an
atom in head position, or at a weak head normal form. Call the halting
state the **residual** `r(g)` and the contraction count `c(g)`. For any
arguments `a₁ … aₖ`, `copy` reduction of `g a₁ … aₖ` performs the same
`c(g)` contractions, none of which enters an argument, and reaches
`r(g)[aᵢ/Xᵢ]`. An argument is inert until it reaches the head, and the atom
run halts exactly there. A residual jet instantiates `r(g)` and charges
`c(g)`, so its count is the reference's, contraction for contraction.

The runtime computes both halves once, at registration, with its own
reducer. A root whose atom run does not halt within a registration bound
is not a residual jet. A residual jet fires only when the remaining fuel
covers `c(g)`; otherwise the reducer steps, so a timeout lands on the
same state it would without jets.

A residual can be larger than the body. It keeps the pending redexes that
normal order has not reached, such as the `(y z)` an `S` contraction
leaves in an argument, and those run later at their own cost or never.
That is why only the residual keeps counts exact. Body instantiation
(§18.1) drops the pending redexes, and is correct up to weak reduction but
not up to count.

**Where this beats Nock.** A Nock battery reads its sample: Nock 3, 4 and
5 test and compare it, so a battery's cost depends on its data, and no
dashboard entry can state it. A closed SKI term cannot factor its
arguments. That is Proposition 3.1, the theorem that keeps quotation out of
the language, and it also makes a supercombinator's head phase a constant
of the term. Vere never needs a jet's cost, because Nock has no fuel.
Avon's object programs have fuel, and a residual jet can pay it exactly.

**Counts, restated.** Residual jets preserve `copy` counts, so they may
run in `copy` mode and inside any fueled run. The conformance suite runs
them on and off and asserts equal counts, a stronger check than equal
values. Body-instantiating jets and native-code jets change counts: they
are off in `copy` mode, and a run using them reports
`(contractions, jet calls)` as two numbers.

**Built in stage 4** (`src/jets.c`, `src/reduce.c`), with these rules the
plan left open:

- **Arity by running, not by the compiler.** The genericity argument
  holds for any `k`, so `k` is the least in 1 to 8 whose atom run halts
  with an atom at the head; a root with none, or a residual of cost 0, is
  not a jet. The registration bound is 10⁶ contractions.
- **Where the dashboard comes from.** `export.py` writes the corpus
  dictionary, `dictionary.tsv`; `avon --jets=` loads it, recomputes every
  row's hash from its term and refuses a mismatch, registers the rows at
  or above a size floor (default 8 atoms: 135 of 282), and wraps each
  jet's inner jets in its term and residual.
- **Compiled residuals.** At registration a residual becomes a list of
  instructions, one per node an instance builds, over constants,
  arguments and earlier results. A fire is that loop and nothing else; a
  first version that walked the template through a hash map per fire made
  jets *slower* than the contractions they replaced, at 4 ns a
  contraction.
- **Share mode never writes a jet's term.** It updates in place, and a jet
  node's term -- the dashboard's, or reached through a residual's inner
  jets -- is what its hash and residual describe. Writing it would leave a
  later `copy` run charging a registered cost against a different tree:
  the first build did exactly that, and `--jet-check` caught it. So the
  matcher returns a fresh copy of the program sharing no node with its
  input or the dashboard; a share-mode instance copies the template's jet
  nodes; a jet node carries a bit saying whether its term is the
  dashboard's; and when a jet does not fire, share mode demotes its node
  to an indirection -- to a private copy when the term is the dashboard's
  -- before entering the term. Copy mode writes nothing and needs none of
  this.
- **Share mode charges a fire the copy cost.** A residual's cost is a
  copy-mode count, so a share-mode run with jets reports more
  contractions than without (T2: 412,300 against 314,309). Share counts
  are reported, never asserted (§1.1).
- **Jets are transparent to every reader but the reducers.** Printing,
  `jam`, the prefix form, probing, hashing and the witness strategy look
  through a jet node to its term (`av_view`); the witness runs jets off
  (§18); a snapshot never holds one (§4.2).

Measured (`tests/test_jets.c`, `tests/test_conformance.c`, release build,
reduction alone): T2 in `copy` mode 2.03 ms without jets and 1.41 ms with
them, 12,801 fires, 504,930 contractions either way; T1 0.38 and 0.27 ms.
Residual jets skip a supercombinator's head phase and nothing more, so the
gain is modest; the interpreter jet (§7) is where the large one is.

### 6.6 Admitting a jet

A jet is a claim, and the claim is checked three ways, all of which the
artifact already does in Python:

1. **Probe tests.** Every entry ships fresh-marker probes, the same ones
   `python/skijack/probe.py` runs. For a residual jet the registration run
   is itself the probe: the term applied to fresh atoms.
2. **Differential.** `--jet-check=N` runs the unjetted term alongside every
   *N*-th fire; `N=1` in the test build. As built, it runs the jet node's
   own term over the fire's arguments in `copy` mode, jets off, for
   exactly the charge, and compares the state reached with an instance as
   graphs -- stronger than comparing decoded values. Only a definite
   disagreement is a fault; a check that runs out of memory or of its
   comparison budget is inconclusive.
3. **Corpus.** The whole conformance suite runs jets on and jets off, and
   the values must agree.

A jet that cannot be validated this way is not registered.

Testing is the admission rule for `share` mode only. Inside a proof the
verifier cannot re-run the term, so a jet there needs a theorem (§18).

## 7. The interpreter jet

**It is Avon's level-1 interpreter, not an optimization of one.** Vere runs
virtualized Nock through `+mock`'s jet. `+mock` is `(mook (mink [sub fol]
gul))` (`hoon.hoon:6180`), and `+mook` only renders a crash's stack trace,
so the jet sits on `+mink` and is `+mock`'s jet in all but name. It uses
the same interpreter as unvirtualized code, jets included. It also
serves Nock 12, the scry opcode, which has meaning only under `+mock`.
Level-1 SKI programs are the ones that scry, so `wfN`'s jet is the path
SKIjack and SKIlark programs actually run on. SKIlark measures level 1 at
about 4,000× level 0 (2.3M contractions against 493); only this jet removes
that.

`whnfF`, `wfQ` and `wfN` get one jet, parameterized by the object leaf set.
It:

- reads the encoded object term — a Scott datum over
  `S | K | I | App t u`, plus `Scry` for `wfQ` and `wfN` — by probing it
  with markers, the same way `run.decode` does, memoized by node index (the
  memo is by index, so the id-recycling trap that `probe.py` documents
  does not arise);
- builds the live term it encodes, as install does (§20.2);
- reduces that term with Avon's own reducer, in `copy` counting, with
  residual jets on (§6.5);
- re-encodes the outcome as the declared result type's datum.

**Avon's own reducer, not a second interpreter.** A native interpreter over
the encoding would collapse one tower level. Reducing live nodes collapses
all of them: an interpreter inside the object term is a live `whnfF`
application, and it reaches the jet again, as nested `+mock` does in Vere,
subject to the fuel rule below.

**A `Scry` leaf, legal only here.** The reducer gains a fourth combinator,
arity 1, which exists only in terms the interpreter jet builds. Its rule is
`wfN`'s `stepScN1`: look the path up in the fact store (§8) and, on a hit,
replace `Scry p` with the answer, at a cost of one object step. On a miss
the jet returns the blocking outcome. At level 0 there is no `Scry` leaf and
nothing to serve, which is Vere's rule for Nock 12 outside `+mock` and the
language's rule (`DESIDERATA.md` item 6).

**Re-encoding is not quoting on behalf of the term.** The jet encodes a
live result, but the datum it produces is the one the unjetted interpreter
computes from data. The running program receives nothing it could not
compute without the jet, so §12's rule holds.

**Fuel is exact.** The jet implements the paper's fuel semantics: fuel `k`
permits `k` step-attempts, the last of which must be the no-redex check, so
`s` contractions need `s+1`. The fuel boundary cases in `EXAMPLES.md` §4
are the test: the answer must flip at the same numeral, not one either
side. Two rules keep it exact:

- The object reducer counts as `copy` does. `whnfF` rewrites a tree datum,
  so an object step is a `copy`-mode contraction; `share` reduction inside
  the jet would give the right values and the wrong timeouts.
- A jet may fire inside the object reduction only if it charges the exact
  `copy`-mode count of what it replaces. Residual jets do (§6.5).
  Native-code jets and body-instantiating jets do not, and stay off inside
  a fueled run. A nested interpreter jet does not either: its charge is the
  outer interpreter's cost of running the inner one, which depends on the
  inner run's data. It fires only when the outer level has no fuel bound,
  until a cost model of `whnfF` per object step exists (§15).

This is where Avon departs from Vere. `+mock` has no fuel, so its jet has
nothing to charge. `wfN` exposes a timeout outcome to the program, and the
jet must reproduce it.

The payoff is the one Nock gets from `+mock`: the paper measures level 1 at
340 contractions per object step and level 2 at ~1,485× on top of that, and
a correct interpreter jet collapses both to roughly the cost of the object
reduction itself. That is stage 5, and it is the stage that makes a third
tower level and the partial-evaluation runs ordinary work.

## 8. Scry

The runtime owns the external side, as §4 item 5 of the runtime note says.
`python/skijack/run.py` already contains the whole protocol and Avon
transcribes it:

- a **fact store**: an append-only list of (key datum, answer datum) pairs;
- `make_resolver`: build the resolver term from `EQ5`, the answer type's
  hit and not-yet constructors, and the facts learned so far. Under the
  interpreter jet (§7) the `Scry` leaf looks paths up natively, keyed by
  the path datum's structure. The resolver term stays the specification,
  and the native lookup must agree with it: comparison is syntactic on
  encodings, as `EQ5`'s is, so `Scry (I K)` does not match the path `K`;
  and fact order cannot matter, because the store is append-only with
  unique keys. Differential runs against the resolver term admit it
  (§6.6);
- the **resume loop**: run, peel the result, and if it is the blocking
  constructor, decode the blocked path, look it up, append, and **re-run
  from scratch**. Re-running is not an optimization failure; it is what
  makes blocking sound under an append-only namespace, and the paper says
  so. Vere does the same: `+mock` returns a `%1` block, and Arvo retries
  from the start.

Two properties to keep visible in Avon's output rather than in a comment:
the namespace is append-only (a key already known and still blocking is
`STUCK`, not a retry), and fuel is not neutral across a resume — a later
round starting from scratch consumes fuel again.

The elided-fuel policy `@[]` is §3c: iterative deepening, doubling from 8 to
a cap of 4096, the cap reported as the timeout outcome. Composed with the
resume loop exactly as `run_with_namespace` composes them.

Two rules for proved runs (§17). The policy may size a budget, off the
record, but may not choose the budget a proof uses: doubling until the run
succeeds publishes its length within a factor of two, which is what a
budget-exact trace exists to hide. And the rounds of the resume loop run
off-circuit; only the final run is proved, with the final fact store as
its committed private input, so the fact store must be exportable, in the
order its facts were learned, as that input.

## 9. Boot

`RUNTIME-DESIGN.md` §3b, unchanged: an executable is a function of the
initial subject, and the runtime starts by applying the loaded term to it.
The initial subject carries the quoted standard library, which settles who
supplies `<subject>`.

A **kernel** is a door in Arvo's shape (SKIjack `SPEC.md` §4.1): a cell
`[battery state]`, battery `[poke [peek load]]`. Avon knows the axes and
no names:

| axis | arm | pulled as |
|---|---|---|
| 4 | `poke : kernel → event → [effects kernel']` | `(4@k) k ev` |
| 10 | `peek : kernel → path → answer` | `(10@k) k p` |
| 11 | `load : kernel → old-state → kernel'` | `(11@k') k' (3@k)` |
| 3 | the state | — |

**The pull is Nock 9's.** Avon selects an arm by axis and applies it to the
whole kernel, `[9 axis 0 1]` with the core as its own subject. An arm
reaches its battery as `2@k` and its state as `3@k`, so no arm names its
own kernel. Selection applies a Scott selector to a pair and never reads a
term's structure, so §12's rule against quotation holds.

**The loop.** Pull `poke`, apply it to the kernel and the event, install
the kernel from the tail of the result, emit the effects from its head, and
serve `peek` to anything that scries. **Upgrade** pulls `load` from the new
kernel with the old kernel's state; the new battery migrates it
(NockApp's rule, §21.2). A kernel can also upgrade itself: `poke` may return
a different battery. A term that is not a kernel is applied once and
reduced.

**Kernel loops run in `share` mode.** The installed kernel's state is the
unreduced application the last poke built. The reference host shares no
work, so under it each poke reduces the whole history again: in the corpus
kernel a `Tick` costs 61, 95, 129, … contractions, 34 more per earlier
event. Update in place computes each state once, 61, 66, then 63 per
`Tick` for as long as it runs (measured with `avon/bench/strategies.py`).
`copy`-mode kernel counts are conformance data, never a cost model, and a
proved poke (§17) proves one event from an installed kernel, not the
history.

Effects and events are terms. Avon does not invent a syntax for them.

## 10. The conformance harness

### 10.1 What Python must export

One new module, `python/skijack/export.py`, run as
`python3 -m skijack.export OUTDIR`. **Built in stage 3**, with two changes
from the first plan, both to keep Avon free of dependencies: one flat
directory rather than one per program, and a line-based manifest rather
than JSON.

```
avon/tests/conformance/
  <target>.skit      the closed executable: container + bitstring (§4.2)
  manifest.tsv       one line per target, tab-separated
```

A target is a closed level-1 executable, `interp fuel <datum>` with the
interpreter's parameters applied. A manifest line gives its host cap, the
status and `copy` contraction count of reducing it to weak head normal
form, the result type's and object type's constructors (`Name/arity`, `*`
on the application constructor), and the constructor and rendered payload
it peels and decodes to. The targets are every level-1 declaration of the
compilable corpus, a policy declaration at the budget `run_policy`
settles on; `EXAMPLES.md` §4's fuel boundary; and the T3 table, whose
`CAP` is a `FUEL` status at host cap 400,000. The atom table is empty:
every target is closed. Atom counts and structural hashes are stage 4's.

The exporter writes the container itself, with a Python `jam`, so the
wire format has two implementations that must agree; skijack's
`tests/test_export.py` pins the codes Avon's `tests/test_wire.c` pins.

This is the only change to the Python side the plan requires, and it is
additive: no existing behaviour moves.

### 10.2 What the suite asserts

1. every decoded value matches, in both strategies, jets on and off;
2. every `copy`-mode contraction count matches the reference exactly;
3. `lower(lift(t)) == t` over the dictionary, computed in C, matches
   Python's answer;
4. `cue(jam(t)) == t` for every corpus term and for reduced states;
5. `print(parse(s)) == s` for every printed form Python emits;
6. the structural hash of every dictionary entry matches Python's, string
   for string, including the `skijack-1:` prefix.

### 10.3 Fuzzing

The differential in `avon/bench/strategies.py` is the template: generate
random small `{S,K,I}` terms, normalize in Avon (both strategies) and in
`aviary`, compare normal forms and — for `copy` — counts. 2,986 terms found
0 mismatches against a Python transcription; against C it should run
millions, under ASan/UBSan, in CI. Add a second fuzzer over the wire format
(`cue` on random bytes must never crash and must reject cleanly).

## 11. Stages, with acceptance criteria

Each stage ends with something testable. Rough sizes are C lines, excluding
tests.

| # | stage | contents | acceptance | ~lines |
|---|---|---|---|---|
| 0 | skeleton | `Makefile` (C11, clang, `-Wall -Wextra -Werror`, ASan/UBSan debug target), `include/avon.h`, unit-test runner | `make check` runs and passes nothing | 150 |
| 1 | heap and reducer | arena, nodes, GC, both strategies, fuel, size cap, statuses, and a reader for the printed form (terms have to get in somehow) | T0/T1/T2 in `copy` mode give 340 / 91,556 / 504,930; `share` mode gives the same values; the random-term differential against `aviary` is clean over millions of terms under ASan/UBSan; throughput ≥ 10⁷ contractions/s in `share` | 900 |
| 2 | the wire format | printer with a node budget, container + bitstring `jam`/`cue`, atom table, hygiene check, arena snapshots | round-trips 10.2 items 4 and 5 on the whole corpus; the bitstring fuzzer never crashes and always rejects cleanly | 500 |
| 3 | probing and the harness | markers, `peel`, `decode`, Scott-numeral reader, manifest runner; `export.py` on the Python side; the `witness` strategy (§17) | every corpus target's decoded value matches; the paper's T3 and scry tables reproduce; every corpus witness passes `lake exe aircheck` and proves and verifies with `lean-ski`'s `bench/plonky3`, at the `copy` contraction counts | 750 |
| 4 | hash and jets | `sha256`, Merkle hash, dashboard, `AV_JET`, loader matching, `--jet-check`, residual jets (§6.5) for the Scott constructors and case forms | hashes match Python's strings; corpus values identical jets on and off; `copy`-mode counts identical with residual jets on and off | 800 |
| 5 | the interpreter jet | one jet for `whnfF`, `wfQ`, `wfN`; decode to live nodes, `copy`-counted object reduction with residual jets, re-encode; the `Scry` leaf against a native fact-store lookup | `EXAMPLES.md` §4 boundaries flip at the same numeral with residual jets on; T2's cost falls to roughly T0's; values unchanged; `scry-*` single runs match the resolver term | 900 |
| 6 | scry | fact store as an append-only log (§19), resolver term as the lookup's specification, resume loop, `@[]` policy | `scry-*` corpus entries reproduce their traces, round for round, including `STUCK` | 400 |
| 7 | boot | pill loader, subject loader, `poke`/`peek`, effects, snapshots, install (§20) | a kernel survives a `poke`, answers a `peek`, and reloads from a snapshot to the same state; `load` moves a state onto a new battery; a kernel installs code its compiler emitted and runs it; per-poke cost in `share` mode stays flat over a thousand events | 700 |
| 8 | self-hosting (§20.3) | the compiler as a term in the pill; the compiler jet, licensed by differential | the compiler term compiles its own source to the term Python produced; the corpus compiles in Avon to Python's terms, hash for hash | 600 |

Stages 1 to 3 are the runtime proper and are worth doing on their own; a
correct, fast, conformant reducer with a harness is the thing everything
else is measured against. Stages 4 and 5 are where the viability argument
of `RUNTIME-DESIGN.md` §2 is either demonstrated or refuted. Stages 6 and 7
are the parts that make Avon a platform rather than a calculator, and they
should not start before 5 is green. Stage 8 makes Avon Vere's peer rather
than a host for Python's output, and it waits for a self-hosted compiler in
the surface language.

The order is deliberate about one thing in particular: **the harness comes
before the jets.** A jet is a claim about agreement, and there is nothing
to agree with until stage 3 exists.

### 11.1 Status

Measured on an Apple M4 Max, clang 21, against aviary-kernel 0.1.0 and
skijack `5d335c0`.

**Stage 0, done.** `make` builds `build/avon`; `make check` builds every
`tests/test_*.c` under ASan and UBSan and runs it, and builds
`build/dbg/avon` for the differential.

**Stage 1, done.** Every acceptance criterion holds:

- `copy` mode gives **340 / 91,556 / 504,930** on T0 / T1 / T2, and T0's
  reduced term is byte-identical to the reference's
  (`tests/test_tower.c`, fixtures from `tests/fixtures/export.py`).
- `share` mode reaches the same normal forms on all three, in 325 / 63,522 /
  324,362 contractions against `copy`'s 371 / 91,587 / 680,290. Its WHNF
  counts on the printed fixtures are 323 / 63,520 / 314,309: they differ
  from §1's 323 / 63,326 / 313,860 because a printed term carries no
  sharing, which is §1's point about share counts.
- **Differential against aviary:** a million random terms (atoms `X`, `Z`,
  2% of leaves the divergent `S I I (S I I)`) at fuel 3, 17 and 400, each to
  WHNF and to normal form: 6,000,000 runs, 0 mismatches in status, count or
  the term reached, 949,462 of them stopped by fuel part way. 22 runs hit
  the oracle's size cap and were skipped (§3.3). Sanitized binary, 29
  minutes (`tests/diff_aviary.py`).
- **copy against share:** a million random terms under ASan and UBSan, the
  same normal form every time and never more steps in `share`.
- **Throughput:** T2 at 63 M contractions/s in `share` and 107 M/s in
  `copy`, parse and process start included; `S I I (S I I)` at 2.6 × 10⁸/s.

Stage 1 found one requirement the note lacked, path compression (§3.1), and
a durability review found three defects, all fixed with regression tests:
a `FUEL` result that could arrive without its term under a tight node cap
(now `SIZE`), NUL bytes in atom names (now refused), and unchecked
allocations in the reducer's hot paths (now asserted in the debug build).

**Stage 2, done.** The container, `jam` and `cue` (§4.2), the hygiene check
(§4.3), and snapshots:

- `print(parse(s)) = s` and `cue(jam(t)) = t`, with `jam` canonical, on all
  281 distinct corpus terms (17 programs; 4 fail skijack's Stage A) and on
  459 reduced states of them, each term run 200 steps in both strategies
  and kept when its tree prints within 200,000 nodes (`tests/test_wire.c`,
  `tests/fixtures/corpus.tsv`).
- The `cue` fuzzer: 2,000,000 hostile inputs, mutated containers and noise
  behind a valid header, under ASan and UBSan. Every one is refused with a
  message or decodes to a term that jams back to the same bytes.
- Snapshots round-trip a part-reduced `share` state node for node and
  resume to the same normal form; any flipped bit in image or sidecar, a
  truncated image, a missing sidecar, and forged images with valid
  checksums but a root past the end, a cycle, a doubly interned leaf, an
  index out of range or a jet node are all refused (`tests/test_snap.c`).

**Stage 3, done.** Probing, the harness, and the witness strategy:

- **Every exported target conforms** (`tests/test_conformance.c`): 45
  targets from skijack `5d335c0` plus `export.py`, each run in both
  strategies. In `copy` mode every status and contraction count matches;
  in both, every value peels to the exported constructor and decodes to the
  exported payload, 86 values in all. That includes the paper's T3 table
  (`Err` gives `RErr` in 127 under `wf5Abs` and host divergence under
  `wf5Omg`; `K I Err` and `I K` give `RVal` in 574 and 438 under both;
  `Ω` gives `RTime` in 10,130), the scry table's eleven rows, the
  character table (16,150 / 62,199 / 47,257 / 16,739), the tower, and the
  §4 boundary (fuel 0 and 1 time out, 2 and 5 give `RVal I`). Corrupting a
  count, a constructor or a payload in the manifest fails the runner.
- **The witness strategy** (`src/witness.c`) reproduces, byte for byte and
  from their terms alone, all nine honest tables `ski-air` writes for
  lean-ski's own corpus (`bench/plonky3/tables/`, generated, not
  committed). On the 43 targets that reach weak head normal form
  (`tests/witness_check.sh`, `make witness-check`): every witness contracts
  exactly as often as `copy` mode; `ski-air` proves and verifies all 43 at
  those counts, T2 at 1,203,249 rows padded to 2²¹ in 22 s; its tables are
  byte-identical to Avon's; and `lake exe aircheck` accepts all 43, all at
  lean-ski `0da9554`, in about two minutes. The two
  `CAP` targets diverge and have no witness. On 300,000 random terms the
  witness halts on copy mode's term, read back as `Mach.decode` reads it,
  after copy mode's count.
- Witness mode refuses terms with atoms for now: lean-ski numbers atom
  cells by its statements' variables, and `aircheck`'s parser has no atom
  cell yet (§17.3).
- A durability review of the stage found the witness machine exact and
  four gaps, all fixed with regression tests: probing assumed its markers'
  leaf ids were consecutive, and nothing reserved their `@` names (the
  parser and `cue` now refuse them, the snapshot loader refuses an image
  in which any node points at one, and a probe finds a marker by its id); a prefix-form file led by a tab was read as one
  atom (the printed form now refuses a backquote in a name, so the two
  forms cannot overlap); a table of an empty run read out of bounds; and
  witness budgets were unclamped.

**Stage 4, done.** The structural hash, the dashboard and residual jets:

- **Hashes match skijack's strings** on all 282 rows of the corpus
  dictionary, recomputed from each printed term, and on seven hand-checked
  terms (`tests/test_jets.c`). The loader finds inside `whnfF`, `wfN`, `UQ`
  and `wf5Abs` exactly the dictionary rows skijack's `hash_all` finds: 28,
  38, 6 and 36 of 147, 224, 33 and 177 distinct subterms.
- **The corpus is unchanged by jets.** All 45 targets, both strategies,
  135 jets registered in one arena shared by every run: every copy-mode
  status and count is the manifest's, all 86 values decode the same, and
  all 50,298 fires pass `--jet-check=1` (`tests/test_conformance.c`).
- **Every jet over random arguments** -- one to three extra, random fuel
  including the boundary, weak head and full normal form: copy mode stops
  at the same state after the same count jets on and off, share mode
  reaches the same normal form, every fire checked. 200 rounds, 27,000
  runs, under ASan and UBSan.
- **Mixing strategies is safe.** After share runs over jetted terms,
  every dashboard term hashes as before, and a graph a share run has
  reduced still counts the same jets on and off. `--jet-check` catches a
  jet whose cost is off by one.
- **Jets survive collection** (an arena of 64 nodes) and never reach a
  snapshot. The witness check still passes at lean-ski `4f78405`: 43 of
  43 proved, identical, accepted.

The stage's own build had three defects its tests or a durability review
caught, all fixed with regression tests: share mode wrote inside jets'
terms (§6.5); instances first walked templates through a hash map per fire
and made jets slower than no jets; and snapshot save collected the arena
in place, writing the dashboard -- with its `@x` markers -- into every
image, which also reopened the marker hole stage 3 had closed. The review
also had `--jet-check` treat an out-of-memory check as inconclusive rather
than a fault, and guarded the instance buffer against re-entry.

## 12. What Avon must not do

Inherited from `RUNTIME-DESIGN.md` §5, still binding:

- change any count the paper reports — the reference host is the oracle;
- reduce under a jet in a way the unjetted term would not;
- quote on behalf of a running term. The compiler quotes. The runtime never
  turns a live value into data for a program to inspect, because the
  language promises that cannot happen, and Proposition 3.1 is why the
  promise is keepable. Install (§20.2) runs the other way, from data to a
  live term, and stays inside this rule.

Three more this plan adds:

- **never report a `share`-mode count as a contraction count of the paper's
  artifact.** The two numbers go in two columns.
- **never print a reduced state as a tree without a budget.** The unfolding
  is exponential and the runtime knows it.
- **never silently accept an atom that the Python oracle would contract**
  (§4.3).

And three that proofs add (§17, §18):

- **never emit a witness from `share` mode**, or from a run with a jet whose
  tier theorem is not proved;
- **never choose a published budget from the run it bounds**;
- **never let a structural hash stand where a proof needs a commitment.**

And one that jets add (§6.5):

- **never write a jet node's term, or anything the jet dashboard holds.**
  A jet's charge is exact only for the tree its hash names.

## 13. Corrections this plan makes to `RUNTIME-DESIGN.md`

Stated plainly so the note can be amended rather than quietly contradicted:

1. **§4 item 1.** "Output must reproduce every count in the paper exactly"
   is achievable only by a non-updating reducer. As written, alongside "hash
   consing of application nodes", it asks for two incompatible things.
   Replace with the two-strategy contract of §1.1.
2. **§3a, hash-consing.** It is not what makes jet lookup O(1) — loader-time
   wrapping is (§6.3) — it is worth ~16% of contractions at the price of a
   probe per allocation, and it can make the graph cyclic. Flag, default
   off.
3. **§3a, reclamation.** The claim that the arena is acyclic is correct for
   SKI update-in-place, so refcounting is sound; but it costs a field per
   node and does not compact, and enabling hash-consing would invalidate the
   acyclicity it relies on. Stop-and-copy first.
4. **§1, throughput.** "About 12,000 contractions per second" is low for
   this machine: T2's 504,930 contractions run in 8.3 s here, about 61,000/s.
   Worth re-measuring before it is quoted anywhere. For scale, a *Python*
   transcription of the sharing strategy runs the same job in 0.15 s — so
   about 55× of the expected speedup is strategy and representation, before
   any of it is C, and the language buys the order of magnitude after
   that. The funding drafts in `ski-in-ski/funding/` quote the Python
   reference at about 10⁴/s; reconcile the two before either goes out.

## 14. Ancestry

What this runtime is a re-implementation of, so that the claim is never
implied by silence. Titles and years are believed right; **page ranges
and exact titles are from memory and must be checked before any of this
is cited** (the same caveat `RUNTIME-DESIGN.md` §6 carries). Turner's SP&E
paper (9:31–49, 1979) and Jay and Given-Wilson (JSL 76(3):807–826, 2011,
Theorem 3.2) are now checked, in `lean-ski`'s `paper/refs.bib`;
Proposition 3.1 is proved there as `no_quote`.

| what | where it comes from |
|---|---|
| bracket abstraction as the compiler's back end | Turner, *A New Implementation Technique for Applicative Languages*, SP&E 9(1), 1979; and *Another Algorithm for Bracket Abstraction*, JSL 44(2), 1979 |
| the supercombinator as the unit of compilation | Hughes, *Super-Combinators*, LFP 1982 — the word and the lifting are his, the motivation is not: he proposed them as the alternative to compiling into a fixed combinator set, and here the fixed set is the ISA |
| compiling that to a machine | Johnsson, *Efficient Compilation of Lazy Evaluation*, 1984; Peyton Jones, *The Implementation of Functional Programming Languages*, 1987 |
| graph reduction with sharing and update in place | Turner 1979 |
| a machine that reduces combinator graphs directly, with recognized combinators run natively — **jets, in hardware, in 1980** | Clarke, Gladstone, MacLean and Norman, *SKIM — The S, K, I Reduction Machine*, LISP 1980; Stoye, Clarke and Norman, *Some Practical Methods for Rapid Combinator Reduction*, LFP 1984; Stoye, *The Implementation of Functional Languages Using Custom Hardware*, Cambridge Computer Laboratory TR 81, 1985 |
| the cost of abstraction in combinators per symbol | Noshita, IPL 20(2), 1985; Joy, Rayward-Smith and Burton, *Efficient Combinator Code*, Computer Languages 10, 1985 |
| graph reduction in hardware, modern | Naylor and Runciman, *The Reduceron Reconfigured*, ICFP 2010 |
| the jet dashboard's matching and registration discipline | Vere, and the Urbit whitepaper |
| what the runtime may do that the calculus may not | Jay and Given-Wilson, JSL 76(3), 2011, §3 |

The one question that separates this runtime from SKIM is not a
technique but a location: SKIM's answer to *where does the interpreter
live* is microcode, and this project's answer is that the interpreter is
a term. Avon exists to make that answer affordable, not to make it true.

## 15. Decisions still to take

- ~~`I` as a third bitstring leaf code versus expansion to `S K K`.~~
  Settled in stage 2 (§4.2): the third code, and atoms after it.
  Decided: retain `I` as third code.
- Whether `copy` or `share` is the default strategy for a bare `avon run`.
  Recommended: `share`, with the strategy printed on every report.
  Decided: `share` as stated.
- ~~Whether a jetted snapshot records the dashboard version.~~ Settled in
  stage 4: a snapshot holds no jets and no dashboard, so it has no version
  to record; jets are matched again after a load. Jet ids are local to an
  arena and never persisted.
  Decided: agreed.
- ~~Whether Avon ever serves `peek` to a *level-0* program.~~ Settled
  (§7): no. The `Scry` leaf exists only in terms the interpreter jet
  builds, as Nock 12 has meaning only under `+mock`.
- A cost model of `whnfF` per object step: the exact `copy`-mode count the
  interpreter spends on one object step, as a function of the object
  state. Without it a nested interpreter jet cannot fire inside a fueled
  run (§7). Not needed before stage 5 ships; the rule keeps it off.
- The residual-jet theorem in `lean-ski`: `copy` reduction of a closed
  term applied to atoms, halted at an atom head or a WHNF, instantiates to
  the reduction of the same term applied to any arguments, with the same
  count (§6.5). It is the genericity lemma, and it licenses residual jets
  in `witness` mode with exact row counts, which §18.1's body
  instantiation does not give.
- ~~The pill's contents and layout.~~ Settled (§20.1): a pill is one term
  whose value, applied to the subject, is a kernel door (§9). Still open:
  whether the standard subject ships compiled, quoted, or both. Needed
  before stage 7.
- Whether install is a runtime primitive the kernel invokes or a `UQ`
  application the runtime jets (§20.2). Recommended: the jet, so the
  calculus alone still defines what install means.
  Decided: the jet.
- Whether a witnessed run may include compilation, and so whether the
  compiler jet needs a proof licence (§20.3). Recommended: not before the
  interpreter jet's licence exists.
- Whether Avon splits into a supervisor process and a worker, as Vere does
  (§20.4). Needed before stage 7.
  Decided: yes we will split; consult me for terminology and boundary before coding it.
- Atoms in the circuit. Decided and done in `lean-ski` (§17.3): the
  machine has an inert `atom` cell and the AIR a halting kind for it. What
  remains is carrying atoms through the Plonky3 tables and the checker.

## 16. Provenance of the numbers in this note

Every count in §1, §2 and §13 was measured on this machine against
`aviary-kernel` 0.1.0 and `tower_harness.py` from `artifact-metacircular-ski`. The script is
`avon/bench/strategies.py`, and it reproduces the whole of §1 in about a
second: the four strategies on the three targets, their node, probe, spine
depth and result sizes, the cycle check, and the 2,986-term differential.
Run it before trusting any number here, and again from C when stage 1
lands.

§6.2's coverage figures come from `avon/bench/coverage.py`, which compiles
a corpus program, builds its dictionary, and reports which rows occur inside
which — the same pass the C loader will make, so the two should agree once
stage 4 lands.

Two details that bite: T2 is `--kk 500` — the harness's default object fuel
of 120 is below what the inner term needs, and produces a different, smaller
run — and node counts include the leaves built at load, so they are node
counts and not atom counts.

## 17. Proofs: the witness strategy

*Added 2026-09-27.* The proof system is in `lean-ski`. Its circuit
(`Ski/Air.lean`, built in Plonky3 in `bench/plonky3`) proves runs of one
machine, the write-once heap machine of `Ski/Heap.lean`:

- a row is the machine's registers: head pointer, stack pointer and
  allocation counter;
- the heap is one committed memory table of cells `S | K | I | A f x | N |
  C x r`, addressed in allocation order, each written once at the counter,
  with the argument stack in the heap as `C` cells;
- the rule table is `Air.stepG`: an unwind pushes one stack cell, `I` and
  `K` pop their arguments, `S` writes three cells.

Lean decides the constraints on a concrete table (`Air.checkA_iff`, run as
`lake exe aircheck`) and proves that an accepted table ends on the value
the reference reducer reaches (`Air.air_sound`).

Neither strategy of §1.1 produces that trace. `copy` has the circuit's
contraction counts, but holds arguments in a C vector and writes no stack
cells. `share` updates in place, and the circuit proves no update in place.
So Avon adds a third:

- `--strategy=witness`: `Air.stepG` executed literally over an append-only
  arena in the circuit's cell encoding. No collection, no hash-consing, and
  jets only as §18 allows. It emits the rows and the memory table, padded
  to public budgets (§17.2). Its contraction counts equal `copy`'s, and its
  values equal both. The Rust `step` and `traces` in `lean-ski`'s
  `bench/plonky3/src/main.rs` are its reference.

`share` stays the way to find an answer fast. The proof comes from a
witness-mode replay, which must reach the same decoded value.

### 17.1 What a witness is

- The rows and the memory table, in the format `Ski/AirCheck.lean` reads,
  or directly as the prover's traces.
- Nothing from the arena. A §4.2 snapshot carries indirections, jet nodes
  and the collector's moves; the memory table has none of them.
- Weak head normal form only. The circuit proves reduction to WHNF, as
  `run.py` runs it (`whnf_only`), so a `NORMAL` run has no witness.

### 17.2 Budgets are public

A proved run reports three quantities, apart:

- **host fuel**, in contractions (§3.2);
- **rows**, one per transition, contractions and unwinds together: about
  2.44 per contraction on the corpus (`lean-ski`'s `lake exe aircost`);
- **memory cells**: the loaded heap, plus one cell per unwind and three
  per `S`.

The circuit accepts a table of `k` rows exactly when `k` exceeds the run's
transitions (`Air.air_budgets`), and the memory table pads to any larger
size (`Air.Accepts.pad`). So the caller fixes both, as powers of two, before
the run, and publishes them with the statement. §8's rule applies: the
elided-fuel policy may size a budget off the record, but may not choose the
one a proof uses.

### 17.3 What a witness does not yet give

- **An output, except by probing.** The constraints fix the run, not the
  value it ends on. Probe decoding (§1, §7) binds it: `v X₁ … Xₙ` reaching
  `Xᵢ` at the head names the constructor, and the stack holds its fields.
  `lean-ski` has the inert atom cell this needs, with a halting kind for an
  atom at the head. A table started from a term applied to atom markers,
  whose last row has the atom `i` at the head, proves that the term
  reduces to `Xᵢ` applied to arguments (`Air.air_probe`). The Plonky3
  tables carry atoms (tag 6), and an AIR may require its last row to read
  a named accepting atom.
- **Secrecy, except for statements.** The corpus proofs load the whole
  term in the clear under a non-hiding commitment. A statement `V x w`
  keeps `w` private: `lean-ski` proves a Sudoku solution in zero
  knowledge (`Ski/Sudoku.lean`, `bench/plonky3/src/sudoku.rs`), with a
  hiding PCS, the witness as a private table of Scott Booleans, fixed
  heights, the last row checked for the accepting atom, and blinding for
  the per-table lookup sums Plonky3 publishes, which otherwise let a
  verifier check a guessed witness. The verifier checks the statement file
  in Lean first. Other witness shapes need their own witness tables and
  blinding. The zero-knowledge argument is informal.
- **Scry.** Only a resume loop's final run is proved, with the final fact
  store as a committed private input (§8).

## 18. Jets in a proof

§6 licenses a jet by testing: probes, differential runs and the corpus.
Inside a proof the verifier cannot re-run the term, so a jet there is a
precompile, licensed by a theorem. There are three tiers, in the order to
build them.

### 18.1 Supercombinator jets: one theorem for all of them

Every lifted λ-chain compiles to a closed combinator, `absN (caps ++ ps)
body`, applied to its captured variables (`wrapLift`, in skijack's `comp`
and `lean-ski`'s `Ski/Compile.lean`). Applied to all its arguments, it
reduces to the body with the arguments substituted. `lean-ski` proves that
once, for every body: `absN_beta_close` is weak β for all formals at once.
The reduction it replaces costs up to `3^k · vsize body` weak contractions
for `k` formals (`absN_beta_count`). A supercombinator jet replaces all of
it with one instantiation of the body. That is the Reduceron's template
instantiation, and its licence is one theorem, not one per jet.

**The licence, proved in `lean-ski`** (`Ski/Inst.lean`). An instantiation
pops the arguments' pointers and writes the body's cells at the counter
(`Mach.instStepG`): a formal becomes its argument's pointer, and any other
variable becomes a public address. When each public address holds its
variable's meaning and the head reads back as `absN xs body`, the state
after reads back as a weak reduct of the state before (`Mach.inst_sound_g`;
`Mach.inst_sound` is the case with no public addresses). A run mixing
machine transitions with instantiations and halting on a weak head normal
form proves normal-order evaluation up to weak reduction of the value
(`Mach.jet_run_eval`). Weak reduction from a WHNF keeps its head and arity
(`small_lemma_whnf`), so a jetted run reads back the head and arity an
unjetted one does (`jet_run_shape`). The value is the same; the
contraction count is not. Carrying this to atom probes needs instantiation
over terms with atoms, which the built rows do not have.

**The circuit, built in `lean-ski`** (`Ski/AirJet.lean`,
`bench/plonky3/src/jets.rs`, `bench/plonky3/DESIGN.md` §2). The CPU gains
one row kind, `INST`, and five tables join the three of §17:

- **ROOTS, HDR and TMPL**, preprocessed from the public jet table below:
  the licensed roots; each jet's arity, cell count and root; and its body
  cells in `ibuild` order, each operand a cell this instantiation wrote, an
  argument, or a public cell.
- **POP**, one row per argument: it reads a stack cell below the
  instantiation's counter and provides the argument's pointer.
- **INSTW**, one row per cell written: it looks up its template row,
  resolves the operands, and writes the cell at the counter.
- **`INST`** itself looks up the root and the header, runs a POP chain over
  the arity and an INSTW chain over the cell count, and sets the head to
  the body's root, the stack to the rest, and the counter past the cells.
  Both chains are keyed by `clk`, a row counter, so each instantiation's
  chains are its own.

An `INST` row is `Air.instRow` at a licensed root, and a table the
verifier accepts satisfies `Air.AcceptsJ`, so it proves the evaluation it
ends on, up to weak reduction of the value (`Air.air_sound_jet`).
`lake exe jets check` decides this on a concrete table
(`Air.checkJA_sound`). Budgets count rows: `INST`, POP and INSTW rows all
count.

**The public jet table** (`JetTable.jetTable`, written by
`lake exe jets emit`) comes from the compiler's own templates: each
equation, each lifted λ-chain, each constructor (`ctorO`). Each maximal
closed subterm of a body becomes a *global*, a public cell in the loaded
heap, so an instantiation writes only the body's open part. The roots are
found by hash-consing the loaded heap, and each is kept only if
`Air.rootOKB` licenses it. The verifier trusts none of this: before it
builds its preprocessed tables it runs `lake exe jets statement`, which
checks that each jet file is exactly Lean's for the term it will prove and
that its roots pass `Air.rootsOKB`.

**Identity is static, and a root is an address.** The first plan of this
section put a jet cell `J g` at the head; the built circuit uses the roots
table instead. It needs no new cell and no change to `decode`: `termAt`
below the first counter never changes (`Air.termAt_take`), and `S` copies
pointers, not cells, so a copy of a root is the root and stays jettable.
No hash is trusted. The structural hash of §5 finds candidates; Lean's
recomputation licenses them.

**Two findings changed the plan.**

- **Globals.** A compiled body inlines whole closed words, so writing
  every cell of the body costs 2.2–6.0× the plain run's rows on the
  compiled corpus rows and `3 sumto` (224% to 597%). With globals, a
  jetted run takes 28–34% of the plain run's rows.
- **η-templates are never roots.** `λ xs. G xs`, with `G` closed,
  compiles to `G` itself; instantiating it rewrites `G xs` to `G xs`, and
  a run jetted there loops.

On the interpreted rows jets do not pay. Each instantiation there is
short, and the POP rows it adds outnumber the CPU rows it saves: 110–112%
of the plain run's rows with globals.

**It cannot quote.** An instantiation moves argument pointers and never
inspects what they point to. So the one rule the theorem does not give
(§12: a jet never quotes for a running term) holds by construction.

**These are not the jets of §6.5.** Avon's stage-4 jets are residual jets:
found by running, keyed by the structural hash, charged their exact
`copy`-mode cost, and licensed by testing. A proof jet instantiates a
body, changes the count, and is licensed by `inst_sound_g` at a root Lean
emitted. The two tables differ, and the `witness` strategy runs with
residual jets off. When it gains proof jets, it should:

- jet at the roots `lake exe jets emit` lists for the term, and nowhere
  else;
- write each body in `ibuild` order, its globals as pointers;
- number its rows, since `clk` keys the POP and INSTW chains;
- stay byte-identical to `ski-air`'s jetted tables, as its plain tables are
  to `ski-air`'s plain ones (§11.1).

### 18.2 Data jets: native values at the boundary

Arithmetic on Scott numerals is unary, so a jet for it pays only over
native values. That needs a word cell `W n`: an inert leaf with a
field-element payload, whose meaning is a term, `⟦W n⟧` being the numeral
`n`. Each jet then gets a table that proves its function on words (`ADD`,
with range checks, and so on), joined to the CPU by a bus.

The licence is per jet: a Lean theorem that the jet's term, applied to
`⟦a⟧ …`, weakly reduces to `⟦f(a …)⟧`. That is `lean-ski`'s word-level
composition theorem for that word (`composition`, with the three-valued
contract proved for the kit's eliminator and owed per table). It is the
paper's jet contract, and the word type is the representation ABI at the
VM boundary.

### 18.3 The interpreter jet

§7's jet collapses a tower level. As a precompile its licence is the
tower's adequacy theorem: the self-interpreter, on an encoded term,
computes the encoding of the term's value. It reads encoded data, which is
allowed. It is the last tier and has the largest payoff.

### 18.4 What changes elsewhere

- §6.5: a jetted witness reports jet calls beside contractions, and has
  fewer rows, not the same count.
- §6.6: testing stays the admission rule for `share` mode. In `witness`
  mode a jet is admitted only when its tier's theorem is proved: 18.1
  once, 18.2 per jet, 18.3 once.
- §6.5: a residual jet in a witness would reach the term the unjetted run
  reaches, not merely a weak reduct of it, and would charge the unjetted
  contraction count, in fewer rows and with a different memory table. It
  needs the genericity theorem §15 lists and an `INST` row that writes the
  residual rather than the body; `inst_sound` does not cover it.
- §11: stage 4 built §6.5's residual jets, which keep `copy`-mode counts
  and need no proof outside a witness. The proof jets of 18.1 come with
  the `witness` strategy's jetted tables. They need no per-jet proof, and
  they cover the Scott constructors, which compile to `absN` like any
  lifted chain (`ctorO`). Numeral arithmetic is recursive, not one
  template, and waits for 18.2's word cells.

## 19. Lessons from Nockchain's persistent memory arena

*Added 2026-09-27, from `nockchain-official` master at `6ccb9e85`:
`docs/pma/DESIGN.md`, `crates/nockvm/rust/nockvm/src/pma.rs` and the
`docs/pma/` incident notes. What is read in that code is marked as such;
the rest is inference.*

**What it is (read).** The PMA is a file mapped `MAP_SHARED`, which the
runtime reaches by offset from a base, with a 64-byte trailer at the end
holding the allocation offset. Allocation only bumps. After each event
the new state is copied forward into the arena; nodes already there are
terminals the copier never descends into, and old pages are never
rewritten. Reclamation is a periodic Cheney copy into a second slab. They
built a b-tree heap with mark-and-sweep and dropped it, at about 35 s
against about 5 s. There is no hash-consing; the mug is cached in the
metadata word. A snapshot is a copy of the slab, hashed over its used
prefix.

**It confirms §2.** Bump allocation, indices rather than pointers, a
stop-and-copy collector and snapshots of the used prefix are where
Nockchain arrived after trying the alternatives. Four details to adopt:

- keep arena metadata outside index space, as their trailer does;
- hash only the used prefix of an image;
- write the root and a checksum last, in a sidecar, after the data is
  synced, and reject an image whose root lies at or beyond its allocation
  offset;
- verify an image before trusting it. Their design calls raw slabs from
  third parties unsafe to load (read), and Avon's loader should refuse
  one that fails its checksum.

**Durability order, for §8 and §9 (read, then adopted).** Nockchain appends
the event to its log first, then advances the heap, then writes the
trailer, syncs, and writes the sidecar last. Recovery loads the latest
verified image and replays the log from it. Avon's kernel loop should keep
the same order, and the scry fact store should be an append-only log in
that order. That log is also the committed private input §17.3 needs, in
the order its facts were learned.

**Jets, for §6 (inferred).** Nockchain's cold, warm and hot jet state and
its ancestry checks exist because a Nock formula's meaning depends on its
subject. §6.1's closed-term argument removes that need, so Avon should not
import the machinery. Keep the dashboard derived, rebuilt at load time,
and never persisted: Nockchain's persisted cold state held process-local
pointers, and a PMA boot now rebuilds it empty (read, `form.rs`). Avoid
rebuilding the whole table on each registration, and avoid an equality
test that mutates during lookup; both are in their code.

**Witness mode, for §17 (inferred).** Nockchain's write-back is
append-only, but four of its writes would break the circuit's write-once
memory, and the witness strategy must forbid each:

- forwarding pointers written into from-space, so no collection during a
  witnessed run: size the arena first;
- unifying equality, which rewrites slots, and so no indirection rewrites
  (`AV_IND`) and no hash-consing;
- caching a hash in node metadata: keep any hash cache in a side array;
- a trailer rewritten on every allocation: in witness mode the bump
  pointer is the counter, `ctr`, and it is recorded in the rows.

Their prover takes nothing from the runtime heap (read): its memory table
lists noun nodes by content, not by address, so nothing there resembles
the allocation-ordered memory table `lean-ski`'s circuit uses. Avon's
witness mode is the first runtime path that must produce one.

**Pitfalls they hit (read), and what Avon takes from them.**

- A boot loop advanced the persisted allocation offset without a new
  event, and copying runtime caches into the arena grew one file from
  1.6 GiB to over 8 GiB. Only a committed root may advance a persisted
  offset.
- Snapshot cleanup moved the valid snapshots aside, and a collection then
  destroyed the only fallback. Never collect without a verified image to
  fall back on.
- "Alien noun" bugs: raw words were decoded against the wrong arena, and
  the fix was branded handles. Avon's `uint32_t` indices carry the same
  risk the day there are two arenas, such as a snapshot and a live heap.
  Tag indices by arena in any API that sees both.
- Checking tag and location on every dereference cost them 1.13× to 4×.
  This favours Avon's single index space, with no location bits in a
  node.

## 20. Avon is to SKI as Vere is to Nock

*Added 2026-09-27.* Vere contains no Hoon compiler. The compiler is a Nock
term inside Arvo; Vere runs it, jets parts of it, and boots it from a pill.
Taking that relation as the model keeps §0's rule that Avon's C does not
compile, and moves the compiler from Python into a term Avon runs. Four
things follow.

### 20.1 Boot from a pill

A **pill** is the bitstring (§4.2) of one term `P`. Boot is §9 unchanged:
Avon cues `P`, applies it to the initial subject, and reduces to weak head
normal form, and the value must be a kernel (§9). So *pill* names the
interchange form, *executable* names the same term by its role, and
*kernel* names the shape of its value. The compiler and the standard
subject ride inside the subject or inside `P`; the pill has no layout of
its own. This is NockApp's form, one jammed kernel, not Vere's pill of
boot events (§21.3).

Python `skijack` builds the first pill, as a cross-compiler builds the
first native toolchain. After that it plays two parts: the oracle every
run is checked against, and the witness that the bootstrap closed (§20.3).
A pill records the dictionary version its jets were matched under, by
§15's rule for snapshots.

### 20.2 Install: data to live term

Nock lets code and data share one representation, so Arvo runs freshly
compiled code with `.*` and nothing more. SKI keeps them apart. A compiler
term outputs an *encoded* term, a Scott datum over `S | K | I | App t u`,
and a program can run it only after something decodes it into live nodes.
Inside the calculus that decoder is `UQ` (43 atoms); the runtime may do the
same work natively.

**Install** is that step: read a datum by probing, as `run.decode` does,
and build the live term it encodes. It runs from data to a live term, the
direction Proposition 3.1 permits. Quotation runs the other way, and §12
still forbids it: the compiler quotes source text, and no running term ever
receives a quotation of a live term.

Install is also where jets are matched for code that arrives mid-run.
Nock's analogue is the `%fast` hint, which asks the runtime to register a
core as it is built. Avon needs no hint, because install is an explicit
boundary: it hashes the new term and wraps its matches, as the loader does
(§6.3), before the term runs.

Install as a `UQ` jet, rather than a primitive, keeps its meaning inside
the calculus: the unjetted term defines what install does, and the native
code is checked against it like any other jet (§6.6). §15 records the
choice.

### 20.3 The compiler jet

Bracket abstraction run as SKI reduction will be slow. Vere's answer for
Hoon is jets on the compiler's hot `+ut` arms (`crop`, `fish`, `fuse`,
`mint`, `mull`, `nest`, `rest`; `play` is not jetted), with memo caches in
the `mint` and `nest` jets and `%memo` hints elsewhere, and the Nock
term as the definition. Avon's answer is the same: native bracket
abstraction, specified by the compiler term. This is the only route by
which compilation code enters Avon's C, and it enters as a jet.

- **In `share` mode** the licence is §6.6's: probes, differential runs
  against the unjetted compiler, and the corpus, which must compile to
  Python's terms hash for hash.
- **In `witness` mode** it needs a fourth tier beside §18's three: a Lean
  theorem that the native compiler agrees with `lean-ski`'s
  `Ski/Compile.lean`. That theorem does not exist, and it is larger than
  §18.1's.

The return on that theorem is a statement Vere cannot make: a proof of a
kernel run could cover compilation too, binding source text to the term it
compiled to and to the value that term reached.

**The bootstrap closes** when the compiler term, run in Avon, compiles its
own source to the term Python produced for it. That is stage 8's
acceptance test (§11), and a fixed point checked once per compiler version
thereafter.

### 20.4 What else the analogy imports

Vere is more than a Nock interpreter. Its other duties map onto Avon as
follows, and each needs a decision before stage 7, not now.

| Vere | Avon |
|---|---|
| event log, snapshot, replay | §19's durability order: log first, then heap, then a checksummed sidecar |
| I/O drivers turning the world into events | drivers that build event terms and `poke` them (§9); effects are terms |
| king and serf processes: the serf (`mars.c`) holds the loom and the event log, the king holds the I/O drivers | undecided (§15); Vere's split puts the log with the arena, so a worker that commits an event holds the state it produced |
| the jet dashboard | derived at load and install, never persisted (§19) |
| `+mock` and its jet | the interpreter jet (§7, §18.3) |
| the Hoon compiler in Arvo | the SKIjack compiler in the pill (§20.1, §20.3) |

## 21. Vere and NockApp, compared

*Added 2026-09-27, from `urbit/vere` (paths under `pkg/`) and
`nockchain-official` (`crates/nockapp`, `crates/nockvm`). Each claim below
was read in the source; lessons for Avon are marked as such.*

### 21.1 What both runtimes do

| concern | Vere | NockApp / nockvm | Avon |
|---|---|---|---|
| virtualization | `+mock`'s jet, registered on `+mink` since `+mock` is `+mink` plus trace rendering (`jets/tree.c:995`); it calls `u3m_soft_run`, which pushes a road and runs the same bytecode interpreter, jets live | the same jet on `+mink` (`jets/hot.rs:526`), fresh memo cache, scry gate pushed | the interpreter jet (§7), running Avon's own reducer |
| scry | Nock 12 calls the head of the road's gate list; the gate runs with the tail, so a scry inside a gate reaches the next layer out (`manage.c:1817-1827`) | `scry_stack` noun list; same pop-and-recurse (`interpreter.rs:1360-1450`) | one resolver per interpreter level; nested levels nest resolvers the same way |
| scry at level 0 | `%exit` bail: the gate list is empty | kernel panics: ".^ invalid outside of virtual Nock" (`form.rs:2296`) | no `Scry` leaf exists (§7) |
| blocking | gate `~` → `%1` tone with the path; road discarded, no continuation (`nock.c:2663`) | gate `~` → `[1 path]` (`jets/nock.rs:173`) | blocking outcome; re-run from scratch (§8) |
| nesting depth | memory only; `%meme` when a road will not fit | not checked | memory only |
| jet key | SHA-256 of the jammed battery plus a parent axis chain (`jets.c:105-135`, 579-615) | hot table by path, warm table by formula and battery chain (`warm.rs`) | the term's structural hash alone (§6.1) |
| jet testing | not checked | `NOCK_TEST_JETS`: run jet and Nock, compare, `%jest` on mismatch (`interpreter.rs:875`) | `--jet-check=N` (§6.6) |
| budget | none | `op_budget`, fails as `%fail`, used by constant folding only | fuel with its own `FUEL` status (§3.2, §3.4) |
| event log | LMDB, held by the serf (`mars.c`) | SQLite, `synchronous=FULL`, full job jammed with entropy and time (`event_log.rs`) | append-only log, §19's order |
| effects | released only after the event commits (`mars.c:847`) | released after the append (`form.rs:1388`) | same |
| failed event | converted to a `%crud` error event | retried as `%crud` (`form.rs:2358`) | see §21.2 |
| boot | pill `[%pill typ bot mod use]`; boot events run by `u3v_life` (`mars.c:1592`) | jammed kernel trap, `[9 2 0 1]` (`form.rs:2038`); no pill | pill (§20.1) |
| upgrade | kernel reloads through Arvo | saved state fed to the new kernel's `load` arm (axis 4); hash mismatch not fatal (`form.rs:497`) | see §21.2 |
| prover trace | — | not from nockvm: the prover runs its own Nock interpreter, `++fink`, written in Hoon | the `witness` strategy, a separate loop (§17) |

### 21.2 Lessons adopted

- **A kernel has three arms: `poke`, `peek` and `load`.** NockApp upgrades by
  feeding the saved state to the new kernel's `load` arm, with no replay,
  and lets the kernel migrate its own state. Avon adopts it: install (§20.2)
  delivers the new kernel, and `load`, at axis 11 of its door (§9),
  receives the old state.
- **An event that fails becomes an error event.** Both runtimes convert a
  crashed poke into `%crud`. SKI has no crash state (`lean-ski`: a run ends
  in a WHNF or diverges), but a poke can end in `FUEL` or `SIZE`. Avon
  commits neither: it discards the run and pokes the kernel with an error
  event naming the original and the status. A kernel that fails its error
  event too is left unchanged, and the event is logged as rejected.
- **The log records everything a replay needs.** NockApp jams entropy and
  time into each logged job, so replay is deterministic. Avon's events are
  terms built by drivers; any entropy or time a driver adds goes into the
  event term before it is logged, never beside it.
- **No memoization across a scry.** Vere saves `%memo` results only when
  no scry gate is live (`nock.c:2796`), because a result under a gate
  depends on the namespace. Avon's caches follow the same rule: the decode
  memo keyed by node index is safe, and any cache of a reduction result
  inside the interpreter jet is keyed by the fact store's length or off.
- **Differential jet testing is a runtime mode from the first jet**, as
  `NOCK_TEST_JETS` is. §6.6's `--jet-check` already says so; NockApp shows
  it is cheap to keep.
- **The witness comes from a separate interpreter.** Nockchain does not
  instrument its fast VM for proofs; it runs a second interpreter that
  records the trace. §17's `witness` strategy is the same choice: a
  separate loop over a separate arena, never `share` mode with a recorder
  attached.

### 21.3 Where Avon differs, and why

- **Jet keys.** Vere and nockvm key jets on a battery plus its parents,
  because a Nock formula's meaning depends on its subject. A closed SKI
  term's meaning depends on nothing else (§6.1), so Avon keys on the term
  and needs no cold, warm or hot state.
- **Jet cost.** Neither runtime can state a jet's cost, because a battery
  reads its sample. Avon's residual jets state it exactly (§6.5), and fuel
  inside the interpreter jet depends on that.
- **Budgets.** nockvm's `op_budget` is a compile-time aid that fails as
  `%fail`. Avon's fuel is part of the language's semantics, and `FUEL` is a
  status, never a crash.
- **Boot.** Vere boots from a pill of events; NockApp boots from a single
  jammed kernel. Avon takes NockApp's form (§20.1): one term, not events,
  since Avon has no boot sequence beyond applying the pill to its subject.
  Its kernel is Arvo's door, pulled Nock 9's way (§9).
