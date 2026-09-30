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

**Nested reductions** (stage 5). A reduction in progress registers its
roots with the arena, and a collection evacuates every registered one, so
a reduction nested in another -- a probe, an interpreter jet's object run
-- may collect without invalidating the outer one's indices.

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
run in `copy` mode and inside any fueled run. The node cap is not
count-exact: a fire builds its residual's closed subterms afresh where
stepping shares them, so a jetted run can hold more nodes than the
unjetted one. A copy-mode fire that cannot have its nodes steps instead,
so a cap stepping fits does not stop a jetted run early
(`a_fire_short_of_nodes_steps`); the retained results of earlier fires
can still reach the cap at another count. The conformance suite runs
them on and off and asserts equal counts, a stronger check than equal
values. Body-instantiating jets and native-code jets change counts: they
are off in `copy` mode, and a run using them reports
`(contractions, jet calls)` as two numbers.

**Built in stage 4** (`src/jets.c`, `src/reduce.c`), with these rules the
plan left open:

- **Arity by running, not by the compiler.** The genericity argument
  holds for any `k`, so `k` is the least in 1 to 32 whose atom run halts
  with an atom at the head; a root with none, or a residual of cost 0, is
  not a jet. The registration bound is 10⁶ contractions. The cap was 8
  until Joy's words, constructors of a 12-way sum, needed 13 (§6.8).
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

### 6.7 The census: choosing jets by running

**A jet is worth what it absorbs on real runs, so Avon ranks candidates by
running the workloads.** SKIjack's static census (`RUNTIME-DESIGN.md` §8)
counts where a subterm occurs; `avon census` counts how often a program
calls it and how many contractions each call would absorb.

    avon census [--select=N] [--top=N] [--min-atoms=N] [--all] [--names=FILE]... MANIFEST...

It runs every manifest target in `copy` mode, jets off, three times, and
checks each count against the manifest:

1. **Count.** Every contraction puts a term in function position (the `x`
   of `S x y z`, `K x y`, `I x`), and a run starts with the loaded term
   there. The census fingerprints each left-spine prefix of that term,
   the nodes a jet could wrap, and counts the call with the arguments
   present. Only a node of the loaded term itself counts: the matcher
   wraps loaded nodes, never a copy the run builds, however alike. A
   census run never collects, so node identity holds through it. (The
   first census matched loaded code by fingerprint, and so counted
   structural copies too, and let one run's code count in the next; the
   order of the manifests then changed the report.)
2. **Capture.** The `--select` most-called prefixes of at least
   `--min-atoms` leaves are copied into the census's own arena.
3. **Measure.** Each captured term is registered as a residual jet (§6.5),
   which gives its arity and cost. A call with at least that many
   arguments is a fire and absorbs the next `cost` contractions; a call
   inside that window belongs to the fire, so recursion does not count
   twice.

**One call reaches a supercombinator's layers in turn.** `step`'s 55
prefixes are each called 589 times. The report folds each row into the
best-ranked row that is called exactly as often and is a subterm of it,
or contains it; ties go to the larger term. Equal counts stand in for
shared calls, so two unrelated rows with equal counts can fold together:
the report's grouping, never its measurements. `--names` files (`kind\tname\thash`) name a
row by §5's hash, and every name a file gives is shown; an unnamed head
borrows its first named layer's name as `~name`. `--all` lists the layers
under their head, and rows with no residual arity.
`jets/birds_names.tsv` names the birds in every encoding (§6.8).

**Results, 2026-09-28.** SKIjack's corpus (45 runs, 1,730,432
contractions) and SKIlark's workloads (41 runs, 928,398: phase 1's runs,
and phase 2's eight programs interpreted and compiled, fuelled and not).
The names are from `jets/birds_names.tsv` and both corpora's
`dictionary_names.tsv`, one of each term's names shown:

| # | saved | % | fires | ar | cost | atoms | name | as λ |
|---|---:|---:|---:|---:|---:|---:|---|---|
| 1 | 216,365 | 8.1 | 43,273 | 4 | 5 | 5 | -- | `λabcd. a b c` |
| 2 | 188,005 | 7.1 | 9,895 | 4 | 19 | 22 | Cons | `λabcd. d a b` |
| 3 | 166,656 | 6.3 | 23,808 | 3 | 7 | 8 | -- | `λabc. c a (b c)` |
| 4 | 161,770 | 6.1 | 11,555 | 3 | 14 | 17 | pair | `λabc. c a b` |
| 5 | 147,600 | 5.6 | 29,520 | 5 | 5 | 5 | -- | `λabcde. a b c e (d e)` |
| 6 | 147,312 | 5.5 | 36,828 | 2 | 4 | 5 | T | `λab. b a` |
| 7 | 141,088 | 5.3 | 8,818 | 6 | 16 | 17 | -- | `λabcdef. f (a b d)` |
| 8 | 138,770 | 5.2 | 27,754 | 3 | 5 | 5 | -- | `λabc. b (a b c)` |
| 9 | 122,530 | 4.6 | 12,253 | 4 | 10 | 11 | -- | `λabcd. d c (a b c d)` |
| 10 | 111,321 | 4.2 | 589 | 4 | 189 | 2,428 | step | SKIlark's interpreter step |
| 11 | 110,519 | 4.2 | 3,811 | 6 | 29 | 32 | App | `λabcdef. f a b` |
| 12 | 104,510 | 3.9 | 20,902 | 2 | 5 | 9 | L | `λab. a (b b)` |
| 22 | 80,402 | 3.0 | 11,486 | 3 | 7 | 8 | Suc | `λabc. c a` |

Each row's saving is what that jet would absorb alone; rows overlap and
do not add. The run takes a quarter of a second per corpus.

**Three kinds of term lead, and the programs' own functions are the
fewest.**

- *Scott constructors:* Cons, pair, App, Suc, T. Each takes its fields,
  then one continuation per constructor, and applies one continuation to
  the fields. Every named row in the top 12 except `step` and `L` is one.
- *Combinators under binders:* rows 1, 5 and 8 are `B (B K)`, `B (B S)`
  and `S B`, the last Church's successor. Rows 3, 7 and 9 are
  continuation plumbing of the same shape. They are what bracket
  abstraction emits for a combinator used under *n* binders. The static
  census found them by occurrence; the dynamic census finds they are
  also where the time goes.
- *Named supercombinators with large bodies:* `step` absorbs 189
  contractions a call but is called 589 times; `eqNP`, the `r`/`u` runs
  and `sumto` rank lower still. Of the combined top 30, 9 rows carry a
  dictionary name.

**Smullyan's birds are candidates by construction.** A compiler to SKI
emits them, so they recur across programs. Under aviary's encodings
alone the census finds 14 of the 50 birds called, at any size
(`--min-atoms=1 --all`, both corpora); §6.8's names add a fifteenth, K,
present only in Curry's η-free form `S (K K) I` and called 266 times:

| bird | term | saved | % | fires |
|---|---|---:|---:|---:|
| V (vireo; `pair`) | `S (S (K S) (S (K K) (S (K S) (S (K (S I)) K)))) (K K)` | 161,770 | 6.1 | 11,555 |
| T (thrush) | `S (K (S I)) K` | 147,312 | 5.5 | 36,828 |
| O (owl) | `S I` | 131,174 | 4.9 | 65,587 |
| B (bluebird) | `S (K S) K` | 124,712 | 4.7 | 31,178 |
| L (lark) | `S (S (K S) K) (K (S I I))` | 104,510 | 3.9 | 20,902 |
| M (mockingbird) | `S I I` | 45,376 | 1.7 | 22,688 |
| D (dove) | `S (K (S (K S))) (S (K K))` | 35,976 | 1.4 | 4,497 |
| B1 (blackbird) | `S (K S) (S (K K) (S (K S) K))` | 34,240 | 1.3 | 3,424 |
| Y | `S (K (S I I)) (S (S (K S) K) (K (S I I)))` | 20,682 | 0.8 | 2,298 |

KM, `K (S I I)`, would absorb 62,706 (2.4%) alone, but it is L's layer,
called exactly as often, and L's jet absorbs it; E, C, B2 and Ki follow
below 0.4%. The default `--min-atoms=5`
hides B, O and M, and O alone would absorb 4.9%; a bird list therefore
seeds the jet set directly, beside the ranked candidates, whatever its
size. A bird matches only in aviary's encoding: a compiler that emits
another term for C or W is missed, and a bird dictionary should list each
encoding a compiler in use produces.

**What this means for the jet set.** Two tiers, in order:

1. Constructors are a family, not a list: a constructor jet is fixed by
   the constructor's field count, its index and the type's constructor
   count. One parametric jet keyed on that triple covers every Scott
   constructor the compiler emits, named or not; rows 2, 4, 6, 11 and 23
   are five instances. §6.8 builds it.
2. The small combinators are Turner's case for an extended basis
   (`B`, `C`, `S'`, `B'`, `C'`): four 5-atom terms would each absorb 5
   to 8 per cent of the contractions. As residual jets they keep counts
   (§6.5). As primitives in the compiler's output they would change the
   counts, which §1.1 holds fixed for the artifact's workloads.

**Limits.** The census sees copy-mode calls on these two corpora only. A
row's saving assumes that jet alone; jetting the leaders together absorbs
less than their sum, and the combined figure is not yet measured.
Families fold only rows with equal call counts, so a layer also called
from elsewhere stays a row of its own. The first census stopped arity by
running at 8, so Joy's words, constructors of a 12-way sum, appeared only
under `--all`, each called 11 to 147 times; §6.8 raised the cap. A small
corpus under-ranks what it happens not to call, which is why §6.8 jets
Joy's word list whatever its rank.

**The profile: which code a share-mode run executes.** The census runs
in copy mode without collecting, which a program that must share -- the
SKIjack-0 front end (§20.3), 2.2 billion contractions -- cannot afford.
`avon reduce --profile=NAMES` (share mode) charges each contraction
instead:

- At load, every application node of the term belongs to the innermost
  subterm whose §5 hash the names file lists (`kind TAB name TAB hash`,
  as for `census --names`). Leaves are one node per atom, shared by every
  term, and belong to no one.
- A contraction is charged to the first loaded node among its
  combinator's partial applications: `S f` then `S f g`, `K x`, the redex
  `I x`. A loaded node the run rewrites in place holds the run's work
  from then on and leaves the loaded term. When the run built all of
  them -- a combinator passed as a value, a Scott boolean a case chose --
  the contraction goes to a "built at run time" row for its combinator.
- Ownership follows the nodes through collections. The profile changes
  no count and no result (`tests/test_profile.c`).

The profile is self time: a row counts the contractions its own code
runs, not its callees'. A term too small to be distinctive (`K K` is a
dozen case branches) would take code from the equation it is written in,
so skijack's `run0 --profile` names only terms of six atoms or more,
labels each lifted lambda and recursion body by its equation, and totals
by equation.

**Results, 2026-09-29: the front end compiling itself** (2,176,424,461
contractions, the renderer that writes the result out included):

| row | share |
|---|---:|
| name comparison: `eqCode`, `eqName`, `eqBit`, `andB`, `notB` | 39.5% |
| built at run time: K, S, I | 32.2% |
| the renderer, `rTm` (the harness, not the front end) | 13.8% |
| everything else, no row above 2.7% | 14.5% |

Comparison is the front end's cost, and the run-time rows are mostly its
consequence: a comparison's result is a Scott boolean or bit, which the
case that reads it applies as a combinator the run built. A second run
splits comparison by call site. Each site gets its own copy of the
comparison chain, made distinct by a constant that K discards, so every
copy costs the same per call. The copies add one contraction per bit
compared, 82.7 million, and the shares are of that run's 2,259,156,268:

| call site | share |
|---|---:|
| dependencies: is each equation free in each body (`eqDeps`) | 10.3% |
| grouping: mutual reachability (`grp`) | 6.3% |
| the memo of finished terms (`findMe`) | 4.7% |
| a dependency list by name (`depsOf`) | 4.7% |
| reachability (`closure`) | 3.2% |
| name resolution (`resolve`) | 2.7% |
| constructor and type tables | 1.7% |
| the rule table, duplicate names | 2.2% |

**What this means.** The recursion analysis -- dependencies, grouping,
the dependency lists and reachability, 24.5% -- is quadratic in the
equations: every equation's name is
tested against every body, and every pair's reachability is compared by
list membership. One pass collecting each body's free names, and
Tarjan's strongly connected components over them, make it linear in the
program. The memo and rule table are linear scans a search tree keyed by
name would make logarithmic. These are changes to the program, not the
runtime. A jet on name equality would take what remains, and it is the
one candidate the profile names; it should wait until the algorithms
stop calling it quadratically often.

**After, 2026-09-29.** The front end now collects each body's free names
once, finds its groups as Tarjan's components, and keeps its rules, memo,
names and constructors in search trees ordered by name. The fixed point
takes 1,262,327,332 contractions, 42% fewer, though the source grew from
375 names to 433; without the renderer, whose output grew with it, the
front end's own work fell from about 1.88 billion to 0.85 billion. Name
comparison fell from 39.5% of the run to 11.4%. What the profile
shows now:

| row | share |
|---|---:|
| the renderer, `rTm` | 32.7% |
| built at run time: I, K, S | 34.4% |
| comparing names: `cmpCode`, `eqCode`, `cmpBit`, `cmpName`, `eqName` | 11.4% |
| everything else, no row above 5.2% | 21.5% |

The run-time rows are now the most of the front end: Scott dispatch on
the values its cases read.

**Jets, measured, 2026-09-29.** On the self-compile above (16.6 seconds
unjetted), with output checked byte for byte: constructor jets (§6.8,
`--ctors`) fire 232 million times and take 24.0 seconds, since a fire
builds its residual in fresh nodes where share mode would have contracted
a few in place; residual jets for all 747 of the front end's rules of
eight atoms or more had not finished after 13.5 minutes. The measurement
also found the constructor scan quadratic -- it sized every subterm with
its own walk -- which ran 20 minutes on this term before one pass
replaced it. Dispatch on a two-constructor value is one or two
contractions, which no jet beats; the way to fewer is fewer dispatches.

**Which jets eat which, 2026-09-29.** The loader wraps every subterm
whose §5 hash is a jet's, nested ones too, and the reducer fires the
first jet node it meets walking down the spine if the arguments cover
its arity, else enters the term, where the inner jets meet theirs. So a
fire can take what an inner jet would have: *eat* it. `avon jetstat`
measures this: per jet, its fires and the contractions they absorb,
together with every candidate and, with `--alone`, registered by itself;
its misses (reached with too few arguments) and share-mode demotions; and
each fire's origin -- its jet node from the program as loaded, from an
instance of another jet's residual (after that jet fired), or from
another jet's term (after it missed). `src/jetstats.c` fixes a node's
origin where the node is made and follows it through collections
(`tests/test_jetstats.c`, hand-counted in both modes). The candidates are
`census --top=40 --emit`, 201 rows with their layers, and the 153 bird
encodings; `--halting` leaves out the two runs the fuel stops, 800,000
of the 2.66 million contractions, whose counts measure the budget.

    avon census --top=40 --emit=census40.tsv MANIFEST...
    avon jetstat [--share] --halting --alone --jets=census40.tsv \
        --jets=jets/birds.tsv --names=... MANIFEST...

| 84 halting runs | copy | share |
|---|---:|---:|
| contractions, no jets | 1,858,830 | 1,169,837 |
| absorbed by 348 jets together | 1,313,452 | 1,228,237 |
| fires | 109,793 | 90,848 |
| stepped, with jets | 545,378 | 202,448 |
| each alone, summed | 11,329,207 | 10,886,105 |

- **Eating is the rule.** The jets absorb 88% less together than their
  alone figures summed. Small patterns lose most: `S (K (S (K K)))` absorbs
  216,345 alone and 28,250 together, T 147,292 and 6,136, O 127,578 and
  10,694, Cons 188,005 and 39,235. Two layers of 810 and 566 atoms absorb
  45,353 each alone and nothing together: the head they belong to fires.
- **Nested fires come from residuals.** An outer jet's residual carries
  the inner jets its body calls, and they fire next: Y's residual fires L
  14,792 times, L's fires KM 16,567. No fire in either mode came from a
  term entered after a miss, and the corpora miss 61 times in all.
- **Share mode can gain fires.** L fires 9,899 times together and 3,916
  alone, Y 1,058 and 453: an instance builds afresh what sharing built
  once, the fixpoint's unrolling here. The corpora still come out ahead:
  202,448 contractions and 90,848 fires, against 1,169,837 contractions.

**The front end compiling itself, with jets** (share mode, output
identical in every case; work is contractions stepped plus fires; user
time best of five, interleaved, on a loaded machine):

| jets | work | time |
|---|---:|---:|
| none | 306,991,371 | 5.31 s |
| birds | 271,732,988 (−11%) | 5.31 s |
| constructors (`--ctors`) | 228,890,634 (−25%) | 5.12 s |
| census and birds | 317,361,509 (+3%) | 7.58 s |
| its own rules, 5 to 64 atoms | 353,526,862 (+15%) | 7.20 s |
| all of these | 251,033,829 (−18%) | 7.41 s |

Its own rules neither miss nor demote; they lose by instantiation, which
copies what sharing would have reduced once, and a fire costs several
contractions' time. The 587 rules over 64 atoms never miss and demote four
times in the first 30 million contractions: the slowness of the first
all-rules run was the fires, not the demotions. Only the constructor jets pay, barely. For this
program the jets that work are the ones that do not copy: the case for a
native extended basis over residual instances.

**Interning and reading, 2026-09-29.** Two changes to that end. The front
end interns each identifier to a binary number after lexing and keys its
tables by the number's bits, so a lookup is a dispatch per bit and never
a comparison of names: the fixed point fell to 740,558,347 contractions
for 492 names. And `avon front0` (§20.3) reads the result by probing
instead of rendering it as a tree of atoms for a printer, which took
another 58%: 306,991,371 contractions, eight seconds, against the first
version's 2,176,424,461 and 40.

### 6.8 Constructor jets and the jet dictionaries

**Avon recognizes a Scott constructor by running it, and jets every one
in loaded code, dictionary or not.** A constructor with `f` fields, of a
type with `n` constructors, takes its fields and then one continuation
per constructor, and applies continuation `i` to the fields:
`C a₁ … a_f k₀ … k_(n-1) = k_i a₁ … a_f`. The triple `(f, i, n)` is its
shape: K is `(0, 0, 2)`, K I `(0, 1, 2)`, T `(1, 0, 1)`, V `(2, 0, 1)`,
Suc `(1, 1, 2)`.

- **Classification rides on the residual.** Registration already runs a
  term on fresh atoms `X₀ … X_(k-1)` for its arity (§6.5). The residual is
  a constructor's when its normal form is `X_h X₀ … X_(f-1)` with
  `h ≥ f`: then `f` fields, `k − f` constructors, index `h − f`. The
  normalization is bounded at 4,096 contractions, since Y's residual has
  no normal form. Every jet carries its shape (`av_jet.ctor`), and the
  census names an unnamed constructor row by it (`ctor f/i/n`).
- **Exact up to weak equality.** An accepted shape gives
  `C a⃗ k⃗ =_w k_i a⃗` for all arguments, since weak reduction commutes
  with substitution; and every C with that equation has least arity
  `f + n`, so the least-k run finds it. Missed: a constructor only up to
  η (an η-expanded field, `λa k. k (λz. a z)`), one whose fields take
  more than 4,096 contractions to normalize, and one past 32 arguments.
  A shape feeds the scan's filter and the census's label only; firing is
  the residual, so a wrong shape changes which jets exist, never counts
  or values. I, `S K` and Church false satisfy the equation: they are
  constructors by it, whatever they were written as.
- **The fire is still the residual.** A constructor jet cannot build
  `k_i a₁ … a_f` directly: Suc's residual is `X₂ (K X₀ X₂)`, not
  `X₂ X₀`, and the pending `K` costs a contraction later or never. Only
  the residual keeps `copy` counts, so the parametric part is recognition
  -- one rule for every encoding -- not a new fire.
- **The scan.** `av_jets_ctors` registers each distinct subterm of the
  loaded term, from 2 to 64 atoms, that classifies as a constructor
  (`avon reduce --ctors[=N]`). It finds 46 to 86 constructors in a
  SKIlark program, 15 in T2, and the whole run with the scan stays near
  10 ms. Each candidate is run once, its shape and residual derived
  together.
- **The arity cap is 32**, up from 8: Joy's `word` has 12 constructors,
  so `Lit` and `Quote` take 13 arguments.

**Two dictionaries sit beside the corpus's**, generated by scripts in
`jets/` and loaded with `--jets=` (repeatable, `--jet-floor=2`):

- `jets/birds.tsv`: Smullyan's birds, 50 of them in 197 encodings and 153
  distinct terms (`jets/birds.py`). A jet matches one encoding, so each
  bird is listed as aviary abstracts it with and without η, in strict
  S/K, as Rathman's chart expands it and as combinatorylogic.com's
  composites expand; every encoding is checked by reduction against the
  bird's rule. `birds_names.tsv` names each by family.
- `jets/joy.tsv`: Joy's word list from every SKIlark form, 35 terms
  (`jets/joy.py`): the 12 word constructors, their compiled bodies
  `wDup` … `wAdd`, the primitives `add`, `mul`, `cat`, `wordOf`, and the
  derived words `over`, `nip`, `tuck`, `rot`, `sip`, `kComb`, `yComb`.
  They are jetted whatever the census says, because eight programs are
  too few to rank them.

**Measured** (`tests/test_workloads.c`): every run of SKIjack's corpus
and SKIlark's workloads, `copy` mode, every fire checked against the
unjetted run, gives the manifest's count. The share of contractions the
fires absorb:

| jets | SKIjack (1,730,432) | SKIlark (928,398) |
|---|---:|---:|
| birds | 18.8% | 24.9% |
| Joy's words | 0.0% | 4.1% |
| constructors found | 21.5% | 24.6% |
| constructors and birds | 30.8% | 36.9% |
| all three | 30.8% | 37.5% |

Constructors and birds overlap -- V, T, K and K I are both -- and
together absorb about a third of the work. Joy's words add 0.6 points on
this corpus. The absorption counts contractions a fire replaces; each
fire still builds its residual, so the wall-clock gain is smaller.

### 6.9 Supercombinator templates: the compiler hands over its functions

**Bracket abstraction erases the program's functions, and the compiler
still has them.** Every SKIjack rule with formals -- equation, recursion
body, group part, lifted lambda, constructor, prelude rule -- is also
written as a template: its formals and open body, keyed by the §5 hash of
the SKI term it compiles to (skijack's `templates.py`, `templates.tsv`
and `template_terms.tsv`). Where that term meets its arguments at the
head in `share` mode, Avon instantiates the body over them in one step,
instead of running the abstraction's S/K plumbing (`src/tmpl.c`,
`avon reduce|front0 --templates=DIR`). It is SKA's function recovery
(Afonin's "Nock Compilation", USTJ 3.2), with the answer supplied by the
compiler that knew it.

**Pure SKI is untouched.** SKIjack emits the same terms and export files
byte for byte; the templates are a separate file. Avon without
`--templates`, or in `copy` mode, which refuses it, runs exactly as
before, and `copy` counts stay the paper's (§1.1).

**Nothing is trusted, not even the hash.**

- *A template proves itself.* Avon abstracts its body over its formals,
  the last first, and keeps it only if the result is its key; a body that
  does not is refused and the term runs as SKI.
- *Identity is structural.* Loading builds every closed term -- the
  referenced terms, each checked against its hash, the globals, the
  abstracted keys -- in one hash-consed table, so equal trees are one
  node. After `av_jets_match`, each loaded jet node for a template is
  interned in the same table and kept only if it is the template's term;
  the hash only proposes. Wrapping a global's inner keys is node identity
  too.
- *The instance is weak reduction.* The body over the arguments is a weak
  reduct of the key applied to them (lean-ski's `absN_beta_close`), so
  the value and every normal form are the unjetted ones.

**What a fire does.** It pops the key's arity of arguments, writes the
body's open part -- its maximal closed subterms are globals, built once
per arena and rooted -- in children-first order, points the redex root at
it, and charges one step. The count is `share`'s own, reported with the
instantiations among it. A miss -- the key reached with fewer arguments,
as a partial application is -- enters the key's term without demoting the
node, so the node fires on its next full application; a node whose term
is the dashboard's keeps §6.5's rule. Left out, as lean-ski leaves them:
rules without formals, open bodies, η-templates, and keys that are a
bare S, K or I.

**One object with §18.1's proof jets.** A template is lean-ski's
`(formals, open body)`: the same exclusions, globals as maximal closed
subterms leaves included, cells in `ibuild` order. The plan for the
witness: lean-ski's `jets emit` takes skijack's templates as its template
source, recomputes roots and globals, licenses the roots with `rootOKB`,
and emits the jet file Avon's witness already reads (§18.1). Share mode's
globals are per-arena nodes; the witness's are heap addresses, which
lean-ski resolves itself.

**Results, 2026-09-29.** The front end compiling itself, with its own
993 templates (641 kept; 352 are duplicates, η-templates or bare-leaf
keys; none refused, none unbound):

| | contractions | of them instantiations | user time, best of 5 |
|---|---:|---:|---:|
| SKI, share mode | 306,991,371 | -- | 4.38 s |
| with templates | 21,238,890 | 18,930,884 | 0.97 s |

The output is the same, every name's hash. Loading and checking the
templates -- 6 MB of printed terms, parsed, hash-consed and abstracted --
is 0.39 s of the 0.97; the compile itself is 7.5× faster, and a compact
template form would take most of the rest. The corpus's 43 halting runs in
`share` mode reach the same normal forms in 63,774 steps, 36,616 of them
instantiations, against 640,853. `make front0-check` runs the edges, a
thousand random programs and the fixed point both ways.

What is left of the self-compile is 18.9 million instantiations, each
writing a template's open part in full, and 2.3 million S, K and I
contractions outside any template, not yet profiled. The instantiations
are the larger part, and what would shrink them is strictness: an
argument a body forces evaluated where it is needed, not written as a
cell (SKA's data requirements).

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
  residual jets as the host has them (§6.5; `--no-jets` means none);
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

**Built in stage 5** (`src/interp.c`), with these rules:

- **Which interpreters.** skijack's `export.py` writes `interpreters.tsv`:
  each generated interpreter core, keyed by its loop term's hash, with its
  object, result and answer types' constructors and what each non-S/K/I
  leaf's arm does -- an error outcome, divergence, or the scry arm. The
  exporter decides that by running each arm on marker atoms, never by
  name, and leaves out a core with a hand-written walker, loop or S/K/I
  arm unless it compiles to the generated one. The corpus gives five:
  `whnfF`, `wf5Abs`, `wf5Omg`, `wfQ`, `wfN`.
- **What a fire does.** It reads the fuel, decodes the datum to a live
  object term, matches residual jets in it, and reduces it in copy mode
  with the fuel as `max_steps`. That is the generated loop attempt for
  attempt: an iteration per unit, an S, K or I redex contracted, a
  combinator short of arguments the value, and any other leaf inert until
  its arm runs. An error arm returns its outcome; a scry arm spends one
  step, asks the resolver, and splices in a hit, returns the miss outcome,
  or blocks with the path; a diverging arm makes the jet decline, and the
  unjetted interpreter diverges as it would. The outcome is encoded with
  the program's own constructors.
- **Reading by structure first.** A datum node that is one of the object
  type's constructor terms, or its application constructor over two
  fields, decodes at once; so does a fuel numeral in an encoding the
  export names. Anything else is probed, as `run.decode` probes. The
  runtime may recognize structure (§3 of `RUNTIME-DESIGN.md`), and a node
  that is a constructor applied to its fields behaves as one.
- **Nested reductions.** A fire's object run, and the probes and resolver
  runs inside it, are reductions nested in the one that fired. Each
  reduction registers its roots with the arena, and a collection
  evacuates them all, so a nested one may collect. A root may hold
  `AV_NONE` -- a result slot rooted before it is filled -- and a
  collection leaves it so; `test_interp` collects inside T2's fire.
- **Fuel.** Interpreter jets are off inside an object run -- its fuel is
  always bounded -- and residual jets follow the host's setting: they
  keep counts, and `--no-jets` means none anywhere. A
  fire charges every contraction it performs, object steps and probes
  together, and declines if that would pass the host's fuel, so the host
  cap still bounds real work. Interpreter jets change counts, so they are
  off by default (`--interp`).
- **The resolver** is the program's own term, reduced; §8's native lookup
  needs stage 6's fact store.

Measured: T2 falls from 504,930 host contractions to 342 -- the object
run, which is T0 exactly (340), and 2 that bring the outcome datum,
`Just` over the encoded value, to weak head normal form. With every datum
read by probing instead, T2 costs 30,088, almost all of it decoding the
quoted interpreter; the structural path removes that.

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
  the path datum's structure, when the resolver is one the fact store
  built (stage 6, below). The resolver term stays the specification,
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

**Built in stage 6** (`src/scry.c`, the scry arm of `src/interp.c`,
`avon scry`):

- **The fact store** (`av_facts`) keeps its terms in its own arena, which
  nothing reduces, so nothing in it moves. A fact is the key datum *as the
  blocked run left it* -- `run.py` appends `fields[0]`, not a normal form,
  and the next resolver compares against that very term, so the counts
  depend on it -- with the answer datum and the key's path, decoded and
  printed. Keys are unique by that print (`run.py`'s `known`); a second
  append of a key is refused. `av_facts_open` backs the store with a log:
  one record per fact, `fact <key SKIT> <answer SKIT>` in hex, written
  and synced before the fact is used (§19's order), replayed on open. A
  blocked field can hold probe markers, `@N`, in positions nothing reads;
  a container refuses `@` names, so the log writes a name starting with
  `@` or `~` with one more `~` and replay removes it.
- **The resolver** is built each round in the round's arena, exactly as
  `resolver_term` builds it: `[p] EQ5 p k₁ (hit a₁) (EQ5 p k₂ (hit a₂) (…
  notyet))`, with aviary's abstraction, η included (`av_abstract`). It is
  registered as a jet key that never fires, tagged with the number of
  facts it encodes.
- **The native lookup.** When the interpreter jet scries with a tagged
  resolver, it prints the path the way the store prints keys and looks it
  up among the facts the resolver encodes. The first use checks the
  lookup against the term, as §6.6 asks: each fact's key, encoded, must
  reduce under the resolver to a hit with that fact's answer, and a path
  longer than every key to not-yet. A resolver that fails is reduced as
  before, never looked up; the check's probes are not charged to the
  fire. A native lookup assumes `EQ5` is syntactic equality on
  encodings; the check is what admits that assumption per resolver.
- **The resume loop** (`av_ns_run`) is `run_with_namespace`: every round
  a fresh arena, the program rebuilt with the resolver over every fact
  learned, run from scratch in `copy` mode to weak head normal form and
  peeled. The block constructor is the result type's second one-field
  constructor and the timeout its last terminal, as `run.py` picks them.
  `@[]` deepens from `start`, doubling, to `cap`. The two properties §8
  wants visible are: STUCK is its own event, and every attempt's fuel,
  status and contraction count is reported, so a resumed run's second
  payment of fuel shows.
- **The export.** `skijack.export` writes `namespaces.tsv`: the twelve
  resume-loop runs `tests/test_scry.py` pins, each with its program's
  terms, its namespace, and `run_with_namespace`'s events and every
  level-1 attempt it made.

**Measured** (`tests/test_scry.c`, `avon scry`): all twelve runs replay
event for event -- one block then a value, a chain of two, a compound
path, a path told from its prefix, a wrong fact and an unresolvable path
STUCK, fuel exhaustion, the policy, its cap, and the round limit -- and
all 21 level-1 attempts give the reference host's fuel, status and count.
With interpreter jets and every fire checked, the events are the same,
and 9 scries are answered natively. A store reopened from its log
resolves the chain in one round, at the reference's 1,250 contractions
for its last round. With `EQ5` replaced by a comparison that is always
false, the check refuses the resolver once it holds a fact, and the run
is STUCK with jets on as off.

**Not yet native:** a literal namespace (`ns{…}`) compiles to the same
shape, but its facts are not the store's, so its resolver is reduced as a
term -- the character table's case (§11.1, stage 5). Exporting a literal
namespace's facts would let Avon build the same term, recognize it by its
hash, and tag it.

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

**Built in stage 7** (`src/kernel.c`, `src/pier.c`, `src/install.c`;
`avon boot | poke | peek | load`):

- **The door.** `av_axis` applies the ABI's selectors, `hd = S I (K K)`
  and `tl = S I (K (K I))`, down the bits of an axis, which is how the
  compiler compiles `n@k`; `av_pull` is `(n@k) k arg`. A poke's value is
  reduced to weak head normal form, and the kernel installed is `tl` of
  it, unreduced, the effects `hd` of it -- exactly the reference loop's
  (skijack `test_examples`). A kernel is recognized by probing, never by
  a name: a pair whose head is a pair whose tail is a pair.
- **Boot** applies a pill's term to the initial subject and reduces it;
  a kernel is installed, and a value that is not one is reported, as §9
  says. skijack's standard subject is not built yet (SPEC §5), so the
  default subject is `I` and `--subject` supplies another.
- **The pier** is §19's durability order: an event is cued, then
  appended to `events.log` and synced, then applied; a snapshot is
  written image first and sidecar last (§4.2's `av_snapshot_save`).
  Reopening loads the newest snapshot that verifies and replays the
  later records -- pokes, and `load`s, which log the new pill and
  subject. A record cut short by a crash is dropped; a poke that does
  not reach weak head normal form never applied, so it leaves the log
  when it fails, and a crash between the two leaves it last, where
  replay drops it. Snapshots are not pruned yet, and the directory is
  not synced after a rename.
- **Upgrade** pulls `load` from the new kernel with the installed
  kernel's state and installs the result, unreduced.

**Measured** (`tests/test_kernel.c`, against `tests/kernel/export.py`'s
record of the reference host): the events kernel's Tick, Poke 5, Tick
cost 61, 108 and 135 contractions and leave 1, 6 and 7 with the
reference's effects; peek answers 7 in 210; `load` puts the first
battery over poke 2's state, 6, and a Tick then costs 143 and leaves 7.
In `share` mode a Tick costs 61, 66, then 63 for every one of a thousand
events, through eleven collections. A pier crashed after three events,
with a torn fourth record, reopens from its snapshot at two to the same
kernel hash by hash; after a failed event, an upgrade to the install
kernel's battery and its `Run`, it reopens to the same kernel again.

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
| 9 | the persistent arena (§19.1) | the node array in a mapped image file; dirty tracking; a journaled commit per event; recovery; the pier on it | a kernel's arena reopens without reading its nodes, in time independent of its size; each commit writes the pages the event changed, not the arena; a crash at any point of a commit reopens to the state before it or after it, and the log replays the rest to the same kernel | 700 |

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

**Stage 5, done.** The interpreter jet (§7):

- **The corpus conforms with interpreter jets.** All 45 targets in both
  strategies, residual and interpreter jets on, every one of the 86
  interpreter fires checked against the unjetted interpreter by
  `--jet-check`: every status and every value is the manifest's
  (`tests/test_conformance.c`). That includes the `EXAMPLES.md` §4
  boundary -- fuel 0 and 1 time out, 2 and 5 give `RVal I` -- the T3
  table, where `wf5Omg`'s diverging arm declines and both runs pass the
  host cap, and every scry single run: the scry table's eleven rows,
  `scry-block`'s blocks with their paths, and the character table.
- **T2's cost falls to T0's.** 504,930 host contractions become 342: the
  object run, T0's 340, and 2 for the outcome (`tests/test_interp.c`).
  T1 falls from 91,556 to 109, T0 from 340 to 3. The scry programs barely
  move -- the character table's `apply` from 62,199 to 60,683 -- because
  their cost is the resolver term comparing paths, which a fire still
  reduces; that is the case for §8's native lookup.
- **Random object terms** for `whnfF`, `wf5Abs` and `wf5Omg`, at random
  fuel, with one datum node or numeral level in five disguised as `I x`
  so that probing is exercised too: the jet gives the unjetted
  interpreter's constructor and decoded payload in copy and share mode,
  and `wf5Omg`'s Err terms run out of host fuel both ways. 4,501 cases
  under ASan and UBSan.
- The jet declines, and the interpreter runs, when an arm diverges, when
  a datum or a numeral cannot be read, or when the fire would pass the
  host's fuel.
- lean-ski's jetted-witness check (`tests/jet_witness_check.sh`) and the
  witness check still pass, at lean-ski `0b2fbcf`.

**Stage 6, done.** Scry (§8, "Built in stage 6"):

- **The corpus's resume-loop runs replay round for round.** The twelve
  runs of `namespaces.tsv` (skijack's `test_scry.py`), including two
  STUCK, the `@[]` policy and its cap, and the round limit: every event,
  and every one of the 21 level-1 attempts at the reference host's fuel,
  status and contraction count (`tests/test_scry.c`, `avon scry`).
- **The native lookup** answers 9 of those runs' scries under the
  interpreter jet, every fire checked, with the same events; a resolver
  whose term disagrees with it is refused and reduced instead.
- **The fact store** is append-only, keyed as `run.py` keys it, and
  logged before use; a store reopened from its log resumes a run in one
  round.
- skijack's 863 tests pass with the export added; lean-ski's witness,
  jetted-witness and probe-witness checks still pass, at lean-ski
  `8821b40` (built from its commit, with another session's uncommitted
  work in the checkout: `SKI_AIR` names a built `ski-air`).

**Stage 7, done.** Boot (§9, "Built in stage 7"; §20.2):

- **A kernel survives pokes, answers a peek, and `load` moves a state
  onto a new battery**, count for count with the reference host's loop in
  `copy` mode: 61 / 108 / 135, peek 7 in 210, load 6 then 143
  (`tests/test_kernel.c`, `tests/kernel/export.py`).
- **A kernel installs code its compiler emitted and runs it**: `Run
  <double>` and `Run <triple>` take the state 1 to 2 to 6, with `UQ`
  reduced and with its jet; the jet's nine fires in `UQ <double> 7` are
  each checked against `UQ`'s reduction.
- **Per-poke cost in `share` mode stays flat**: 61, 66, then 63 for every
  Tick of a thousand, §9's measurement, through eleven collections.
- **A pier reloads from a snapshot to the same state**, after a crash and
  a torn record, after a failed event, and after an upgrade: the same
  kernel, hash for hash.
- Leak-free (`leaks`) across boot, poke with a snapshot, and peek.

**Stage 8, the compiler's core done; the front end open** (§20.3, "Built
in stage 8"):

- **The compiler term compiles its own source to the terms Python
  produced**, for the part of compilation that is bracket abstraction:
  all 87 distinct abstractions of compiling `abstract.ascii.ski`.
- **The corpus compiles in Avon to Python's terms, hash for hash**, again
  for abstraction: all 8,636 distinct abstractions of the 17 compilable
  corpus programs, by the term (`make selfhost-check`).
- **The compiler jet, licensed by differential**, agrees on every one,
  every fire checked; a term that does not abstract as aviary does is
  refused.
- **The compiler is a term in a pill**, a kernel answering `Abs` events.
- **The front end, for SKIjack-0, compiles its own source** (§20.3,
  "Built for SKIjack-0"): all 492 of its names, from source text, hash for
  hash (`make front0-check`). The full language's front end remains.

**Stage 9, done.** The persistent arena (§19.1, "Built in stage 9"):

- **A kernel's arena reopens without reading its nodes**: 32 MB in
  0.3 ms, against 160 ms from a snapshot.
- **Each commit writes the pages the event changed, not the arena**: a
  Tick in 1.5 to 6.8 KB, a thousand times over; after a collection, the
  live arena.
- **A crash at any of a commit's four points reopens to the state before
  it or after it**, and a pier's log replays the rest to the same kernel.
- **The image is the arena, byte for byte**, after in-place share-mode
  updates alone and after collections; the test fails if dirty tracking
  is disabled.
- `make check`, the witness, jetted-witness and probe-witness checks and
  the selfhost check pass; the CLI's pier on the arena runs the events
  kernel as the snapshot pier does, leak-free.

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
  §17.4 builds it: probe segments, one per constructor of the outcome.
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

### 17.4 Probe segments: the witness binds an output

**Avon writes the table that proves what a term halts to.** A jetted
witness proves `3 sumto` halts; a probe table proves it decodes to `[6]`.
`lean-ski` specifies it (`Air.AcceptsP`, `Ski/AirProbe.lean`), checks it
(`lake exe jets check-probe TABLE OUTCOME`, sound by
`Air.checkPA_decodes`) and proves it (`ski-air probe-prove`).

    avon witness --jet-table=JETS --plan=PLAN TERM

The plan comes from `lake exe jets plan OUTCOME`: one segment per
constructor of the outcome's probe tree, depth first, each
`base k ctor arity parent field`. `[6]` takes 11: the result's `RVal`,
the stack's `Push`, the item's `Num`, six `Suc`, `Zero`, and `Empty`.
The run, per segment (`av_witness_run_probe`, lean-ski's `run_probe`):

1. **A probe row**, the current state, with the pointer the segment
   probes: the loaded head for segment 0, else field `field` of segment
   `parent`'s end.
2. **The markers**: atoms `base … base+k−1`, a stack of them, a nil; the
   head becomes the probed pointer.
3. **A jetted run** to a halt, exactly as `--jet-table` runs, with every
   row but the halted one.
4. **The end**: the head must be the atom `ctor + base` over exactly
   `arity` fields and a nil. The fields are recorded for the segments
   that probe them. Any other end, for a plan from `jets plan` and a
   licensed jet table, means the term does not decode to the outcome,
   and Avon exits nonzero naming the segment and the marker it reached.

The plan reader takes only the shape `Air.planOf` gives: each segment's
markers follow the last's from 0, `ctor < k`, every segment after the
first reads a field of an earlier one, each field is read exactly once,
and the last segment has none. A plan with shifted or overlapping bases
is refused, though a run under it could reach its markers: `check-probe`
rebuilds the plan from the outcome and would reject that table.

The last state closes the table. After `av_witness_table`'s sections come
`starts` (each segment's probe row, then the padded table's last row) and
`fields` (per segment, its count and pointers); atom cells print as `X n`.

**What an accepted table proves, and for which term.** The theorem is
lean-ski's: `check-probe` runs `Air.checkPA`, and `Air.checkPA_decodes`
(axioms `propext` and `Quot.sound` only) gives `Decodes t o` for the term
`t` on the table's first line. Avon's exit status proves nothing; its
refusals are a convenience. `check-probe` certifies whatever term the
table names, so a caller binds that line to the corpus row. Since
lean-ski `7031be9` (issue #2), `ACCEPT` names the term -- `corpus row
NAME`, or a term outside the corpus -- and `check-probe --row NAME`
refuses a table whose term is not that row's (`NOT THE TERM OF NAME`)
before checking it; `jets check` takes `--row` the same way. Avon's
checks run both with `--row` and require `ACCEPT` to name the row;
`ski-air probe-verify` binds the row by name.

**Checked** (`make probe-witness-check`, `tests/probe_witness_check.sh`):
the 7 rows of lean-ski's corpus, a count the check pins, with outcomes
from their Joy programs -- `val 6` for `1 2 + dup +`, `3 [dup +] i` and
`3 sumto`, `val 1 2 1` for `1 2 over`, in both compiled forms. Every
table names its row's term, is byte-identical to `ski-air
probe-prove`'s, and is accepted by `check-probe`. Per row, three wrong
outcomes -- `err`, the value less one, and one whose plan has the right
outcome's length (`val 3 0`, `val 2 1 1`), so `check-probe` must read
the markers and not only count segments -- are refused by Avon as not
decoding and REJECTed by `check-probe`: 21 of 21. Four tables offered
as `3 sumto`'s are refused: another row's term spliced onto its body and
`compiled_up`'s own true table (issue #2's case) as not `sumto_us`'s
term; a start row moved and a field pointer moved as REJECT.
`jet-witness-check` likewise requires `jets check --row` to name each
row, and refuses each table offered as the next row's. `3 sumto` takes 4,144 rows and
1,045 instantiations, the count lean-ski reports. The `--jet-table`
output without a plan is unchanged, byte for byte, on every corpus row.

**Where Avon and ski-air differ.** Avon's row budget defaults to 2²¹
(`--rows`), ski-air's run to 2²⁰ rows, so Avon can write a table past
what `probe-prove` would; Avon refuses a jet table with a root outside
the loaded heap, which `rootsOKB` refuses anyway; and `--plan` runs
without `--jet-table` too, on the plain machine.

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

### 19.1 The persistent arena

**A kernel's arena is a file mapped into memory, and an event's commit
writes only what the event changed.** Stage 7's pier recovers by loading a
copied-out snapshot and replaying the log, so a reopen reads every node and
a snapshot rewrites every node. The persistent arena (PMA) removes both
costs, as Vere's loom and Nockchain's PMA do, and keeps the durability
order above.

- **The image.** A directory holds `nodes` -- a header page, then the node
  array, node `i` at `header + 8i` -- and `atoms`, the leaf names. The
  header carries the node count, the leaf count, the root, the events
  applied and a SHA-256 of the atoms, and a SHA-256 of itself. Indices are
  positions, so the image needs no relocation (§2).
- **The mapping.** The arena reserves address space for the most nodes it
  can hold and maps the image's node array at its base, copy-on-write
  (`MAP_PRIVATE`): opening reads the header and the leaf names and nothing
  else, and a page of nodes is read when it is first touched. Growth past
  the image maps anonymous pages in the reservation; the base never moves.
- **Dirty tracking.** Every in-place write of a node -- the share-mode
  update, path compression, a jet node -- goes through one helper that
  marks its 4 KiB chunk. Nodes allocated since the last commit are dirty
  by position; a collection rewrites the arena, and marks it all.
- **The commit** is a redo journal. The dirty chunks, the new header and
  the leaf names if they changed are written to `journal.tmp` with a
  SHA-256 over all of it, synced, and renamed to `journal`; then applied
  to the image and synced; then the journal is removed. A crash before the
  rename leaves the old image; after it, opening applies the journal
  again, which is idempotent. Only a commit advances the persisted node
  count and root, §19's first pitfall; and a collection happens in memory,
  so the image on disk is always a committed one, its second.
- **The pier on it.** An event is logged and synced, then applied, then
  committed with the kernel as root and the event count. Reopening
  recovers the image and replays only the log records after its event
  count.
- **Not persisted: the jet dashboard** (§19, "Jets"). A jet node carries a
  dashboard id, so an arena with jets is refused a commit; so, until jets
  are rebuilt at load, is a PMA kernel run with jets.
- **Trust.** The image is local state, not an interchange form: opening
  checks the header, the leaf names and the journal, not every node, which
  is what makes it cheap. `av_pma_verify` checks every node on demand, and
  a snapshot (§4.2), verified in full on load, stays the form to move a
  kernel between machines.

**Built in stage 9** (`src/pma.c`; the pier's `av_pier_new_pma`; `avon
boot --pma`), with these rules the design left open:

- **The header is one page**, the system's (16 KiB on Apple silicon), so
  the node array maps page-aligned; a commit writes only its 108 bytes of
  fields. The nodes file never shrinks after a collection: a private
  mapping must not end beneath pages it maps.
- **One process at a time.** Attaching or opening an image takes an
  exclusive lock on it, held until the arena is freed, before a journal
  is recovered; a second opener is refused.
- **Probe markers are leaves like any other** in an image: probing
  interns `@N` in the arena, and the image records it. A snapshot, the
  interchange form, still refuses a graph that reaches one.

**Measured** (`tests/test_pma.c`, Apple M4 Max):

- **It reopens to what it committed.** After four rounds of share-mode
  reduction over a committed root -- the first two with no collection,
  196,736 contractions rewriting committed nodes in place, the last two
  with collections -- the image equals the arena byte for byte after
  each commit, read from the file. With dirty marking disabled, that
  test fails.
- **An open reads nothing it need not.** A 4,000,000-node arena (32 MB)
  reopens in 0.3 ms; the same state loads from a snapshot in 160 ms.
- **A commit writes what changed.** The first commit of that arena
  carries 7,813 chunks; one node later, one chunk and 2,290 bytes. A
  pier on the arena commits a Tick of the events kernel in 1,498 to 6,839
  bytes from the eleventh event to the thousandth, except the one commit
  after a collection, which writes the live arena.
- **A crash at each of the four points of a commit** -- after the
  journal is written, after its rename, half way through applying it,
  after applying it -- in a forked process, reopens to the state before
  the commit at the first and after it at the other three, with no
  journal left; a pier crashed between an event's log record and its
  commit reopens with the event replayed and committed.
- **Refused:** a commit of an arena with jets, a second opener, a header
  that does not verify; a node pointing past the image fails
  `av_pma_verify`.

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

**Built in stage 7.** `av_install` reads the datum by probing (`S | K |
I | App`, in that order) and matches the live term's jets. A term is
admitted as the unquoter (`av_unquote_register`) only if, on sample
terms, its normal form applied to a datum Avon builds (Scott
constructors by bracket abstraction, `av_encode`) is the term; the
paper's 43-atom `UQ` is. With `install_jets` -- off by default, since
a fire's charge is its probes' contractions, not `UQ`'s -- `UQ d` at the
head is installed natively, and `--jet-check` compares a fire with
`UQ`'s own reduction by normal form. The install kernel
(`tests/kernel/install.ascii.ski`) takes `Run d`, `d` the compiler's
quotation of `double` or `triple`, and runs it on its state: its pokes
match the reference count for count, and with the jet `UQ <double> 7`
normalizes in 20,284 contractions against 118,461, nine fires, each
checked. The kernel is compiled without Stage B: a decoded term is
untyped, as a formula run with `.*` is.

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

**Built in stage 8, for the compiler's core** (`tests/selfhost/`,
`src/compiler.c`, `avon selfhost`). skijack compiles every equation by
bracket abstraction (aviary's `expand` abstracts each formal in turn),
so a compilation is a sequence of calls `[x] body → result`. The core is
that abstraction, written in SKIjack: `abs x t`, aviary's algorithm with
η, over encoded terms `tm = TS | TK | TI | TV nat | TA ap`, `ap = Ap tm
tm` (an application's fields have their own type, since a type with a
two-field self-constructor would be the program's object type). It is
one recursive equation, because skijack refused mutual recursion when it
was written.

- **The fixed point.** skijack compiling `abstract.ascii.ski` performs
  123 outermost abstractions, 87 distinct once variables are renamed;
  the term, run in Avon, gives every one of them, text and hash, in
  12,214,849 contractions.
- **The corpus.** Compiling the 17 corpus programs that compile performs
  19,301 abstractions, 8,636 distinct; the term gives every one, hash for
  hash, in 523,815,334 contractions, ten seconds. Each definition's term
  is the last abstraction of its chain, so every one is Python's.
- **The compiler jet** answers `abs x t` natively (`av_abstract`), its
  datum decoded by probing and its result encoded with the program's own
  constructors. It is admitted only if the term agrees with it on sample
  terms, and with `--jet-check=1` every fire is compared with the term's
  reduction: 8,636 of 8,636 and 87 of 87 agree.
- **The compiler in a pill.** The same source declares a kernel whose
  event `Abs x t` has the effect `Out ([vx] t)`; booted from its pill and
  poked with every call of its own compilation, it answers each with
  Python's abstraction, by the term and with the jet.

**Built for SKIjack-0: the front end** (skijack's `selfhost-front-end`
branch, `python/skijack/selfhost/`; `tests/front0_check.sh`). SKIjack-0
is the subset of SKIjack with types, equations, definitions, cases,
cells, picks and lambdas, and skijack's `docs/SKIJACK-0.md` specifies its
compilation term for term. The front end is a SKIjack-0 program: it
lexes, parses, desugars, lifts lambdas, ties recursion -- one fixpoint
per group of mutually recursive equations, which skijack's expander
learned on the same branch -- and abstracts with the core's `abs`. Python
compiles it to one term, `front`; Avon runs it in share mode on a
program's 7-bit character codes.

`avon front0 DIR SOURCE` (`src/front0.c`) builds that input in the arena,
each code's datum once, and reads the result by probing -- ROk, then each
name and term -- into a line per name, the name and its term's §5 hash,
computed bottom up with a memo of hashed nodes, so no term is rebuilt or
printed. The front end's work happens inside those probes, lazily, so
unlike av_peel's they collect: the reader registers as a reduction, and
the collector evacuates its stack of held nodes, its marker leaves, and
remaps its memo.

- **The fixed point from source text.** `front` applied to its own
  39,622-character source gives all 492 of its names their terms, hash
  for hash with Python's, in 306,991,371 contractions, eight seconds;
  with its supercombinator templates (§6.9), in 21,238,890, one second.
  The first version took 2,176,424,461 for 375 names; §6.7 follows the
  steps between.
- **Agreement.** It compiles a thousand random SKIjack-0 programs as
  skijack's specification does, and accepts or refuses 67 programs at
  the subset's edges (duplicate names, cycles, newlines before a closing
  bracket, shadowed recursion) as it does.
- **Sharing is required.** `front` passes its tables and environment to
  many callers; a reducer that copies recomputes each at every use, so
  the check runs in share mode, and the non-sharing reference reducer
  runs only the lexer (skijack's `tests/test_front0.py`).

The full language's front end -- cores, macros, signatures, quotation,
scries, namespace literals and the type checker -- still runs in Python.
Next comes the whole language's front end, checked on the corpus. §6.7
measured jets for this one: constructor jets and residual jets for its
own equations both make it slower in share mode, so what remains of its
cost is for the extended basis to try.

### 20.4 What else the analogy imports

Vere is more than a Nock interpreter. Its other duties map onto Avon as
follows, and each needs a decision before stage 7, not now.

| Vere | Avon |
|---|---|
| event log, snapshot, replay | §19's durability order: log first, then heap, then a checksummed sidecar; built as the pier (§9, stage 7) |
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
