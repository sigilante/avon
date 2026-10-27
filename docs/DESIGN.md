# Avon: the native runtime, planned

> **Status (2026-10-22).**
>
> - **Built:** stages 0 to 7 and 9 of §11. Stage 8 has the compiler's core, the SKIjack-0 front end, and the full language's front end through M4: every corpus program compiles in Avon to Python's terms. Its checkers, M5 (Stage A) and M6 (Stage B), remain (§11.1, §20.3).
> - **Beyond the stages:** share mode runs supercombinator templates, data jets, Y's one-step unfolding and Poseidon2 natively, and defers an instance's root (§6.9 to §6.13), all outside the proof. Jets under hiding are built (`ZK-JETS.md`). Frame traces and the defect count serve the pure-S paper's hider census (§22). The structural hash is `skijack-2`, 128 bits (§5), and a dashboard entry is its term, not its digest (§6.5).
> - **Open:** what the proofs do not yet cover, and the unbuilt stage work, are listed in §11.1, "Open". `WORKLIST.md` orders what is next.
>
> **How to read this note.** It began on 2026-09-16 as the build plan, before any code existed, and grew as the stages were built. §0 to §4 and §10 to §16 are the plan and its decisions; §11.1 is the record of what was built, with figures as measured at the time; §5 to §9 and §17 to §22 are the current design. `RUNTIME.md` is the user's reference, `ARCHITECTURE.md` the map of the source. Where this note and the compiler differ, the compiler (SKIjack's `python/skijack`) and its tests are authoritative. Paths that begin `avon/bench/` are in the [SKIjack repository](https://github.com/sigilante/SKIjack/tree/master/avon/bench), where this note was first written; `RUNTIME-DESIGN.md` and `SPEC.md` are SKIjack's too.
>
> **Revisions, 2026-09-27.**
>
> - §17 and §18 fit Avon to the proof system in lean-ski: a third strategy whose runs the circuit proves, and the licence a jet needs inside a proof.
> - §20 takes Vere's relation to Nock as the model: Avon's C never compiles, but Avon runs a compiler.
> - §6.5, §7 and §8 follow Vere's `+mock` jet: the interpreter jet is the level-1 interpreter and serves scry, and residual jets keep fuel exact inside it.
> - §9 and §20.1 fix the kernel as a door `[battery state]` pulled by axis, and the pill as one term.
> - §21 compares Vere and NockApp from their sources.
>
> **Terms.** A *jet* is native code that stands for a term; its *licence* is the argument that the jet agrees with the term, checked by differential (`--jet-check`) or carried into a proof (§6.4, §18). A *residual jet* leaves every copy-mode count exactly as the unjetted run has it (§6.5). The *dashboard* is the table of known jets. A *door* is a cell `[battery state]`: the battery is its code, arms pulled by axis, and the state its data. A *pill* is a term whose value, applied to a subject, is a *kernel*, a door; a *pier* is the directory that holds a kernel's event log and snapshots (§9). A *scry* is a read-only lookup by path, answered from a fact store (§8). The *reference host* is `aviary_kernel.reduce`, the Python reducer whose counts the papers publish.

*2026-09-16. The build plan for the C runtime named in `RUNTIME-DESIGN.md`
§3a. Its constraints come from three places: the reference host
(`aviary_kernel.reduce`, which is where the paper's counts come from), the
compiler (`python/skijack`, which is what produces the terms), and the
paper's measured targets. §1 reports a measurement that changes one of
`RUNTIME-DESIGN.md`'s stated acceptance criteria, and most of what follows
is downstream of it. When this was written, nothing was built and
`avon/` was empty; §11.1 records what has been built since.*

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
truncated to 32 hex digits, 128 bits, published with the version prefix
`skijack-2:`. Avon computes the same values, in one bottom-up pass, with a
vendored public-domain `sha256.c` (~200 lines, no dependency).

It is computed **at load time only** — once per dictionary entry and once
per candidate node in the loaded program — and never on the reduction hot
path. §6 is why that suffices.

**Built in stage 4** (`src/jets.c`): it matches skijack's string on all
286 rows of the corpus dictionary (`tests/test_jets.c`).

The hash is for **dispatch, not commitment**. Until 2026-10-21 it kept 16
digits, 64 bits (`skijack-1`), and 64 bits admit a collision after about
2³² work by anyone who picks both terms; it keeps 128 now (`skijack-2`,
SKIjack #18), past that reach. A collision is still harmless here, as every
dashboard hit is held to its term (§6.5), and would be fatal only where a
verifier trusted the hash. Nothing a proof
relies on is keyed by it: a proof binds terms by the circuit's own field
fingerprints (`lean-ski`'s `zk/`, with a proved collision bound), and a jet
inside a proof is licensed by recomputing the term it stands for (§18.1),
not by its hash.

## 6. Jets

### 6.1 What the key is

**The subterm, and nothing else.** The key is the Merkle hash of §5 over
that node's tree — leaf names and application structure — published with
the `skijack-2:` prefix. Not the name it was compiled from, not the type
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
  or above a size floor (default 8 atoms: 139 of 286), and wraps each
  jet's inner jets in its term and residual.
- **A match is tree identity, not a digest.** `av_jets_match` finds a
  candidate by the 128-bit digest. It wraps the node only if the node is
  the jet's term, tree for tree.
  - Before 2026-10-06 a digest alone sufficed, so a term built to
    collide in about 2^32 work ran as another (`AUDIT.md` item 8). An
    interpreter's dictionary rows are held to their hashes the same way.
  - Trees are compared by canonical ids. A leaf's id is its interned
    node; an application's is the pair of its children's ids. The table
    lasts a whole match, so the program and the jets' terms each cost
    their nodes once.
  - The first version, in #26, compared with a pair budget set by the
    jet's size. It refused a program whose copy of a term shared less
    than the jet's term: 92 templates on front1's own source. That made
    front1's fixed point 9.7% dearer, 88,316,487 contractions, and
    front0's 3.5% dearer, until the ids replaced it (2026-10-09).
- **An entry is its term, not its digest.** A template, a numeral
  operation, an interpreter's loop, an unquoter, a compiler or a
  resolver attaches to the dashboard through `jet_entry_for`, and a
  dictionary row through registration; both look the digest up first.
  - Before 2026-10-21 a hit was taken as the term's own entry, so a
    template whose key collided with a dictionary row's took that jet's
    arity, residual and fallback, and ran its occurrences as the other
    term (SKIjack review, Chevalier).
  - A hit now counts only if the entry's term is the offered one
    (`av_equal`, its budget the 10^8 distinct pairs the reducer's
    comparisons get, so a copy that shares less costs its nodes, not its
    unfolding). Another term under the digest is refused as a collision
    (`jet_collision`): the template is counted refused, the word
    operation runs as its term, and the other callers report it.
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

**Rerun, 2026-10-23: SKIlark on Church fuel.** SKIlark's kernel now
bounds a run with a Church numeral, the loop's body applied *n* times,
in place of a Scott numeral computed as it is consumed (SKIlark's
`PLAN.md` §3). Its workloads fall from 928,398 contractions to 333,013;
SKIjack's corpus is unchanged. Over both, 2,063,445 contractions, the
constructors lead: `Cons`/`Push` 188,005 (9.1%), `B (B K)` 167,890,
`pair` 161,770, `B (B S)` 139,050, then `step` with its wrapper at
121,923 (5.9%), called 589 times as before. What fell was the fuel's
arithmetic: `B (B K)` loses 9,695 fires, `T` 18,867, and SKIlark's
`Suc` 9,737 of its 10,153. The analysis and the bird table below read
the 2026-09-28 run.

**Rerun, 2026-10-23: SKIlark toward Joy in full.** SKIlark's kernel has
grown past Joy's basis to its arithmetic on signed integers, truth
values, `branch` and `ifte`: a 28-way `word` and a `step` of 11,461
atoms (SKIlark #6 and #7). Its workloads take 558,847 contractions, and
over both corpora, 2,289,279, `B (B S)` leads at 10.2%, then SKIlark's
`step` with its wrapper at 9.5%, 470 calls at 463 contractions each,
`Cons`/`Push` 8.5%, `B (B K)` 8.4% and `pair` 7.3%. A wider kernel makes
the interpreter's dispatch the costliest named term again.

**Rerun, 2026-10-23: SKIlark's lists.** SKIlark's quotations became
Joy's lists: words are symbols, a fourth kind of stack item, and
`uncons`, `null` and `small` join the kernel, while `succ`, `pred`,
`max`, `min`, `and`, `or` and `not` move out into derived words. The
`word` sum narrows to 24 constructors and `step` grows to 16,112 atoms
(SKIlark #8). Its workloads take 564,740 contractions, and over both
corpora, 2,295,172, `B (B S)` leads at 9.9%, then `Cons`/`Push` 8.5%,
SKIlark's `step` 8.4%, 486 calls at 399 contractions each, `B (B K)`
8.4% and `pair` 7.3%.

**Rerun, 2026-10-24: SKIlark's combinators, characters and strings.**
SKIlark's kernel gained the stack as data (`stack`, `unstack`), `Def`
for a derived word in a quotation, characters and strings (`Glyph`,
`Text`, `ord`, `chr`), and the reference implementation's comparison
and truth values; Joy's recursion combinators are derived (SKIlark #9
and #10). The `word` sum has 31 constructors and `step` 33,231 atoms.
Its workloads take 742,609 contractions, and over both corpora,
2,473,041, SKIlark's `step` leads at 13.2%, 502 calls at 648
contractions each, then `B (B S)` 12.5%, `B (B K)` 8.3%, `Cons`/`Push`
7.9% and `pair` 6.8%.

**Rerun, 2026-10-24: SKIlark's sidestep.** SKIlark's five literal
constructors became one, `Lit item`; its kernel gained Joy's `typeof`,
from which the type tests derive, sets of 0 to 63, and Joy's `not`, a
set's complement (SKIlark #11 to #13). The `word` sum has 29
constructors, under the cap, and `step` 45,016 atoms. Its workloads take
882,928 contractions, the interpreted runs 660,290 from 551,541 and the
compiled 132,952 from 101,382: `succ` and `pred` now tell a truth value
from an integer, and `sumto` counts down with `pred`. Over both corpora,
2,613,360,
SKIlark's `step` leads at 14.3%, 614 calls at 607 contractions each,
then `B (B S)` 13.4%, `B (B K)` 8.5%, `Cons`/`Push` 7.8% and `pair` 6.7%.

**Rerun, 2026-10-25: SKIlark's library words and numbers.** SKIlark
derived the reference's library words (stage 7, #17) and moved its
naturals onto skijack's numeral operations, each casing its numerals
first (#18). The `word` sum is unchanged and `step` is 57,842 atoms. Its
workloads take 941,408 contractions in copy mode, which runs the
operations as their terms: the interpreted runs 696,878, the compiled
154,844. Over both corpora, 2,671,840, SKIlark's `step` leads at 14.0%,
614 calls at 607 contractions each, then `B (B S)` 13.4%, `B (B K)`
8.5%, `Cons`/`Push` 7.7% and `pair` 6.5%. SKIlark then divided with
skijack 0.2.2's `natDiv` and `natRem` (#19): `step` is 57,570 atoms, and
the workloads, none of which divides, take the same contractions.
SKIlark's stage 8 (#21) gave `word` a thirtieth constructor, `Ext ext`,
which holds its further words, `size` and `at` so far, in a sum of their
own: `word`'s one-field constructors take 31 arguments, under the cap.
The workloads use neither word, so they pay only the wider `word`: 959,160
contractions, from 941,408, and `step` 614 calls at 632 each, from 607.

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
- `jets/joy.tsv`: Joy's word list from every SKIlark form, 74 terms
  (`jets/joy.py`): the word constructors, phase 1's 12 and the kernel's
  28 Joy words of a 30-way sum (`Dup` … `Do`, `Lit` of an item, `Add` …
  `Ifte`, `Uncons` … `Unstack`, `Def`, `Ord`, `Chr`, `Typeof`, `Not`),
  their compiled bodies `wDup` … `wIfte` and `wTypeof`, the primitives
  `add`, `mul`, `cat`, `wordOf`,
  and the
  derived words `over`, `nip`, `tuck`, `rot`, `sip`, `kComb`, `yComb`.
  They are jetted whatever the census says, because eight programs are
  too few to rank them.

**Measured** (`tests/test_workloads.c`): every run of SKIjack's corpus
and SKIlark's workloads, `copy` mode, every fire checked against the
unjetted run, gives the manifest's count. The share of contractions the
fires absorb:

| jets | SKIjack (1,730,432) | SKIlark (941,408) |
|---|---:|---:|
| birds | 18.8% | 15.9% |
| Joy's words | 0.0% | 7.7% |
| constructors found | 21.5% | 23.6% |
| constructors and birds | 30.8% | 31.3% |
| all three | 30.8% | 32.6% |

Constructors and birds overlap -- V, T, K and K I are both -- and
together absorb about a third of each corpus's work. Joy's words add 1.3
points on SKIlark's. On Joy's basis SKIlark's workloads were 928,398
contractions on the Scott fuel (24.9, 4.1, 24.6, 36.9, 37.5%) and
333,013 on Church fuel (22.1, 7.2, 29.7, 39.6, 40.0%); with Joy's
integers and truth values they were 558,847 (15.7, 9.6, 25.5, 32.4,
33.9%), with lists 564,740 (17.0, 8.7, 26.5, 34.2, 35.2%), and with
its combinators, characters and strings 742,609 (13.7, 8.6, 22.7, 29.0,
30.5%), and with its type tests and sets 882,928 (13.9, 8.2, 23.2, 29.5,
30.9%). The absorption counts contractions a fire replaces; each
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
are the larger part. Strictness was the expected lever, and measurement
says otherwise (`docs/BENCHMARK.md`, "What becomes of an instance's
cells"): of the cells instances write, 8 to 20% are argument thunks and
61 to 65% are spine, unwound at once; and 16 to 56% of instances case on
a formal that arrived already a value, a dispatch that could join the
instance.

### 6.10 Data jets: constructors dispatched, numerals held as numbers

**Data jets make a `case` and a numeral cheaper in share mode, and change
no answer.** With templates (§6.9), `--data` adds two: a constructor
meeting its continuations dispatches straight into the branch it selects,
and a numeral is held as a number, on which skijack's numeral operations
run natively. The program is still the pure SKI term: copy mode, the
witness, and a run without `--data` are what they were, and normal forms
are the unjetted ones byte for byte.

**A `case` was three steps; it is two.** Scott encoding makes a `case` an
application of the scrutinee to one continuation per constructor, and
skijack lifts each branch that binds fields into a rule over what it
captures and the fields. With templates, `case xs of Cons x r -> e` took
the function's own instantiation, the constructor's (`Cons x r n c` to `c
x r`), and the branch's. A constructor's template is recognized by its
body, a formal applied to the fields -- `v_h v0 .. v(m-1)`, the shape
`(m, h - m, k - m)` of §6.8 and lean-ski's `ctorO` -- and with every
argument it dispatches: the continuation its index selects, applied to the
fields, replaces the redex root, one step. When that continuation is a
template's key applied to exactly the arguments that, with the fields, it
takes, the branch is instantiated in the same step, *fused*: a `case` is
the function and the branch, as it is the Reduceron's function application
and case alternative. A nullary constructor never fuses: its continuation,
applied to nothing, is itself the redex, and must be updated where it
stands, since it may be shared.

**A word is a numeral held as a number, and every reader still sees the
numeral.** `W n`, for n >= 1, is a jet node flagged `AV_JET_WORD`: its id
field holds n and its term is `SUC (W (n-1))`, `W 0` being `K`, where SUC
is skijack's successor `S (K K) (S (K (S I)) K)`, the term every `Zero |
Suc t` type compiles to, whatever it is called. `av_view` sees through it
as through any jet node, so printing, the §5 hash, `jam`, snapshots and
the witness read the numeral itself; the predecessor is its term's right
child. A word meeting its two continuations dispatches with no allocation:
`W n z s` becomes `s (W (n-1))` in place. A word is a value but its term
is not in normal form -- `SUC x` is a redex -- so making a normal form,
or reporting a weak head normal form with a word at the head, reduces a
fresh copy of the term, as the unjetted run would. Copy mode runs the term.

**Words come from where a numeral is already whole; nothing is forced to
make one.** The loaded program's closed numerals become words in place
(`av_words_scan`, after binding); a template instruction applying SUC to
a numeral already held builds a word (`av_words_mark`); and the numeral
operations return words.

**The numeral operations are skijack's terms, pinned and checked by
running.** `natAdd`, `natSub` (truncated), `natMul`, `natIfEq` and
`natIfLe` join skijack's prelude when a program names one (skijack
`SPEC.md` §4).
- `words.tsv` lists each by the §5 hash of its term. Avon loads a row only
  if the term matches its hash.
- Avon admits a row only if its term is skijack's, node for node.
  `words.c` pins the five terms (2026-10-05, `AUDIT.md` item 7). A row
  under its own hash used to bring an operation of its own: an addition
  right on 0 to 6 and wrong past them passed the test below.
- The term must also agree with the native operation on all 36 pairs of
  the numerals 0 to 5, run in share mode on private copies.
- A row that fails any of these runs as its term.

Neither the pin nor the match on 36 pairs is a proof: each admitted operation
is native code the runtime trusts, as a Vere jet is, and its licence for
a proof is §18.2's word-level theorem, owed per operation. An operation
fires only when both numeral operands are words already, as the
Reduceron's primitive-redex speculation fires only on evaluated
operands; otherwise its node runs its term, kept for the next call. So an
operation forces nothing its term would not: `natAdd ⊥ 1` is a successor.
One that would build more than 2^20 nodes runs its term too, which builds
its result lazily. A word's value fits the 28 bits of a jet node's id
field, so a numeral past 2^28 - 1 stays SKI, and jet ids, sharing the
field, are capped at 2^28.

**What was not built.** The plan (2026-09-29) also made a constructor
value reduced on its own a node that keeps its dispatch, a DATA node. In
lazy share-mode reduction a constructor value is reduced without its
continuations only at the top of a run or while the normal form is
made, and both must report the SKI term, so a DATA node would be made
only to be undone; on the five Reduceron ports no constructor template
missed once. It was built, found idle, and taken out. Types of more than
32 constructors still dispatch as SKI: a template past 32 formals cannot
be checked with the 32 markers the hash-cons table has.

**Counts are reported apart; only time is the measure.** A dispatch, fused
or not, and a numeral operation are each one step of fuel, and are
reported beside the contractions (`data:` on stderr), never folded into
the instantiations. That a fused dispatch is one step and not two says
how Avon counts, not that it does less; the claim rests on user time.

**Results, 2026-09-29** (avon `f414272`, skijack
`8b34529`; user CPU, best of five, interleaved). The
front end compiling itself, all 492 names the same:

| | contractions | instantiations | dispatches (fused) | user time |
|---|---:|---:|---:|---:|
| templates | 21,238,890 | 18,930,884 | -- | 0.96 s |
| templates and data | 17,389,998 | 6,554,787 | 8,527,205 (3,848,892) | 0.92 s |

Of each time, about 0.39 s loads the templates. The five Reduceron ports
(`docs/BENCHMARK.md`), their integers now the prelude's operations: data
jets take 1.10 to 1.19 times less time than templates alone on the four
without arithmetic to speak of, and PermSort, whose comparisons run on
words, 2.12 times less. The corpus's 43 halting runs, to weak head normal
form: 43,348 steps with templates, 33,244 with data jets, 13,627 of them
dispatches. Every normal form is SKI's and every weak head normal form
templates' (`tests/test_data.c`, `make front0-check`).

**A case joined to its instance** (2026-10-02, `case_kind` and
`case_join` in `src/reduce.c`). A template whose body is one of its
formals applied to p operands is a case, found at load: the root is the
last instruction, and each application of its spine below the root is
used by its parent alone. When an instance of it meets that formal as a
value the next step would dispatch on -- a constructor with its fields and
p continuations, or, with two, a word or zero (`K`) -- the instance writes
the body's other applications but not its spine or root. The dispatch
then writes over the redex root what it would have written there after
the instance. So the graph is the same but for the spine, which no one
else could reach. The two steps are counted as two, and a join is made
only when the fuel covers both, so every count and every state a run can
stop in is what it was. It is made only when the free nodes cover both
writes without a collection; otherwise the instance runs as before.
`tests/test_data.c` holds runs with and without joins equal in every
count and state, at every fuel from 0 to 400 and through collections.
The results are in `docs/BENCHMARK.md`, "A case joined to its instance".

**Bit strings, 2026-10-28** (`src/words.c`, "Bit strings"; `bits_fire` in
`src/reduce.c`). skijack's own front end names everything by bit strings,
`Bn | Bz b | Bo b`, and keeps its stores in tries keyed by them. With
templates and data jets, front1 on front0's source took 50,728,634
contractions, and `--jet-stats`, now counting each template's fires and
each constructor's dispatches, put a third of them in that traffic: the
`Bz` and `Bo` dispatches 16%, `eqB` 6%, `idBits` 6%, the lookup shared by
`rvGet`, `cmGet`, `sHasB` and `ndGet` 4%, `eqId` 3%.

Three of those functions now run natively, as the numeral operations do.
- *Pinned.* A program's function is the operation only if its term is
  front1's, node for node: `eqB`, the lookup, and `eqId`, which compares two
  names `IdRaw n | Id b` by their bits, an IdRaw's being `Bn`. A term is
  found only where the template set holds it already, so a program without
  these functions loads as before. A function with formals, as `eqId` is,
  is a template, and the operation sits on the template's own jet.
- *Admitted by running.* The term runs first on every pair of bit strings
  of up to three bits, names with an IdRaw among them, and every such key
  in five tries; one whose normal form differs anywhere is refused.
- *Reading only values.* An operand is read only where it is a value
  already: a constructor template's node applied to exactly its fields,
  or `K` and `K I`. The walk takes the term's cases in its order. Where it
  meets a field not yet a value, the operation applied to what it has
  reached is a weak reduct of the redex, and the fire leaves that, headed
  by the redex's own jet node. An operand not yet a value at the top
  declines the fire; the term runs, a template instantiating, and forces
  it. So an operation forces nothing its term would not. `eqId` fires
  only where it can decide.

Its first version fired on 81,393 calls of about 1.4 million and saved
5%: `eqId` passes `eqB` the thunks `idBits x` and `idBits y`, so `eqB`'s own
fires came only from callers holding evaluated bits. Jetting `eqId`, whose
names are evaluated once and shared, made 1,213,753 fires. The output is
the same, every name's hash:

| front1 with templates and data jets | contractions | dispatches | bit-string operations |
|---|---:|---:|---:|
| on front0's source | 50,728,634 | 25,593,119 | -- |
| with the bit-string operations | 33,814,092 | 15,288,253 | 1,213,753 |
| its fixed point, 1,529 names | 633,573,940 | | -- |
| with the bit-string operations | 411,048,920 | | |

The fixed point fell from 53 s to 47 s, the template load among them:
loading front1's templates is 4.3 s of front0's source's 5.5 (§20.3).
Each operation is native code the runtime trusts, as a numeral
operation is, and a proof would owe a theorem for each. `tests/test_data.c`
runs every pair and key above, each in one native step to the term's
normal form, operands not yet values, and collections mid-run, on
`tests/data/bits`, a program defining the three functions as front1 does.

**What is left.** The profile of Milestone 0 (Queens2, templates) put
`whnf_share` at 47% of samples, `av_app` 23%, `tmpl_instance` 21%,
`try_interp` 5% and the collector 3%. The two levers it named are pulled
(avon `aeae3c9`, `docs/BENCHMARK.md`): `tmpl_instance` is inlined into
`src/jets.h` and allocates from a reservation, writing the root over the
redex root, and only jets with an interpreter's role call `try_interp`. A
step of Queens2 with data jets fell from 568 instructions to 401, a
one-node fire from 314 to 193. The levers measured since (§6.9, and
`docs/BENCHMARK.md`, "What becomes of an instance's cells") are a case
on a known value joined to its instance, and the spine cells, 61 to 65%
of what instances write.

### 6.11 Y unfolded in one step

**With `--fix`, share mode rewrites `Y g` to `g (Y g)` in one step.** Y is
Curry's `S (K (S I I)) (S (S (K S) K) (K (S I I)))`, the term skijack ties
every recursion with. Without the rewrite, each recursive call re-derives
Y's unfolding in five or six S, K and I steps (`docs/BENCHMARK.md`, "What
the gap is made of"). `av_fix_on` before the template load registers Y as
the numeral operations are registered (§6.10), found in the term and in
the templates' globals by tree identity. Y at the head with an argument
rewrites the redex root to `App(g, y)`, `y` a fresh `App(Y, g)`: one step,
one node, no indirection, and every pointer still points backward.

**It is convertible, not a reduct, so it keeps values, not states.**
With `M = S I I` and `Q = S (S (K S) K) (K M)`, `Y g` reduces to
`g (M (Q g))` and on to `g (g (M (Q g)))`, which `g (Y g)` reduces to as
well; neither of the two reduces to the other. So:

- a normal form `--fix` reaches is SKI's, byte for byte (by Church-Rosser,
  since the rewrite stays within conversion), and a term without one still
  stops at FUEL (`Y K`, `Y I`, `Y (S I I)`, `tests/test_fix.c`);
- that `--fix` reaches every normal form SKI's reduction reaches is shown
  by tests (`tests/test_fix.c`, `make front0-check`, the Reduceron ports),
  not proved: no argument here covers lazy share reduction plus the rule;
- answers read by probing are unchanged on every test; `Y g` and its
  unfolding have the same Böhm tree, which makes it expected, but the
  argument is not written out;
- a weak head normal form state may differ in form: `Y K` stops at
  `K (Y K)` where SKI stops at `K (K (S I I) K (I (S (K K) (K (S I I) K))))`.

lean-ski's simulation already allows for this: `Tr` "is a relation, not a
function" because Y unrolls to a self-reference that behaves as `Y ⬝ F`
(`Simulation.lean`, `Tr.self`).

**Not a cycle.** The experiment of `e74e581` (tag `experiment/knot`)
rewrote `Y g` to the cycle `n = g n`, and a cycle is what Avon cannot keep:

- it changes answers: `Y K` reports NORMAL, where SKI stops at FUEL;
- it hangs: `Y I` writes an indirection to itself and spins in `av_res`,
  `Y (S I I)` makes the spine cycle, both where no fuel is checked, and
  copy mode hangs;
- most of the runtime's graph walks loop on it -- the §5 hash, `hc_canon`,
  `match`, snapshots, `--profile` -- against §2's and §4.2's acyclic arena;
- the witness cannot hold it: lean-ski's heap points only backward, its
  `termAt` gives a cycle no meaning, and every soundness theorem needs
  `decode` to succeed.

The one-step rewrite writes a cell that points backward, so a witness row
for it could fit the write-once memory as it stands: at a loaded Y address with
a C cell, one cell `App(g, r)`, `r` the `App(Y, g)` the stack holds. Its
licence would be a simulation theorem relating the run to the plain one
by `Tr`, owed in lean-ski; not built.

**Results, 2026-09-30** (avon `fix-jet`; `docs/BENCHMARK.md`, "Y unfolded
in one step"). The steps fall almost as far as the cycle's -- PermSort
116.8 million against the cycle's 112.9, from 132.8 -- but the time does
not: 1.03 times less than data jets alone by geometric mean, against the
cycle's 1.20. The difference is memory. The cycle shares one node for a
function's recursion; each one-step unfolding makes a fresh `Y g`, and a
lazy structure keeps each copy it captured alive. PermSort peaks at 266 MB
with the rewrite, 244 MB without, 3.5 MB with the cycle; OrdList at 244,
236 and 3.4 MB.

So the sharing, not the steps, is what the cycle was worth, and an
acyclic unfolding cannot share an infinite term. What would recover it
is a cycle made safe: black holes, so that a cyclic redex that needs
itself stops at FUEL as SKI does; walks that tolerate cycles, or a proof
that none reaches them; copy mode left without it; and, before a witness
could use one, a lean-ski heap semantics for cycles. That is its own
plan. `--fix` stays: it agrees with SKI on every test, it is cheap, and
a witness row for it could be built. Today `avon witness` refuses `--fix`,
as it refuses `--templates` and `--data`: the witness runs plain SKI.

**Shared (`--memory`, 2026-10-05).** Almost all of a
port's live set is Y's unfoldings: with the cycle, the largest live set
after a collection falls from 2,293,349 nodes to 590 on OrdList and from
3,956,193 to 1,355 on PermSort. A recursive function is a shared node
updated in place to `g (Y g)`, whose `Y g` is updated in its turn, so every
level of recursion reached stays chained to it. `--memory` keeps one
`Y g`, `y0`, per generator `g` (by node identity), never written, and one
unfolding `u0 = g y0`, updated as any node. Every `Y g` of that `g`
becomes an indirection to `u0`, and `y0`, when demanded, leads to `u0`.
The link from `y0` to `u0` is a table's (`R.ymemo`, weak across
collections), not the graph's, so the graph stays acyclic and every walk
works as before. Following the link is a step, so a `Y g` that needs
itself runs out of fuel as SKI does. The node a call reduces, which its
caller reads, is unfolded in place as `--fix` does, and its `g` is never
shared again. Without that rule `K (Y K)` reported NORMAL, a bug the tests
now pin.

It keeps the cycle's memory: the largest live set falls to 584 to 7,802
nodes and peak memory to 4 to 8 MB on the five ports. It does not keep the
cycle's time: 1.00 times `--fix`'s by geometric mean, PermSort 1.10 faster
and Queens2 1.13 slower. A cycle's node is its own value, so a recursive
call reaches it at once; `y0` is never written, so every call passes
through it, its jet and a table lookup, 10 to 40 million times a port
(`docs/BENCHMARK.md`, "Y shared (`--memory`)"). Answers and normal forms
are `--fix`'s, the front end compiles its 492 names hash for hash, and
`tests/test_fix.c` checks a term with no normal form, the fixtures, every
fuel to 300 and a collecting arena. An option for a run whose heap matters
more than its time, such as a long-lived kernel; off unless asked, and
`avon witness` and copy mode refuse it with `--fix`.

**True cycles: parked.** On today's code the cycle would take 1.12 times
less time than `--fix` by geometric mean, 1.00 to 1.25 (`docs/BENCHMARK.md`,
"The ceiling for a true cycle"), and its memory is `--memory`'s. Against
that, a safe cycle needs indirection writes checked never to close a
loop, re-entry of a knot under evaluation turned into fuel, a normal-form
pass that refuses infinite terms, and no cycle leaving a reduction: every
exit, kernel pokes included, breaking each knot's back-edges, or every
walk and snapshot learning cycles.

### 6.12 Poseidon2 run natively

**With `--p2=FILE`, share mode runs lean-ski's Poseidon2 term natively.**
FILE holds the term `P` (`Ski/ZK/Poseidon2SKI.lean`) in the DAG form that
`lake exe p2run K OUTDIR` writes as `OUTDIR/P.dag`. `P` applied to a state
`stateN vs` reduces to `stateN (permute vs)`, sixteen 31-bit elements in
and the permutation out (lean-ski's `P_specN`). That theorem is the
licence, and the jet is its right-hand side computed in C (`src/p2.c`,
`av_p2_permute`).

**The C is printed from a proof.** `lean/P2Prog.lean`, checked against
lean-ski, prints `src/p2_prog.h` and proves what it prints
(`AvonP2.permuteC`). On every state of sixteen `uint32_t` values, the
printed program run with C's arithmetic gives `permute`. The proof has two
parts:

- **The program is the specification.** It is fifty-two layers of
  sixteen expressions each. The layers are lean-ski's own (`mat4LE`,
  `mixLE`, `sboxLE`, `sbox0LE`, `intLinLE`), the expressions from which
  her term `P` and the Poseidon2 AIR are proved, and her bridges join them
  into `permute` (`run_prog`).
- **C computes the program exactly.** A bound on every subexpression
  stays below 2^64, so no `uint64_t` sum or product wraps; every variable
  is one of the sixteen elements; and every layer's results stay below
  2^31 (`bnd`, `fits`, `prog_ok`, checked by the kernel). The printed
  S-box, reducing its input and then each of its four products modulo p,
  gives `x^7 mod p` (`sboxC_eq`).

The proof uses only `propext` and `Quot.sound`. What is trusted is C11's
unsigned arithmetic, exact modulo 2^64 (6.2.5p9), and the printer: one
line of C per constructor of the expression type (`cExpr`); a layer's
sixteen results computed from the old state before any is stored
(`cBody`); each distinct layer printed once and the layers called in the
program's order (`header`); and the S-box's text, which `sboxC` models
step for step. `make
p2-witness-check` reruns the proof and requires its print to be
`src/p2_prog.h`, byte for byte. The printed C matches the hand-written
permutation it replaced on 10^7 random states, at the same speed: 0.70 µs
a permutation against 0.73.

**`P` is pinned, and keyed by tree identity, not by digest alone.**
FILE is the user's input, and the jet would assert a false equation for
any other term. So `av_p2_register` refuses FILE unless its full digest
is `P`'s, compiled in (`AV_P2_SHA256`). The full digest is §5's Merkle
hash with every digest kept whole, 256 bits, over S, K and I only. The
§5 digest alone would admit a forged FILE: an atom whose name hashes to
one of `P`'s 12,753 subterms' digests, put in its place, after about 2^50
hashes at `skijack-1`'s 64 bits and 2^114 at `skijack-2`'s 128.
Registration also refuses a digest that another jet already holds under
another role or another term.

`av_jets_match` wraps each occurrence of `P` in the program, which may be
hostile. `av_p2_bind` compares each wrapped term with FILE's, node for
node (`av_equal`), unbinding any that differs. Every fire and every
decline checks its jet node's term again, so a jet node made after the
bind is held to the same rule; such nodes arise in a copy of another
jet's term, a template's globals, or a run-time match. A decline needs
the check as much as a fire does, since it runs FILE's term, not the
node's. Before 2026-10-04 it was unchecked, so such a node over anything
but a state ran `P` in place of its own term. The comparison visits each
pair of nodes once, and answers no past eight pairs per node of `P`'s
term. A 64-bit collision in the program therefore cannot reach the native
step, which would otherwise replace an arbitrary term's reduction with a
permutation. The check costs under 0.01 s a call.

**The jet fires on a state as it stands, or on a chain of calls ending in
one.** At the head with an argument, `P` reads the argument through
indirections and jet nodes (`av_p2_state_read`). The argument must be
exactly `stateN vs`:

- each element `bitsT 31 v` holds 31 pairs `S (S I (K b)) (K rest)`;
- each bit is `K` (1) or `K I` (0), least significant first;
- each element and the state end in `K`, with sixteen elements.

The redex root then becomes the permuted state, 2,562 fresh nodes, in one
step. An argument that is itself a call `P y` is a chain: lazy reduction
meets the outer call first. Avon checks the outer node's term, then walks
down the chain once to the innermost call whose argument is a state. It
fires the calls from there outward, each writing its permuted state over
its call's node, one step each, as far as the fuel and the free nodes
reach. Only a collection, which moves the nodes walked, forces a second
walk, so a chain of m calls costs O(m) visits per collection, not per
call: 16,000 calls take 0.16 s. A node found to be `P`'s is remembered
until the next collection, so a shared `P` is compared once, not once
per call. Each write is the reduct lazy reduction would write once the
outer call forced the inner one, so sharing holds: a call shared
elsewhere is permuted once. `P (P x)` for test vector 1 now takes two steps and 0.03 s,
against 981 million steps and 11 s before, when the outer call declined.
The unjetted run takes 1,943,605,466 steps and 22 s, to the same normal
form, byte for byte.

Any other argument runs a fresh copy of `P`'s term, counted as a decline:
a thunk, a malformed state, or a chain whose innermost argument is no
state. The copy keeps the jet node's own term unwritten, so a shared `P`
stays `P` for its next call. A jet node unbound at a call is counted too.
Words (§6.10) work the same way: an operation fires only on operands
already held. A chain of `P` calls fires natively. Any other computation
between the calls, `P (f (P x))`, declines unless its state is built
before it is passed on.

**Counts change, as for the other share-mode jets.** A fire is one step,
reported as `p2: … permutations run natively`. Fuel counts those steps,
not the 962 million the term takes. The normal form is SKI's, byte for
byte, because `P_specN` gives it. The weak head normal form state differs
in form only where the jet fired. Copy mode refuses `--p2`, and so does
`avon witness`: a proof licenses the jet through its own table (lean-ski's
`P2Jet.p2Row`; `ZK-JETS.md`), not through this rewrite.

**Results, 2026-10-03.** Plonky3's three test vectors (`make
p2-witness-check`, step 7) each reach Plonky3's output in one step. Test
vector 1 unjetted takes 962,192,547 steps, 10.1 s and 66 MB. With `--p2`
it finishes in under 0.01 s.

### 6.13 Deferred roots

**An instance no longer writes the spine the reducer is about to unwind.**
A template instance used to write its body over the redex root at once,
spine and all, and the reducer then walked straight back down that
spine. Spine cells are 61 to 65% of what instances write, and 55 to 95%
of them sit under a head that steps at once (`BENCHMARK.md`, "Most spine
cells are contracted through at once"). Now, in share mode with
templates, an instance leaves its root and spine in the reducer's stack,
as the Reduceron does (`src/stack.h`).

**The stack holds three kinds of entry.**

- **A real entry** is a node of the graph, as before.
- **A deferred entry** is the redex root's node, left as it was. The
  entry holds the body's outermost argument, and the entry above it is
  the function part.
- **A virtual entry** is an application with no node: the entry above it
  applied to the argument it holds. An instance pushes one for each
  application on its root's spine that only its parent uses
  (`av_tmpl.vspine`, found at load).

An entry's kind sits in a node index's two spare bits. A virtual entry
holds its argument in the same word, and a deferred entry's argument
sits beside its index on a second stack, so the stack takes no more
memory than before.

A contraction whose redex root is virtual builds no node for it. An
indirection's target becomes the head; an application's argument stays in
the entry, and its function becomes the head. A dispatch defers the same
way: a fused branch's instance, or the continuation applied to the
fields.

**A deferred root is written before anything else could read it.** The
graph is acyclic (§2), so while a root is being reduced nothing can reach
it by another path. It is written with the application its entries stand
for:

- before a contraction consumes it as a function part. It is then a
  value, its head short of arguments, and the graph shares it as the
  undeferred reducer would have;
- when the reduction stops: at a weak head normal form, at FUEL or
  INTERRUPTED, or at SIZE when there is room;
- before the steps that read the stack as nodes: interpreter, Poseidon2
  and residual jets. These write everything deferred first, then run
  unchanged.

A contraction whose redex root it is writes it, as it writes any root.

**A deferred node keeps nothing alive.** When a root is deferred its node
is overwritten with `I I`, since nothing reads it before it is written.
Left as it was, its old redex kept alive what the undeferred reducer
lets go: an adversarial review measured the live set up to 2.3 times the
undeferred one on a lazy list consumed in a loop. Overwriting it is safe
because writing the deferred roots never fails: the arena keeps a free
node for every virtual entry (`R.nvirt`), and every allocation while one
exists reserves them too.

**Nothing but the nodes changes.** Every contraction is the one the
undeferred reducer makes, at the same step. Steps, instantiations,
dispatches, fusions, joins and every state reported are the same, byte for
byte, unless a node cap (`--max-nodes`) binds: a stopping run writes its
deferred roots, and the reserve moves the collections, so near the cap the
deferred run may stop at SIZE a few steps sooner or later.
`tests/test_data.c` checks this with and without data jets, at every fuel
from 0 to 400 and in an arena small enough to collect, and checks that a
cap the undeferred run fits within by 10% fits both. Three bugs planted in
the deferral each fail it. `--no-defer` writes every instance at once, for
the comparison.

**A join no longer depends on the arena's fill.** A case joined to its
instance (§6.10) declined when the free nodes did not cover both writes.
With fewer nodes written, collections fall at other moments, so the joins
differed with deferral and without. The caller now reserves both writes
before it asks, so a case joins whenever its formal is a value. OrdList
joins 6,222,685 cases where it joined 6,222,282.

**Off where nodes are counted.** A profile and the jet stats key on the
nodes rewritten, and the stats build (`make stats`) counts the cells
instances write, so deferral is off under all three. A template that
makes words from SUC (`av_tmpl.sucop`) is instantiated as before.

**Results, 2026-10-04** (`BENCHMARK.md`, "Deferred roots"). On the five
Reduceron ports with templates and data jets, deferral runs 5.8 to 14.5%
faster: Clausify 1.79 s against 2.05, PermSort 3.53 against 4.03. It
retires 3.5 to 10.6% more instructions and runs 15 to 20% fewer
collections. Peak memory rises on three ports, by 8 to 39 MB, while the
largest live set is the same within 0.1%. The SKIjack-0 front end still compiles
its 492 names hash for hash in every mode (`make front0-check`).

### 6.14 Data jets for SKIlark: a plan

*Plan, 2026-10-24. Measured on avon `2040293`, skijack 0.2.1 and SKIlark
`4f607f5` (stage 5); steps are to weak head normal form unless a table
says otherwise.*

**SKIlark already gains from templates and constructor dispatch; its
numbers do not reach the native operations, and its lists have no data
jet.** Six interpreted programs, the steps of each mode:

| program | copy | share | templates | templates and data |
|---|---:|---:|---:|---:|
| `[1 2 3] [dup *] map` | 380,852 | 265,603 | 5,703 | 4,436 |
| `4 [1] [*] primrec` | 516,796 | 337,272 | 7,619 | 5,917 |
| `6 fact` | 183,405 | 132,649 | 3,046 | 2,363 |
| `"abcdef" size` | 147,268 | 111,685 | 2,405 | 1,855 |
| `[1 2 3 4] size` | 105,349 | 81,850 | 1,757 | 1,361 |
| `10 [0] [+] primrec` | 1,408,973 | 737,434 | 16,802 | 13,006 |

Templates take 60 to 84 times fewer steps than copy mode, and data jets
22 to 23% fewer again; no numeral operation fires, since SKIlark's
arithmetic is its own and not the prelude's.
Steps are not time, which is the measure (§6.10). The plan has three
parts, by the kind of data.

**SKIlark's terms: its sums dispatch now, and the cap keeps them doing
so.** `item` (6 constructors), `word` (31), `prog`, `stack`, `text` and
`result` are Scott sums, and §6.10's dispatch takes their cases in one
step. A template past 32 formals dispatches as SKI, since 32 markers
check it, so `word`, whose one-field constructors take 32 arguments, is
at the limit both of §6.8's constructor jets and of dispatch. Raising
`AV_JET_ARITY_MAX` for SKIlark's sets (its PLAN.md §3, stage 5) must
raise the markers with it, or `step` loses its one-step dispatch.
*Decided, 2026-10-24:* SKIlark took the sidestep instead (its PLAN.md
§3, stage 6). Its literals merged into `Lit item`, and `typeof`, sets
and a kernel `not` came in under the cap: `word` has 29 constructors,
`item` 7, and the one-field words take 30 arguments, so `step` keeps
its one-step dispatch and the cap stays at 32. SKIlark's stage 8 keeps
it there: its further kernel words go in `ext`, a sum of their own under
`word`'s thirtieth constructor `Ext`, and the one-field words take 31. The
compiled form's `quot` sum has one constructor per static quotation,
171 when SKIlark's thirty combinator programs compile as one set, so its
`apply` already dispatches as SKI there.

**Numbers: SKIlark's arithmetic on the prelude's operations, with its
operands made words first.** SKIlark's `nat` is a `Zero | Suc` numeral,
so its closed numerals become words (`W n`, 149 of them in the `map`
run), and its integers and characters ride on them: an integer is a sign
and a `nat`, a character an integer. Two changes on SKIlark's side make
the native operations fire:

1. *Build `nat` arithmetic from `natAdd natSub natMul natIfEq natIfLe`*:
   `add` as `natAdd`, `monus` as `natSub`, `less m n` as `natIfLe (Suc
   m) n True False`, and the comparison as `natIfEq m n Same (natIfLe m n
   Less More)`. Avon then admits the five operations.
2. *Case on an integer before an operation, so its magnitude is a word*:
   an operation fires only when both operands are words already, and
   `mul (mag a) (mag b)` hands it two unreduced applications. With the
   first change alone, `200 200 *` fires no operation.

Run to normal form with templates and data, with the first change and,
for multiplication, the second (the comparison cases on its integers
already):

| program | SKIlark's arithmetic | the prelude's, cased first | operations |
|---|---:|---:|---:|
| `200 200 *` | 8,360,922 | 160,085 | 1 |
| `200 200 * 199 <` | 84,354 | 118 | 3 |
| `200 200 * 7 /` | 8,607,176 | 291,621 | 5,715 |

User time for `200 200 *` fell from 0.25 s to 0.07 s. Division remains a
loop of native subtractions, since skijack has no `natDiv` or `natRem`;
adding them to the prelude, with Avon's words, is the third change. Two
limits stay. A word holds 28 bits, so a SKIlark integer past 2^28 - 1
computes in SKI, correctly and slowly. And a reader that prints a
result's normal form builds its unary numeral: `200 200 * 200 *` takes
1.67 billion steps either way, which a level-1 question (SKIlark's
`topIs`) or a reader that takes a word as a number avoids. zk's
verifiers compute in the compiled form's naturals block, whose terms
lean-ski proves, so that block keeps its own arithmetic until the proofs
move with it (§18.2).

**Lists: a word for lists, by analogy with the numeral's.** SKIlark's
quotations (`Done | Then word prog`), stacks (`Empty | Push item
stack`) and strings (`TNil | TCons int text`) are list-shaped: a nullary
constructor and a constructor of an element and the rest. Nothing in
Avon holds them natively, so `cat` copies its left list cell by cell,
and `size` and `at` walk one. The plan mirrors §6.10's words:

- *A list word.* `L [x0 .. xn-1]` is a jet node over a vector of element
  nodes, whose term is `Cons x0 (L [x1 ..])`, seen through by `av_view`
  as a word is, so printing, the hash, `jam` and the witness read the
  Scott list. It is made where a list is already whole: a closed list at
  load, and a list operation's result.
- *Operations on lists in the prelude, pinned by hash*: `listAppend`,
  `listLength`, `listAt`, `listTake` and `listDrop`, written generically
  over any list-shaped type as the numeral operations are over any
  numeral type, each admitted only if its term is skijack's node for
  node and agrees with the native operation on small cases. An operation
  fires only on list words already held, and builds lazily otherwise.
- *SKIlark's side.* The kernel's `cat` and `catT` become `listAppend`.
  Joy's `size`, `at`, `take` and `drop` are derived words, recursions
  over `uncons`, which a list word makes a dispatch per element but not
  one operation; to reach `listLength` and the rest they must become
  kernel words, and each is a `word` constructor: two fit under the cap
  since the sidestep, and more need the cap raised or `word` split.

*Progress, 2026-10-25.* Step (1) is SKIlark #18: its naturals are the
prelude's operations, each casing its numerals first so a computed one is
a word, and `200 200 * 199 200 * -` takes 962 steps, from 16,520,814.
Step (2) is skijack #25 and this runtime's `div` and `rem`: `natDiv` and
`natRem`, total (by zero, 0 and the dividend), pinned by term and run
natively; `100 7 /` on a SKIlark kernel whose division is `natDiv` takes
148 steps and one operation. SKIlark takes them up once skijack is
released with them.

*Progress, 2026-10-25, step (4).* skijack #27 and #28 add the prelude's
`listLength`, `listAt`, `listAppend`, `listTake` and `listDrop` on any
list type, total (`listAt l k d` is `d` past the end), listed in
`words.tsv`. This runtime holds a list as a chain of list words, the
numeral words' shape: `L n` is a word flagged `AV_JET_LIST` whose id
field is its length and whose term is `CONS x (L (n-1))`, so no side
storage is needed and every reader sees the cells. The scan makes them
from closed lists; a list word meeting its continuations dispatches as a
constructor of two fields, fused as a constructor's is, so a program of
lists dispatches as before (`tests/data/lists`: 331 steps, 83 fused,
either way). The operations fire on list words and words: `len` builds
its numeral, `at` and `drop` walk to their cell, `take` and `app` build
their cells, and each runs as its term on anything else. Each is pinned
by term and admitted on lists of up to three numerals. `test_data`
checks each against its term on lists of 0 to 3 elements and indices 0 to
4, and joins and deferral at every fuel to 400 on `tests/data/listops`,
whose `out` takes 124 steps to its normal form, from 522 as SKI. Numeral
words now hold up to 2^27 - 1, the 28th bit flagging lists. SKIlark's
`size` and `at` take them up next.

**Order of work.** (1) SKIlark's interpreted kernel and the compiled
integers on the prelude's operations, cased first: SKIlark alone, its
counts re-pinned, zk untouched. (2) `natDiv` and `natRem` in skijack's
prelude and in Avon's `words.c`. (3) The cap: markers and
`AV_JET_ARITY_MAX` together, or `word` split in two: SKIlark's sets
needed neither (the sidestep, 2026-10-24), and list kernel words past
two would. (4) List words: the prelude's list operations, Avon's list jet
node, and `tests/test_data.c`'s parity at every fuel. (5) The proofs:
§18.2's word cells, and a list cell beside them, each operation's
licence a Lean theorem owed.

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
  subject. A record cut short by a crash is dropped. A poke that does
  not reach weak head normal form leaves the log when it fails.
  - A logged record is an event the kernel took. Replay runs it with no
    fuel limit and no interrupt, so another run's `--fuel` cannot erase
    an acknowledged event (`AUDIT.md`, item 1).
  - A record that does not replay stops the open, and stays in the log.
  - So a crash between a live failure and its removal leaves an event
    that replays uncapped: it applies, or the pier refuses to open.
  - A pier's directory is 0700 and its files 0600 (item 2).
  - Every sync reaches the media. On macOS that is `F_FULLFSYNC`, since
    `fsync` leaves the data in the drive's cache. Directories are synced
    after a create or a rename (`src/durable.c`, item 3).
  - A record is written whole. One that fails to write or to sync is cut
    away again, so a pier kept open appends after a whole record (item 4).
  - Each record ends with a checksum, the first 4 bytes of its SHA-256,
    and its hex is read strictly and in linear time. A flipped digit
    stops the open instead of replaying as another event (item 10).
  - `events.log` is locked for the pier's life. A second process gets
    "the pier is in use" (item 5).
  - An event applied and logged is the pier's even if a persistent
    arena's commit then fails. The failure is reported beside it
    (`av_pier_commit_error`), so no caller retries an applied event. The
    next commit, or a reopen's replay, carries it (item 6).
  - Snapshots are not pruned yet.
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

### 9.1 Entropy

*Written 2026-10-04; decided the same day: per request, shape A, Scott
Booleans, effects as a list. SKIjack's side is SPEC §4.1, "Entropy".*

**A kernel gets randomness only as event data.** Reduction stays a
function of its term: no combinator, jet or scry yields fresh bits.
Replay, the conformance counts, every jet's licence and every proof rest
on that. Entropy reaches a kernel the way Vere's reaches Arvo, as events
the pier writes to the log before it applies them, so a replayed pier
sees the same bits.

**Decided:**

- **128 bits an event.** This is a research proof of concept, not
  production security, and 128 bits keeps the log and a proof's private
  witness small.
- **Per request.** A kernel asks in an effect, and the pier answers with
  an event carrying fresh bits from `getentropy(2)`, logged before it is
  applied. Boot answers one request of its own, so a kernel starts with
  a seed. The kernel keeps no ratchet; it asks again when it needs more.
- **Shape A, a tagged cell under an opt-in.** The pier acts on requests
  only for a pier booted with `--entropy`; any other kernel's effects
  pass through untouched.
- **128 Scott Booleans in a list,** `cons b₁ (cons b₂ … nil)`, each `bᵢ`
  `K` or `K I` (SPEC §4). It is pure SKI, so copy, share and witness
  modes all carry it, and it is the shape of lean-ski's private bits.
  Data-jet words would be compact, but they exist only in share mode
  (§6.10), so a proved poke could not take them.
- **`--entropy=FILE`** replaces `getentropy` with a file's bytes, for
  reproducible tests. A file that runs out stops the pier rather than
  falling back to `getentropy`.
- **The log is as secret as the bits it holds,** and so is the pier's
  directory.
- **In a proved poke the bits are a private witness** (lean-ski,
  `Ski/Entropy.lean`; proved below, "Proved").
- **Kernel entropy never feeds the prover's seed** (`ZK-JETS.md` §7).
  The two are separate draws from `getentropy`.

**Why per request, and not with every event.** Vere puts fresh entropy
into every event, and Arvo never asks. Under `--entropy` Avon could do
the same, wrapping each event `ev` as `[bits ev]`. It would need no
request shape, no probe of effects and no boot reply, and when running
it costs almost nothing: a `getentropy` call of about a microsecond, a
list of about 900 nodes that a poke which ignores it never forces,
and 16 bytes of log, all beside the millisecond `fsync` every event
already pays. The cost lands in proofs. A proved poke's statement covers
its whole event, so every proved event would carry the bits as private
witness cells, roughly 500 to 700 memory cells, whether or not the kernel
reads them; the Poseidon2 statement we prove has 9,480 in all. Most
events need no entropy, so most proofs would pay for nothing. Per
request, the extra work is a probe of each poke's effects, which runs in
the pier, outside any proved poke, and costs a few selector applications
per effect. Only the events that ask pay for bits, and only reply events
carry them into a proof. The price is a convention in SPEC §4.1 for the
shape of effects and events.

**The convention, for a kernel booted with `--entropy`.** It follows
Arvo's `(quip card _this)`: a poke returns a list of cards, each a cell
with its tag first.

- **Effects are a list,** `nil` and `cons` (SPEC §4), of cells
  `[tag data]`, `tag` a Scott numeral.
- **A request is the element `[0 id]`,** `id` a numeral the kernel
  chooses, like a `%pass` on a wire.
- **Events are cells `[tag data]` too.** The reply to a request is the
  event `[0 [id bits]]`, like the `%sign` that comes back on the wire.
  Tag 0 belongs to the pier, so that no driver can forge a reply and
  choose a kernel's bits. The pier accepts an outside event only when a
  probe shows it a cell whose tag is a successor, and refuses everything
  else, a probe that runs out of fuel included. Only that positive answer
  is sound. A tag can reach 0 after more steps than a probe spends, and
  copy-mode probes and the share-mode kernel count steps differently, so
  "not shown to be 0" lets such a tag through; the first review found
  exactly that forgery. A positive answer holds whatever the fuel: probe
  markers are inert, so a reduction to `m g d` with `g z s` reducing to
  `s n` is a reduction for the kernel's own continuations too.
- **Boot's reply is `[0 [0 bits]]`,** the first event after boot.

The pier reads the effects by probing (`av_peel`, `av_read_nat`), as it
reads a kernel, never by name. It walks the list in order and answers
each request with its own reply event; a reply's effects are walked in
turn. Elements that are not requests are left as they are, and so is an
effects value that is not a list. One outside event draws at most 16
replies, and its probes, its replies' included, spend at most 10,000,000
contractions. A kernel that asks without end is stopped there, its
remaining requests reported and unanswered.

**Logged as bytes, rebuilt on replay.** A reply is logged as an `eny`
record holding the jammed `id` and the 16 raw bytes, synced before the
reply is applied. Replay rebuilds `[0 [id bits]]` from them: bit `8i + j`
of the list is bit `j`, least significant first, of byte `i`. Replay
answers no request; the replies it needs are the `eny` records already
in the log. `--entropy=FILE` reads the file from byte `16 n`, `n` the
`eny` records in the log, so a test pier reopened with the same file
draws what it would have drawn without the reopen.

**Failures after the event leave it applied.** A request whose reply
cannot be drawn (a spent file, a failed `getentropy`) leaves the event
that asked applied and logged, so `av_pier_poke` reports success and puts
the failure beside it (`av_pier_entropy_error`); a caller that took it
for the event's failure would apply the event twice. So does a crash
after the event is logged and before its reply is. Either way the request
stays unanswered, as a lost network packet would, and the kernel asks
again. Boot's own request is the exception, since no kernel asks it: the
first poke answers it if no reply is logged.

**Opt-in and source are fixed at boot.** The `entropy 0` record goes to
the log before the pier's image, so a crash between them leaves a pier
that does not open, not one that opens without its opt-in. The record
also says whether the pier draws from a file, and a pier never mixes the
two sources: a file pier refuses a poke given no file, and a
`getentropy` pier refuses a file.

**Built 2026-10-04** (`src/pier.c`, `avon boot --entropy`; SKIjack SPEC
§4.1). `tests/test_entropy.c` runs `tests/kernel/entropy.ascii.ski`, a
kernel whose events ask once, ask twice with an ordinary effect between,
or turn greedy and ask on every reply. Against a file of known bytes:

- boot's reply and each request are answered in order, with the ids
  asked and each reply's bits the file's next 16 bytes, least
  significant bit first;
- a reopened pier replays to the same answers on every peek path, and
  with the file again draws on from byte 64, after the four replies
  logged;
- a forged reply is refused and leaves no record, and so is one whose
  tag reaches 0 only after about 400,000 steps, and an event that is no
  cell;
- boot's reply, lost to a crash, comes with the first poke;
- a file pier reopened without its file refuses to poke;
- a collection in the event hook loses no request;
- the greedy kernel draws 16 replies and is left one request;
- a spent file leaves the event applied, its failure reported beside it;
- a pier booted without `--entropy` passes a request through as an
  ordinary effect and takes a tag-0 event as its own.

A reply is 909 nodes as the pier builds it. The probe reads a request's
`id` as its normal form, since a probe's field is a thunk over its
marker; the reply carries that normal form, convertible to the kernel's
`id`.

**Proved, 2026-10-05** (lean-ski `Ski/Entropy.lean`, `release/entropy`).
A poke whose event is a reply is a predicate statement over 128 literal
bits, the reply's. Its verifier, `entropyV`, reads the public `[k [id
chk]]`, builds `[0 [id bits]]` from the circuit's bits in this pier's
encoding, pokes `k` with it and hands `[effects k']` to the check `chk`.
An accepted proof holds 128 Booleans on which `chk` accepts that poke
(`Circuit.entropyExport_sound`), and the bits are the circuit's private
slot cells (`Circuit.comp_zk`). lean-ski compiles the kernel from
`tests/kernel/entropy.ascii.ski` to the same term SKIjack does, and its
`lake exe entropy emit` reads a pier's `eny 1` record for the witness.
The release proves two checks of this kernel's boot poke, each from a
fresh pier's bits: `bootok`, which reads no bit, and `firstset`, which
discloses the first. About 1,900 CPU rows and 13,600 memory cells, half a
second. The proof does not show that the bits came from a pier: a prover
chooses them, as the pier's operator does.

### 9.2 Drivers: effects every front end shares

*Written and decided 2026-10-26. SKIjack's side is
`RUNTIME-DESIGN.md` §3e and `SPEC.md` §4.1, SKIlark's is its `PLAN.md`
stage 15. Built in memory: `avon run --kernel` (`src/drivers.c`), which
agrees with SKIjack's reference drivers on 17 runs
(`tests/drivers_check.sh`, in `make check`). The first user, SKIlark,
is built: its door (SKIlark #31, `skilark/door.py`) runs every stage-14
program and every example file under `avon run --kernel`, writing what
stage 14's host writes, in copy and share mode. The durable form, `avon
boot --drivers` (`src/pier.c`), is built 2026-10-28: every world of
`tests/drivers_check.sh` runs in a pier as in memory, each finished pier
reopened performs nothing, and echo killed while it waits on a read
resumes to the same output (`tests/test_drivers.c` stops runs at every
request and resumes them).*

**A program does I/O through effects in one shape, and the pier performs
them.** SKIlark's I/O words (stage 14) end a run with `RIO n s q`, and
SKIlark's own Python host answers them. Avon cannot answer that shape
without learning Joy: how a Joy value prints, how a factor reads, which
number is `put`. A front end that targets Avon would each need such a host.
Vere and Arvo split the work the other way. Gall's agents emit cards, Vere's
drivers perform them, and neither knows the other's language. Avon already
has one such driver: entropy (§9.1). This section adds the others a
command-line program needs: writing bytes, reading bytes, the environment,
a clock and an exit. SKIlark would be their first user; any front end that
emits SKIjack's kernel shape, a Jock or a Hoon front end among them, could
emit the same cards.

**The shapes are §9.1's, generalized.**

- **A program is a kernel** (§9): a door whose `poke` returns
  `[effects kernel']`.
- **Effects are a list** (`nil`, `cons`) **of cards `[tag data]`**, `tag`
  a Scott numeral.
- **Events are cells `[tag data]`**, and tag 0 belongs to the pier. A reply
  is the event `[0 [id answer]]`, `id` the numeral the kernel put in its
  request. The pier still accepts an outside event only when a probe shows
  a successor tag, so no driver can forge a reply.
- **Bytes** are Scott lists of numerals from 0 to 255. Share mode's list and
  numeral words hold them natively (§6.10); copy and witness modes carry
  them as plain SKI.

**The cards.** The tag picks the driver. Entropy keeps tag 0.

| tag | card | the pier | reply |
|---|---|---|---|
| 0 | `[0 id]` | draws 128 bits (§9.1) | `[0 [id bits]]` |
| 1 | `[1 [fd bytes]]` | writes `bytes` to `fd`, 1 or 2 | none |
| 2 | `[2 [id [fd max]]]` | reads at most `max` bytes from `fd` 0 | `[0 [id bytes]]`, `nil` at end of input |
| 3 | `[3 [id name]]` | looks up the variable `name` | `[0 [id v]]`, `v` a list: `nil` when unset, `cons value nil` when set |
| 4 | `[4 id]` | counts the run's steps so far (below) | `[0 [id steps]]` |
| 5 | `[5 code]` | stops the run after the cards before this one | none; `code` from 0 to 255 is the exit status |

Reading takes bytes, not a line or a token: `max` of them, fewer only at
the end of input, so a pipe's short reads change no answer. The kernel
buffers what
it has not yet consumed, so the driver knows no syntax: Joy's `get` asks
for bytes until it holds a whole factor. A variable's value is a list of
zero or one strings, so unset and empty differ, and the shape needs no
option type beyond the prelude's lists.

**A run starts with its arguments.** Boot under `--drivers` answers a
request of its own, as boot under `--entropy` does. The first event is
`[0 [0 [argv bits]]]`: `argv` the program's arguments as a list of byte
strings, its name first, and `bits` the 128 bits under `--entropy`, or
`nil` without it. The first poke therefore starts the program, with
`main`'s arguments and no extra request. A pier booted with `--entropy`
alone keeps §9.1's boot reply unchanged.

**The walk is §9.1's, extended to every card.** The pier walks a poke's
effects in list order once the event is logged. It performs a write when
the walk reaches it, answers a request with a reply event poked then and
there, and queues the reply's own cards behind the ones not yet walked.
So a kernel that writes a prompt and then asks to read has the prompt on
the terminal before the read blocks. A card the pier does not know, or one
whose fields do not probe to the shape above, passes through untouched, as
§9.1's do. An exit card ends the walk; the cards after it are not
performed.

**Bounds change for programs.** §9.1's 16 replies and 10,000,000 probe
steps for one outside event bound a kernel that serves events. A program
is one chain of replies from its first event, so under `--drivers` the
pier follows replies until the queue empties or an exit card ends it.
`--fuel` still bounds each poke. A run whose queue empties without an exit
ends with status 0.

**Every answer is logged before it is applied**, as an `eny` record is:
the bytes read, the variable's value, the step count and the arguments.
A record keeps the answer as its payload, `rep N <tag, id> <payload>`,
not the reply's term, which a megabyte read would make gigabytes of jam;
the reply is built from the payload, live or replayed, the same way.
Boot's answer is logged when the pier is made, before its image, so the
arguments survive a crash before the first poke.

Replay answers nothing; it applies the logged replies, so a reopened pier
reaches the state it left. The walk is replayed with them: a reopened pier
runs from snapshot 0, its only image, since the queue of cards not yet
walked is in no snapshot, and each request the walk meets takes the log's
next answer, its tag and id checked against the request's. Writes are not
performed again on replay: an effect is released only after its event
commits, as Vere's are (§21.1). At the first request the log does not
answer, the run is live again. A pier reopened after a crash therefore
continues without printing twice. The cost is at most once: a write the
walk had not reached when the crash came, behind the last logged answer,
is not performed either. A program waiting on a read, the usual place to
be killed, loses nothing.

**The clock counts steps, not time, until binary numerals land.** Card 4
answers the contractions the run's pokes have taken when the walk reaches
the card, in the pier's strategy. Copy mode's count is the
reference host's, so copy mode answers as the oracle does; share mode
counts its own steps, which differ for the same program. Time would cost twice
over: a CPU clock measured from the process's start runs backward across a
restart, and wall time since the epoch, near 2^41 ms, is no unary
numeral. A step count has neither problem. Replay runs the same pokes and
recounts the same steps, so the count never decreases across a restart,
and the logged answers agree with it. Wall time and CPU time come with
binary numerals, with `time` and `rand`.

**The count is a Scott numeral, unary like every numeral here.** In share
mode with `--data` the pier builds the reply as a word (§6.10): its
arithmetic native, though its predecessors are built too, two nodes each. In copy mode the reply is the
plain term, n successors deep: a run of 10^6 contractions is answered by
a term of 10^6 successors, and arithmetic on it is unary. That is what any
SKIlark integer of that size costs. Bytes stay small, at most 255
successors.

**Most programs are not kernels, so the kernel is the opt-in.** A door is
a cell `[battery state]`, and no shape tells it from any other value, so
the command line says which it has:

- **`avon run PROG`** reduces a plain program and prints its normal form,
  as `avon reduce` does. It performs no cards.
- **`avon run --kernel FILE ARG…`** runs the kernel FILE holds with the
  drivers on, its log in memory, exiting with the program's status. FILE
  is the kernel itself, as SKIjack's reference host takes it, not a pill,
  and it is adopted unreduced: its first poke reduces it, and the step
  count includes that.
- **`avon boot --drivers --pier=DIR FILE ARG…`** is the durable form of
  the kernel run. It survives a crash mid-run, and can be proved event by
  event. Without FILE it reopens the pier's run: the log replayed, then
  the run continued, in the strategy it was made with.

**Proofs keep their shape.** A poke whose event is a reply is a statement
over that reply's answer, as an entropy reply is (§9.1, "Proved"). The
answer is public or private by the statement's choice. A write is part of
`effects`, which a probe segment can bind as output (§17.4). Nothing here
is proved, and no circuit changes: a driver acts between pokes, outside
any proof.

**What it costs Avon:**

- **The C:** a probe of each card's tag and fields and a read of its bytes,
  a probe per successor, or at once for a word. Then a system call per
  card, and, in the durable form, a log record per answer.
- **The pier:** the queue and the log record types beyond `eny`.
- **The front end:** printing and parsing values in its own terms. Avon
  never learns a language.

**What it costs a front end.** The work Avon does not do, the front end
does in SKI. SKIlark must print a Joy value for `put` and read a factor
for `get` inside its kernel. These are contractions that the stage-14
Python host spends outside the run today. Jets can win them back later,
licensed as any jet is (§6).

**Decisions, taken 2026-10-26:**

1. **Flat numeral tags,** with the registry in SKIjack's SPEC §4.1. NockApp
   nests `[driver [verb data]]` so that several drivers can watch one
   effect; here each card has one driver, and one probe of a numeral picks
   it.
2. **Boot's reply under both opt-ins is the pair** `[argv bits]`, so a
   kernel asks for nothing at the start.
3. **`clock` answers the run's step count,** as above, in place of Joy's
   CPU time. Time waits for binary numerals, with `time` and `rand`.
4. **Descriptors 0, 1 and 2 only.** Files by path are a later driver,
   SKIlark's stage B.
5. **No bound under `--drivers` beyond `--fuel`.**

**Out of scope:** files by path, timers, the network and `system`. Each
would be a further tag in the same shape.

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
   for string, including the `skijack-2:` prefix.

### 10.3 Fuzzing

Two fuzzers run in `make check`, and so in CI, under ASan and UBSan, with
20,000 cases each by default (`AVON_FUZZ=N` sets the count):

- `test_reduce` reduces random terms of S, K, I and atoms in both
  strategies and compares their normal forms;
- `test_wire` hands `cue` mutants of valid containers (bits flipped, bytes
  replaced, ends cut) and random bytes behind a valid header. `cue` never
  crashes, and whatever it accepts `jam`s back to the same bytes.

`test_jets` adds 20 rounds of jet fires checked against their terms and
`test_interp` 150 interpreter cases per spec. The differential against
`aviary_kernel`, `tests/diff_aviary.py`, needs aviary and runs by hand: one
run of 6,000,000 terms under the sanitizers found no mismatch. CI runs
none of it at millions.

## 11. Stages, with acceptance criteria

Each stage ends with something testable. Rough sizes are C lines, excluding
tests, as planned in 2026-09; the built code differs (about 15,700 lines of
C today, `main.c` and `reduce.c` since split along their commands and
machines).

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
skijack `5d335c0`, unless a stage names another revision. Each stage's
figures are as measured when it was built; the revisions the checks use
today are pinned in `tests/pins.sh`.

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
  285 distinct corpus terms (18 programs; 4 fail skijack's Stage A) and on
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

- **Hashes match skijack's strings** on all 286 rows of the corpus
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
  all 81 distinct abstractions of compiling `abstract.ascii.ski`.
- **The corpus compiles in Avon to Python's terms, hash for hash**, again
  for abstraction: all 8,554 distinct abstractions of the 18 compilable
  corpus programs, by the term (`make selfhost-check`).
- **The compiler jet, licensed by differential**, agrees on every one,
  every fire checked; a term that does not abstract as aviary does is
  refused.
- **The compiler is a term in a pill**, a kernel answering `Abs` events.
- **The front end, for SKIjack-0, compiles its own source** (§20.3,
  "Built for SKIjack-0"): all 492 of its names, from source text, hash for
  hash (`make front0-check`). The full language's front end is built
  through M4 of six: every corpus program compiles in Avon to Python's
  terms (`make front1-check`). The checkers remain.

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

**Beyond the stages: speed in share mode.** None of it enters copy mode
or a witness; `avon witness` refuses every option below (`--templates`,
`--data`, `--fix`, `--memory`, `--no-defer`, `--p2`), as it refuses any
reduction option it would ignore.

- **Supercombinator templates** (§6.9, 2026-09-29): the front end compiles
  itself in 21.2 million steps against SKI's 307.0 million, 4.5 times
  faster, every name's hash unchanged.
- **Data jets** (§6.10): constructor dispatch fused into the branch, and
  numerals held as words. PermSort takes 2.12 times less time than with
  templates alone, the other four Reduceron ports 1.10 to 1.19.
- **Cheaper instances** (§6.10, "What is left"; avon `aeae3c9`): a step of
  Queens2 fell from 568 instructions to 401.
- **Y unfolded in one step** (§6.11, `--fix`): 1.03 times less time by
  geometric mean. The steps fall, but each unfolding copies `Y g` where a
  cycle would share it.
- **Poseidon2 run natively** (§6.12, `--p2`): `P ⬝ stateN x` in one step,
  against 962 million steps and 10.1 s unjetted.
- **Against the Reduceron** (`docs/BENCHMARK.md`, "Remeasured,
  2026-10-04"): with data jets, `--fix` and deferred roots Avon takes 1.47
  to 2.67 times its time on the five ports, 2.08 by geometric mean, and
  1.91 compiled with skijack's inlining. Per step it keeps the Reduceron's
  pace; it takes more steps, most of them Y re-deriving its unfolding.

**Beyond the stages: proofs and the paper.**

- **Jets under hiding** (`ZK-JETS.md`, milestones 1 to 9, 2026-09-30):
  Avon writes composed statements' witness tables with jets, byte for byte
  ski-air's, and lean-ski proves `split8` with jets under hiding.
- **Frame traces** (§22): the pure-S paper's hider census runs through
  Avon, every trace and verdict equal to the census's on the 82,500 terms
  of size 1 to 12, and sizes 13 to 16 (13.3 million terms) in eight
  minutes. The paper's check of its defect lemma runs through Avon too:
  every count of size 1 to 11 equal to the paper's, and sizes 12 to 16
  (13.4 million terms, 2.97 billion steps) with no counterexample, size
  16 in 126 s.

**Open.**

- *Stage 8:* the full language's checkers, M5 (Stage A: refusal parity,
  errors with a class) and M6 (Stage B: Hindley--Milner type checking).
  The front end through M4 is built.
- *Proofs* (to lean-ski): witnesses refuse terms with atoms (§17.3); scry
  proves only a resume loop's final run; zero knowledge survives
  Fiat–Shamir in the programmable random-oracle model for the Sudoku,
  hidden-term and composed circuits, not yet for those with jets or
  Poseidon2; Fiat–Shamir soundness past the counting step (`logup_fs`)
  and ChaCha20's pseudorandomness are assumed (one 128-bit prover seed
  per proof, `ZK-JETS.md` §7); data jets
  and the one-step Y have no witness rows, and the Y row's simulation
  theorem (`Tr`) is owed (§6.11, `ZK-JETS.md` §8).
- *Speed:* a case on a known value joined to its instance and the
  spine cells instances write are built (§6.10, §6.13); the join is not
  yet retried on top of deferred roots. The sharing a safe cycle would
  give Y is parked: 12% did not pay for what a safe cycle needs (§6.11,
  `WORKLIST.md`).

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

Struck items are settled; the rest remain open.

- ~~`I` as a third bitstring leaf code versus expansion to `S K K`.~~
  Settled in stage 2 (§4.2): the third code, and atoms after it.
- ~~Whether `copy` or `share` is the default strategy.~~ Settled: `share`.
- ~~Whether a jetted snapshot records the dashboard version.~~ Settled in
  stage 4: a snapshot holds no jets and no dashboard, so it has no version
  to record; jets are matched again after a load. Jet ids are local to an
  arena and never persisted.
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
  whether the standard subject ships compiled, quoted, or both. Stage 7
  shipped without it, since SKIjack's standard subject is not yet built;
  `boot` applies a pill to `I` unless `--subject` names another.
- ~~Whether install is a runtime primitive the kernel invokes or a `UQ`
  application the runtime jets (§20.2).~~ Settled: the jet, so the
  calculus alone still defines what install means.
- Whether a witnessed run may include compilation, and so whether the
  compiler jet needs a proof licence (§20.3). Recommended: not before the
  interpreter jet's licence exists.
- Whether Avon splits into a supervisor process and a worker, as Vere does
  (§20.4). Decided in principle: it will split; the terminology and the
  boundary are to be fixed before it is built. Stage 7 shipped as one
  process.
- Atoms in the circuit. Decided and done in `lean-ski` (§17.3): the
  machine has an inert `atom` cell and the AIR a halting kind for it. What
  remains is carrying atoms through the Plonky3 tables and the checker.

## 16. Provenance of the numbers in this note

Every count in §1, §2 and §13 was measured on this machine against
`aviary-kernel` 0.1.0 and `tower_harness.py` from `artifact-metacircular-ski`. The script is
`avon/bench/strategies.py`, in the SKIjack repository, and it reproduces the whole of §1 in about a
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

A composed statement with jets (`docs/ZK-JETS.md`) names four budgets in
its `log R M Lp Li` line: rows, memory cells, and POP's and INSTW's rows --
the instantiations' argument pops and written cells. `avon witness
--statement=PUBLIC --jet-table=JETS WITNESS` pads its table to the
statement's heights, not to the next power of two above the run, and
refuses a run over any of the four. Under hiding a height chosen from the
run would publish the run's size.

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
  blinding. lean-ski now proves honest-verifier zero knowledge for its
  hiding circuits, the quotient, its chunks and FRI's view simulated
  (`transcript_zkG_fri`, `*_transcriptG_fri`). It assumes that the Merkle
  commitments hide and that the honest chunks are the quotient (`RecOK`),
  and takes ζ and α_b of full degree as hypotheses. Zero knowledge
  survives Fiat–Shamir in the programmable random-oracle model for the
  Sudoku, hidden-term and composed circuits (`*_fs_open4`), with only the
  first commitment's hiding derived (`*_fs_open4ROMMC_fri`); not yet for
  the circuits with jets or Poseidon2. Jets under hiding are
  designed in `ZK-JETS.md`. The prover draws all of a proof's hiding
  randomness from one fresh 128-bit seed, expanded by ChaCha20 with one
  stream each for blinding tuples, leaf salts and masking codewords;
  that ChaCha20 is indistinguishable from uniform is assumed
  (`transcript_prg`, `ZK-JETS.md` §7). Avon takes no part: its tables are
  unblinded, and kernel entropy never feeds the seed.
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
  jetted run takes 28–34% of the plain run's rows, and 27–30% since
  lean-ski stopped licensing jets at bare combinators (`ZK-JETS.md` §1).
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
native values. Share mode holds them already (§6.10): a word `W n` is this
cell's value in the clear, its term the numeral, and its operations are
admitted by identity, each term pinned to skijack's and checked on 36
pairs, which is all share mode needs. A proof needs more:
share mode's word is a jet node over its numeral term, which the witness
has no cell for, and its operations are trusted, not proved.

A proof needs a word cell `W n`: an inert leaf with a
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
- §6.11: Y's one-step unfolding would be a row writing one backward cell,
  `App(g, r)`, licensed by a simulation theorem up to lean-ski's `Tr`
  (owed); a witnessed recursive call now pays Y's plumbing in S, K and I
  rows.
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
- Under hiding: `ZK-JETS.md` designs a circuit that joins the jet tables
  to lean-ski's composed statement in zero knowledge, with statement-fixed
  heights and a blinding tree over the eight private tables.

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
  123 outermost abstractions, 81 distinct once variables are renamed;
  the term, run in Avon, gives every one of them, text and hash, in
  687,177 contractions.
- **The corpus.** Compiling the 18 corpus programs that compile performs
  19,358 abstractions, 8,554 distinct; the term gives every one, hash for
  hash, in 476,833,099 contractions. Since skijack #36 each abstracts a
  formal over a body whose references are still atoms, and a
  definition's term is the last abstraction of its chain with each
  reference replaced by its own term, a substitution; before, the bodies
  held the references' terms, and the counts were 87 and 8,636 distinct,
  in 12,214,849 and 523,815,334 contractions. The terms are the same.
- **The compiler jet** answers `abs x t` natively (`av_abstract`), its
  datum decoded by probing and its result encoded with the program's own
  constructors.
  - It is admitted only if its nine terms (`abs` and the constructors)
    are skijack's: `compiler.c` pins their full digests (2026-10-06,
    `AUDIT.md` item 8).
  - The term must also agree with the native abstraction on sample terms.
  - With `--jet-check=1` every fire is compared with the term's
    reduction: 8,554 of 8,554 and 81 of 81 agree.
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

§6.7 measured jets for this front end: constructor jets and residual
jets for its own equations both make it slower in share mode, so what
remains of its cost is for the extended basis to try.

**The full language's front end, by milestone** (skijack's
`python/skijack/selfhost/front1.ascii.ski` and `run1.py`;
`tests/front1_check.sh`; the milestones in `WORKLIST.md`, item 3). It
grows from `front0` and is checked against the expander with checking
off, which gives the same terms as with checking on.

- **M1 to M4, built 2026-10-05:**
  - M1: cores, hygienic macros with the expander's three limits,
    signatures parsed and dropped, the birds `B`, `C`, `W` and `Y`, and
    the numeral operations;
  - M2: interpreter generation, the walker, rebuilder, default steps and
    each interpreter core's step and fuel loop, with the names they need
    built at run time;
  - M3: quotation and level-1 runs. A datum is its body's term encoded by
    the object type's constructors. A quotation may name a datum only if
    that datum is declared before it, directly or through level-0 rules, as
    in Python;
  - M4: scries, paths and namespace literals.
- **Its fixed point:** all 1,009 of its names, in 80,541,877 contractions
  with templates and data jets.
- **The corpus:** it agrees on all 21 programs, the 17 the expander accepts
  and the 4 it refuses.
- **Edge programs:** it agrees on all of them, run0's and each
  milestone's. Twelve once differed where aviary's environment decided,
  not SKIjack's rules: a binder named as a defined name, a binder twice, a
  recursion's name rebound, a binder named as a later definition. skijack
  fixed the reference (2026-10-21, a binder is a binder whatever name it
  spells), and front1 had been right on all twelve.
- **Random programs:** it agrees on 200 random SKIjack-0 programs, and on
  every random program of the full language the expander accepts. Those
  programs have macros, cores, object types, interpreter cores, datums and
  level-1 runs.
- **What counts as refused:** a term holding a name the expander left
  unresolved, a free atom, counts as refused, as Stage B refuses it. One
  example is a level-0 name that names a level-1 run.

Its term is 635,173 nodes inlined, against 265,145 at M1. Python takes 48
seconds to compile it, against 9.

- **M5, built 2026-10-27: Stage A** (`check.py`), over the parsed program
  before macros and generation, as Python checks before it expands. A
  refusal carries its class, a numeral `avon front0` prints as `RErr n`:
  Stage A's first problem's, ScopeError to SymbolTableError, or 0 where
  the parser or the expander refuses. The first class needs no reordering
  of the walk: every duplicate is a ScopeError and comes first, then the
  object and path types' shapes, then a binder named S, K or I, then each
  declaration in source order. Its reference is Stage A over Python's
  parse, then the expander with checking off.
  - It agrees on all 22 corpus programs, the 4 refused each a ScopeError,
    and on all 432 edge programs, 97 of them M5's: each of Stage A's
    checks passed and failed, and the order of the first problem.
  - It agrees on 991 of 1,000 random programs of the full language, on
    100 of a second seed and on 200 of SKIjack-0. The other 9 pass 2×10⁸
    contractions or 2×10⁷ nodes and are not compared; the three measured
    against front1 before M5 cost it the same there.
  - Its fixed point: all 1,116 of its names, in 95,944,164 contractions
    with templates and data jets.
  - Two readings of the parser it needed: a qualified name, `a.b`, is
    one name no table holds; pass one refuses a constructor declared
    twice.
  - Its term grew from 117,273 distinct nodes to 131,354; Python takes 63
    seconds to compile it with checking, against 48.
  - It did not yet install `natDiv`, `natRem` or the list operations,
    which the expander's prelude gained after M4; it has since M6 (below).

- **M6, built 2026-10-28: Stage B** (`typecheck.py`), over the generated
  program with its bodies macro-expanded, after Stage A and before
  front1's own expansion, as Python orders them; any problem is class 7,
  TypeMismatchError.
  - Python's Stage B mutates objects in place: variables bind, and an
    arrow's elimination, nominal type, datum, checked and numeral marks
    change during unification. front1 keeps every type node in a store
    keyed by number, each node the next, so the variables keep Python's
    order, which generalization sorts by. Unification is oriented and
    equirecursive, its seen pairs threaded as Python's set is shared down
    one call. Every problem is the same class, so the first ends the pass.
  - Its reference is Stage A, generation, Stage B, then the expander.
    front1 agrees only where both can witness: a refusal Python gives
    because inference outran its recursion limit is not compared, and
    front1 may accept that program. None occurred in the runs below.
  - It agrees on all 22 corpus programs, all 472 edge programs (43 of
    them M6's), 1,300 random programs of the two generators and 500
    programs typed as they are written, 429 of them accepted, hash for
    hash.
  - Its fixed point: all 1,520 of its names, in 619,922,690 contractions
    with templates and data jets, 2.46 GB at peak. Without templates
    Stage B's run passes 12 GB, so the fixed point runs with them.
  - The prelude's later operations, 2026-10-28 (skijack #39): front1
    installs all twelve numeral and list operations a program names and
    does not define, `natDiv` and `natRem` over the prelude's `natSub` and
    `natIfLe` as `natMul` is over its `natAdd`. It found a bug in the
    expander: an operation installed only for another's use took the
    program's name, so a core called `natSub` beside `natDiv` printed its
    loop but resolved to the prelude's `natSub`; skijack fixed it. Every
    corpus program, all 482 edge programs (53 of them Stage B's), 1,300
    random programs and 500 typed ones, 424 accepted, agree, and the
    fixed point covers 1,529 names in 633,573,940 contractions.
  - Two changes outside it made that affordable. skijack's expander
    abstracts formals with references as atoms and expands them after,
    the same terms, so front1 compiles with checking in 12 seconds where
    aviary's order passed an hour (skijack #36). skijack writes template
    terms in the DAG form, which Avon's loader reads (avon #82, skijack
    #37): 122 MB where the printed trees were 410 MB and took 7.8 GB to
    load.
  - Stage B in SKI doubles front1's work on front0's source, from
    415,021,159 contractions to 835,862,139. The candidates for
    supercombinator and data jets, from a profile of that run: the
    store's tries keyed by numbers (`ndGet`, `ndPut` and their kin, 10%
    of contractions), name and bit comparisons (`cmpCode`, `eqB`,
    `cmpBit`, `cmpName`, 9%), a scheme's instantiation (`bInst`), and
    the continuations built at run time (33%).
  - With templates and data jets, the run's own profile (2026-10-28)
    puts a third of it in bit strings, and three bit-string operations
    run natively (§6.10, "Bit strings"): front1's fixed point from
    633,573,940 contractions to 411,048,920. The rest of a run's time is
    mostly the template load, 4.3 s of 5.5 on front0's source, in SHA-256
    and hash-consing: a lever for a cache of verified templates, not a
    jet.

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

## 22. Frame traces for the hider census

**Avon observes copy mode's head run for the pure-S paper's hider census;
the census decides.** The census (`fixed_points_hider.py`: `run`,
`descend`, `classify`) runs `f X`, X an opaque passenger, and classifies `f`
by the fate of the X-headed items. It needs more than an endpoint: the frame
length and the passenger's seat at every step, counts its defect and y-step
lemmas use, and the frames at confirmed record times for the fold
certificate and the descent. `--trace-frame` gives these (`docs/RUNTIME.md`,
"Frame traces"); the verdicts, the fold lookup and the descent stay in the
census's Python, called unchanged (`tests/hider/client.py`). A certified
exit is a proof only through the census's own certificate.

**What the census takes from Avon, and what it checks.** Avon reports
the run's exit, the confirmed records, and at each its lowest X-headed
position and whether an X-headed item sits at L-1. The client checks every
position a decision rests on against the dumped frames before it asks the
certificate: the item at the reported position is X-headed, none below it
is, and the mint's X-headedness equals the L-1 flag. Records are strict
future minima, so a record's positions 1..L-3 are never touched again, and
the check grows with the frame, not the run. A falsified position or flag
either fails the check or leaves the verdict unchanged (1,776 falsified
records tried on size 10). The record times and the exits HALT-X and OPEN
are taken from Avon's run unreplayed; on sizes 1 to 12 they equal the
census's own, and past 12 they are Avon's reduction, not new evidence.

**The horizon's edge.** The census stops at an OPEN before stepping; Avon
takes the opening contraction, which leaves X at the head. A term that
opens at step H-1 so spends the last fuel, and Avon reports `FUEL H OPEN`:
the exit is OPEN, at step H-1, as the census's. Trace parity at horizons
1 to 21 holds this edge (`make hider-check`); before the fix, 80 of the
2,056 terms of size 1 to 9 differed at horizon 5. At horizon 600 no term
of size 1 to 16 opens at step 599: the census of sizes 13 to 16, rerun
with the fix and the position checks, gives the counts it gave before,
every term classified and every check passed.

**The frame is copy mode's argument slots.** The census's frame `[u_1 .. u_L]`
is the S head's arguments, `u_1` at the x-seat; a step pops `(x, y, z)` and
pushes `spine(x) ++ [z, y·z]`. That is `run_copy`'s S contraction on the
slots `stk[base..top)`, `u_1 = stk[top-1]`, so the trace is a hook beside
the census's (§6.7), called before each S contraction of the head run.
Positions count from the end, 1 the last item.

**It costs what the run costs.** These terms become DAGs within a few
hundred steps, and anything recursive over paths is exponential on them. A
trace run never collects, so every application's children are older than
it, and the per-node facts -- X-headed, contains X, sigma (the X-headed
items among the head's arguments) and arity -- are filled in index order
on demand. A step changes only the slots above its top three, so prefix
counts over the slots are recomputed only there; the passengers are found
by binary search on them, and the defect is a difference of two prefixes.
A 10⁵-step run is linear (`tests/test_trace.c`).

**Frames go out as a node table, shared.** A frame printed as a tree would
unfold the DAG; a dump prints each node once per term, children first, and
the frame as node ids, and the DAG input form (`dag ... @root`) takes a
record mint back for the descent's sub-run in its size. Dumps at the
confirmed records need the records first, so Avon runs such a term twice:
copy mode is deterministic and these runs never collect, so the node ids
of the two passes are the same.

**Parity, 2026-09-30** (`make hider-check`, the paper's scripts at
`HIDER_SCRIPTS`). `avon enum` gives the census's closed terms in its order
for every size to 12; on all 82,500 closed terms of size 1 to 12 (the
58,786 of size 12 among them), horizon 600, Avon's trace of `f X` equals
the census's run line for line -- length and X-headed positions against
its `hist`, the depth, defect, event and front arity against the
definitions -- and its exit and step; the census through Avon gives the
census's verdict, exit and trail; and the five named cases hold, through
both.

**The defect count is the paper's check of its defect lemma, through
Avon.** The lemma says D never falls along a level, and is at least 1 for
ever after a y-step; the paper checks it on every closed term of size
<= 11 (`fixed_points_fold.py`, mode `defect`). `--defect` keeps that
check's count beside the trace: D along the run while there is exactly one
X-headed item and it is not at the x-seat, the falls, the y-steps, the
steps after the first y-step with D = 0, and the confirmed records after
it, with those of D >= 1. It reads the D the trace already keeps, so it
costs nothing more than the run. On every closed term of size <= 11 the
count equals the one the definitions give from the trace lines, term by
term, and the totals equal mode `defect`'s, run unchanged: 23,714 runs,
2,955,501 steps, no fall, 8,914 y-steps, 6,029 confirmed records after
one, every one with D >= 1. `S a X S` keeps D = 0 after its y-step, as
the lemma's remark has it: the stack item it absorbs is not a mint.
