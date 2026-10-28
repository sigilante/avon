# Subject knowledge analysis, for SKI

A plan, written 2026-10-28: what Afonin's subject knowledge analysis (SKA) does for
Nock, what Avon already has of it, and what Avon takes next. The two articles:

- K. Afonin, "Subject Knowledge Analysis", *Urbit Systems Technical Journal* 3.1
  (2026), <https://urbitsystems.tech/article/v03-i01/subject-knowledge-analysis>.
- K. Afonin, "Nock Compilation (Subject Knowledge Analysis II)", *UST J* 3.2,
  <https://urbitsystems.tech/article/v03-i02/nock-compilation-subject-knowledge-analysis-ii>.

Section numbers such as §6.9 refer to `DESIGN.md`.

## 1. What SKA does for Nock

**Every Nock call is an eval, and SKA finds the ones whose code is known.** Nock 2
runs a formula computed at run time, and Nock 9 is Nock 2 over an arm pulled from a
core, so no call target is static. In practice the formula-formula is a Nock 0 into a
known subject or a quoted Nock 1, so the target is almost always knowable.

- *A partial interpreter.* SKA runs the formula over a partly known subject, a `sock`:
  a mask of known parts beside their data. Nock 0 and 1 give known results; Nock 3, 4
  and 5 give unknown ones; Nock 6 intersects its branches; Nock 2 with a known formula
  enters the callee.
- *A ska-function.* A known formula with the subject masked to the parts used as code,
  by it and its callees. Two subject-formula pairs that agree under the mask are one
  function, so the analysis is reused, and a call to one becomes a direct call with its
  jet matched at compile time.
- *Loops.* The first article finds strongly connected components as it goes, as
  Tarjan's algorithm does, guesses each loop's subject, and redoes the component when a
  guess fails; that cost grows exponentially with the depth of nesting. The second
  recasts the call graph as the least fixed point of the partial evaluator, reached by
  Kleene iteration over a worklist, and keeps the chain finite three ways: a call whose
  subject nests under a caller's with the same formula is recursion, returned unknown;
  a consed noun is never itself used as a formula; and a subject that embeds a
  caller's homeomorphically is generalized to the two's most specific generalization.
- *Compilation.* Each function compiles to SSA with basic-block arguments, walked
  backwards (destination-driven), and passes its callees only the axes they read
  unconditionally; branches merge their data requirements by the most specific
  generalization.

## 2. What Avon already has, in SKI terms

**A closed SKI term means the same thing anywhere, so SKA's main problem shrinks to one
place.** A Nock battery's meaning depends on its subject; a closed term's depends on
nothing (§21.3). Avon needs no masks and no subject equivalence: a term is its own
identity.

| SKA | Avon |
|---|---|
| a ska-function: known code, recovered | a template (§6.9): the compiler's rule, checked by abstracting its body again to its key |
| a direct call | a template fire: the key meets its arguments and its body is written over them, one step |
| jet matching at compile time | `av_jets_match` at load: a node is a jet's when it is the jet's term, tree for tree; dispatch is a tag test |
| the partial interpreter over unknowns | residual jets (§6.5): `g X₁ … Xₖ` on fresh atoms until an atom reaches the head, arity found by running |
| the subject mask | none: a term is closed |
| cached analysis, made persistent (the first article's future work) | not needed: the load's cost was the matcher's (§3) |

**The one place left: a formal at a body's head.** Inside a template's body, a formal
applied to arguments is a call whose target arrives as an argument: a Scott case on a
constructor, a continuation, a function passed in. That is SKA's indirect call. Where
the argument is a known function, SKA's answer applies: specialize the caller on it, so
the call is direct.

## 3. Step 1: the template load (done 2026-10-28)

**The load's cost was the matcher, not the template file, and it is gone.** WORKLIST
item 1 named the load, 4.3 s of a 5.5 s run on front0's source, and proposed a cache of
verified templates. A profile of a one-line source showed where the time went:

| front1 on a one-line source, master `298c252` | sampled |
|---|---:|
| the run | 3,432 ms |
| `av_jets_match`, matching the program | 2,012 ms |
| of it, SHA-256 of every program node | 1,918 ms |
| loading the template files: parse, hash-cons, check | 639 ms |
| binding the templates to the program | 288 ms |

`av_jets_match` hashed every node of the program with SHA-256 to propose candidates,
then confirmed each by tree identity. It now proposes nothing: it canonicalizes the
jets' terms once into a table of trees, and looks each program node up by its
children's canonical ids, adding none. A subtree no jet's term holds has no id, nor has
anything above it.

- *The same jets.* Every jet's digest is its term's: each registration computes it, or
  checks the term against it, and debug builds assert it in `jet_entry_for`. One digest
  holds one term, so two jets never share a tree, and the tree finds the jet a digest
  lookup would. A digest no longer takes part in matching at all, so a term built to
  collide with a jet's digest cannot pass for it (`AUDIT.md` item 8).
- *Kept in the arena.* The interpreter jet matches on every fire and a kernel on every
  poke, so the dictionary lives in the arena, grows as jets are added, and survives
  collections: its ids name trees (a leaf's is its atom's), and only its memo of nodes
  is dropped.
- *The cache was not needed.* What is left of the load is the proof itself: each
  referenced term checked against its hash and each template against its key. A cache
  keyed by the files' contents would hash 123 MB to skip it, and one keyed by anything
  less would trust the file system.

**Results, 2026-10-28.** Avon `d8baad7` against master `298c252`, front1 with
templates and data jets (SKIjack `b0b980a`), `avon front0` alone, wall clock: the best
of three runs for the two sources, one run for the fixed point. Every output is the
same byte for byte, and every count:

| run | master | the matcher by trees | peak, master | peak |
|---|---:|---:|---:|---:|
| a one-line source | 4.0 s | 1.4 s | | |
| front0's source, 33,814,092 contractions | 5.1 s | 2.4 s | 1.66 GB | 1.43 GB |
| front1's fixed point, 1,529 names, 411,048,920 contractions | 14.4 s | 11.3 s | 1.74 GB | 1.43 GB |

front1 against Python's front end on the corpus and every edge program, 504 in all,
agrees on each with templates and data jets, and with `--fix` too. The match no longer
holds a digest for every program node, and the peak falls by 0.2 to 0.3 GB. `tests/test_jets.c` falls from 23.6 s to 14.5 s under ASan, and
`tests/test_interp.c` from 3:46 to 2:12, since the interpreter jet matches on every
fire. Of a one-line source's 1.3 s of user time, 0.9 s is what the profile put in
loading the templates, which checks each, and binding them.

## 4. Step 2: the measurement (done 2026-10-28)

**`--jet-stats` now counts each template instance by its body's head.** The head of the
body's root is one of three things:

- a closed term: a call whose target is known, a direct call;
- a formal: a call to whatever that argument holds, the indirect call;
- nothing: the body is a lone formal or closed term.

For a formal at the head it records what the argument held when the instance was made:
a constructor with its fields (a case), a numeral or list word, a known function short
of its arguments (a template or residual jet), S, K or I short of theirs, a head holding
all its arguments (not yet a value), or anything else. For a known function it records
the site: caller template, formal, callee and the arguments the callee held. With
`--jet-stats` a case never joins its instance (§6.10), so every case is counted.

**Results, 2026-10-28**, the same sources with this change's `--jet-stats`, each output
the same as without it:

| | front0's source | | the fixed point | |
|---|---:|---:|---:|---:|
| template instances | 12,118,784 | | 149,696,475 | |
| head a closed term: a known call | 582,118 | 4.8% | 4,185,739 | 2.8% |
| head a formal | 11,510,157 | 95.0% | 145,418,139 | 97.1% |
| no application | 26,509 | 0.2% | 92,597 | 0.1% |
| *what the formal held* | | *of formals* | | |
| a constructor with its fields: a case | 5,903,876 | 51.3% | 84,049,457 | 57.8% |
| a head with all its arguments: not yet a value | 3,641,466 | 31.6% | 48,260,877 | 33.2% |
| a known function | 903,538 | 7.8% | 4,250,611 | 2.9% |
| S, K or I short of their arguments (zero among them) | 615,108 | 5.3% | 3,739,810 | 2.6% |
| a numeral or list word | 440,455 | 3.8% | 5,079,987 | 3.5% |
| an atom, a native operation or Y | 5,714 | 0.0% | 37,397 | 0.0% |
| *of the known functions, completed by the head: a call made at once* | 56,940 | | 266,162 | |

**Almost every call through a formal is a case or a thunk, and almost no known function
is called there.**

- *Cases*, 51 to 58%: a constructor meets its continuations. §6.10's join already
  dispatches these in the instance's step: 6,909,309 cases joined on front0's source in
  a run without `--jet-stats`.
- *Thunks*, 32 to 33%: the formal holds an application not yet evaluated, which the
  reducer evaluates next at the head. No specialization removes that work; it is the
  strictness question of `WORKLIST.md` item 1.
- *Known functions*, 3 to 8%, at 28 sites, the top 10 holding 98.5%. Only 6.3% of them
  are calls the head completes. The rest are partial applications the instance builds,
  and one site holds 90% (810,911 instances on front0's source, 3,817,563 on the fixed
  point): a template `λa b c d e. a b c e`, its first formal holding itself with one
  argument, short of its five.

**That site was front1's tokens, past the arity cap.** The template is a lifted branch
of `forceAll`, and the first reading of this table took the site for `forceAll`'s own
chain, but a jet is its tree: the branch's key
is `S (K (S (K K)))`, a layer `L` with `L x b c d = x b c`, and a probe of the site's
argument found `L` 32 deep over `T`. front1's `tok` is a 34-way sum; its constructor
`TName` is `L³³ T`, `λx c₀ … c₃₃. c₀ x`, and takes 35 arguments, past the cap of 32,
so no `tok` constructor was a template. A case on a token peeled the 33 layers one
instance each, every `L` inside the constructor's term a jet node of the branch's key.
The cap is now 64 (§6.8), and the 34 constructors dispatch as templates:

| front1, master `95b260c` against the cap of 64 | before | after |
|---|---:|---:|
| templates accepted | 2,262 | 2,296 |
| front0's source: contractions | 33,814,092 | 32,817,600 |
| front0's source: template instances | 12,118,784 | 11,268,473 |
| front0's source: wall clock, best of three | 2.35 s | 2.32 s |
| the fixed point: contractions | 411,048,920 | 406,467,740 |
| the fixed point: wall clock, one run | 11.9 s | 11.8 s |
| known functions at a formal, front0's source | 903,538 | 21,683 |

Every output is the same. The contractions fall 3.0% and 1.1%; the wall clock is within
the runs' spread, since an `L` instance was cheap. A case still dispatches once either
way: before, the last layer's `T x c₀` was itself a dispatch.

## 5. Step 3: specialization on known functions (decision: not taken, measured 2026-10-28)

**At most 266,162 calls on the fixed point would become direct, against its 411,048,920
contractions: 0.06%, so specialization is not built for front1.** The design stands for a workload that
passes known functions through formals and completes them; `--jet-stats` shows whether
one does. A template specialized on a known function argument makes its indirect call
direct, and its check is the one templates already pass. Take a template `g` of `k` formals
whose head formal `i` receives a known function `f` holding `m` arguments `c₁ … cₘ`.

- *The specialized template.* Its key is the closed term `g` applied to `f` in position
  `i`, abstracted over the other formals and the `m` captured arguments; its body is
  `g`'s body with `f c₁ … cₘ` at formal `i`, and `f`'s body instantiated there in place
  of the call. Avon checks it as every template: abstracting the body over its formals
  must give its key, node for node (§6.9), and the instance is a weak reduct of the
  key applied, so values and normal forms are the unjetted ones.
- *Where it fires.* A site found by step 2 is a pair of templates, not a program
  location: the program builds `g (f c₁ … cₘ) …` at run time. Matching is therefore at
  the fire: a template fire whose head formal holds `f` with `m` arguments takes the
  specialization, a lookup on `(g, i, f, m)`. Nothing is rewritten in the program.
- *Termination.* Specializing `g` on `f` may expose `f`'s own head formal holding
  another known function, and so on. SKA II's devices bound it: a specialization whose
  pair is already on the chain is recursion and is not unfolded; nesting depth has a
  cap; and the set of `(g, i, f, m)` is finite, since every `g` and `f` is a template
  of the loaded set.
- *What it saves.* One instance and the cells the inner call's spine would write, per
  site fire: on front1, at most the 56,940 and 266,162 calls step 2 counts.
- *The proof.* A specialized template is a template: lean-ski's
  `(formals, open body)` with the same exclusions, so the supercombinator proof jets
  (§18.1) cover it unchanged.

## 6. Later

- **Discovery without a compiler.** Every prefix of an atom run is count-exact, not
  only its end (§6.5): `copy` reduction of `g a₁ … aₖ` reaches `r[aᵢ/Xᵢ]` after any
  number of the run's contractions. So a residual may stop at a call into another known
  function instead of inlining it, giving functions with call edges, found by running,
  for programs no compiler hands templates for. For the pill (§20.3), front1 emitting
  templates as it compiles is cheaper: it holds each rule before abstraction, and today
  emits none.
- **Data requirements and compiled bodies.** SKA II passes a callee only the axes it
  reads on every path. In SKI the analogue is the formals a template cases on along
  every path, so its instance could take their fields directly: §6.10's case of a
  known value, made static. Step 2 puts the cases at 51 to 58% of formal heads and
  the thunks at 32 to 33%, so this, with `WORKLIST.md` item 1 (strictness), is where SKA's
  second article points for front1. Compiling bodies to straight-line code is §6.9's
  "compact template form".

## 7. Risks

- Step 2's runs never join a case (§6.10). A join changes how a case's instance is
  written, not its head, so the counts are a plain run's; the wall clock is not.
- The measurements are front1's alone. SKIlark's interpreted programs and the corpus
  pass functions differently, and step 3's verdict holds only for the workloads
  measured.
- The specialization key is a site by templates, not by program location: two callers
  that pass the same function share a specialization, and one that passes many
  functions gains little.
- A known function at a formal can be a partial application built at run time from
  values; specializing on the function captures its arguments as formals, so the
  instance still writes them.
