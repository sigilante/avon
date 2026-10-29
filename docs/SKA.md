# Subject knowledge analysis, for SKI

A plan, written 2026-10-28 and every step decided by 2026-10-29: what Afonin's subject
knowledge analysis (SKA) does for Nock, what Avon already had of it, and what Avon took
from it. The two articles:

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

**The other two classes take no new mechanism, measured 2026-10-28** on front0's source
at the cap of 64, with probes not kept in the source:

- *Cases on a value are all joined already.* A case template's instance whose formal
  holds a value joins its dispatch (§6.10) whenever it can: 6,516,064 joinable at the
  last sample, 6,516,064 joined, and 6,982,147 joined over the run. Taking a case's
  fields straight into the instance, along every path, is what the join does.
- *Thunks are calls the reducer makes next.* Of the unevaluated applications a formal
  held, 3,360,437 of the first 3,500,000 are templates with all their arguments,
  131,932 S, K or I redexes and 7,631 constructors holding continuations as well. Each
  is evaluated as soon as the instance is written, at the same count; forcing it first
  could only let the case join, and a join writes the body's other applications as an
  instance does, leaving only the spine, which deferred roots (§6.13) already leave
  unwritten.

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

## 6. Step 4: templates discovered (built 2026-10-28)

**`--discover` finds templates in a term with no compiler's files, by inverting bracket
abstraction.** The forward rules are `hc_abstract`'s:

    [x] x = I    [x] M = K M (x not in M)    [x] (M x) = M (x not in M)
    [x] (M N) = S ([x] M) ([x] N)

so a body `b` with `[x] b = t` is `x` for `I`, `M` for `K M`, and for `S P Q` the bodies
of `P` and `Q` applied, when the forward rules take that application back to `S P Q`;
otherwise `t x`, which is `t` by η and no formal at all.

These are Hindley and Seldin's abstraction, clauses (b), (a), (c) and (f) of their
Definition 2.18 (*Lambda-Calculus and Combinators*, 2008), lean-ski's `abs` clause for
clause. The η clause (c) is what makes inversion ambiguous: without it, Curry's
weak abstraction `[ ]w` (their Definition 9.20) would give every key one body, at the
cost of longer keys (their Remark 2.23). Curry's `[ ]β` admits (c) only where the term
it returns is functional, `S X Y`, `S X`, `K X`, `S`, `K` or `I` (their Definition
9.6), and so inverts the translation to λ exactly (their Remark 9.27). Avon keeps the
compilers' `[ ]η`, since a key must be the term the compiler emitted, and resolves
the ambiguity as below.

- *Every S or K application of the program is a candidate key.* Peeling formals until
  only η is left gives its arity and body. The memos are per formal and shared by every
  candidate, over the hash-consed program, so a subterm is inverted once per formal.
- *η erases a formal its body applies last*, as `[g] (S (K f) g)` is `S (K f)` and
  `[y] (K y)` is `K`. A partial `S P`, `S` or `K` meets only η, but applied to the formal
  it inverts at the next, so such formals are kept pending and taken with the next one
  that inverts: B's key `S (K S) K` comes back as `λf g x. f (g x)`.
- *The abstraction decides.* Each body goes through the loader's own check, abstracted
  again to its key node for node, with η-templates, open bodies and leaf keys skipped
  as before. A key whose instance saves fewer than two contractions is discarded.
- *Y is left to `--fix`.* Curry's Y is an abstraction too, and discovery finds its key.
  With `--fix` on, discovery skips it, so `--fix` registers Y and unfolds it in one step:
  `tests/data/nats` to head normal form falls from 8,170 steps to 7,193, with 478
  unfoldings.
- *What it cannot see.* The compiler knows which closed subterms of a body are other
  rules. Inversion does not: it may take a reference apart, as `S I (K x)` for `T x`,
  inlining it, S and K over formals included. The body is still a weak reduct of its
  key, so the answers stay right. Telling a reference by its being shared, by a
  combinator at an open head, or by its firing in a run (§8) each made discovery slower:
  inlining a reference is not where its templates lose to the compiler's.

**Results, 2026-10-28**, share mode to normal form, every normal form SKI's:

| program | SKI | discovered | the compiler's templates |
|---|---:|---:|---:|
| the corpus, the 43 halting runs | 640,853 | 145,620 | 63,774 (BENCHMARK, "Templates on the corpus") |
| `tests/data/nats` | 58,140 | 8,170 | 7,789 |
| `tests/data/lists` | 5,380 | 1,010 | 787 |
| `tests/data/listops` | 5,523 | 907 | 723 |
| `tests/data/bits` | 9,090 | 1,461 | 726 |
| `tests/data/quot` | 84,808 | 11,859 | 10,194 |
| front1 on a one-line source, with `--data` | 1,693,922 | 176,951 | 69,410 |

- *Recall.* On front1, discovery keeps 25,695 templates, none refused, among them
  2,274 of the compiler's 2,298 keys, 2,168 at the compiler's arity; the rest are
  pieces of larger abstractions, and sub-abstractions the compiler never named.
- *Time.* Discovery canonicalizes the whole program: front1 on a one-line source takes
  2.3 s with it, 1.2 s with the compiler's files and 0.07 s as SKI.
- *Its limit.* front1 on front0's source passes 3.5 GB between 40 and 100 million
  contractions, where with the compiler's templates the whole run is 32.8 million in
  1.43 GB. Stage B needs its templates' real bodies, as DESIGN §20.3 records of the
  fixed point without templates (past 12 GB), so front1's heavy runs keep the
  compiler's files.

## 7. Step 5: front1's own templates (built 2026-10-28)

**front1 hands over its templates itself, so a pill holding front1 needs no Python for
them.** Its expander already holds each rule's template at the moment it abstracts it:
`ruleTm` takes the formals, the body with each reference a variable numbered past them,
and the references' terms, then abstracts and substitutes.

- *front1* (SKIjack #40). `ROk outs tpls`: the second field is each rule's template,
  made by `ruleTp` and `inlT`, which mirror `ruleTm` and `inl` step for step over the
  rule map from the memo the terms were made with; a lifted rule inside a body gives its
  own. `sucR`, the prelude's successor, became a rule of its own, so a body names it as
  `skijack.templates` does; the terms are the same.
- *Laziness.* Only `front0 --emit` reads the field. A run that never reads it never
  makes it: a plain run's contractions are unchanged, and `tests/test_front0.c` reads a
  result whose templates field diverges.
- *Avon* (#91). `front0 --emit=OUT` writes the field as `OUT/templates.tsv` and
  `OUT/template_terms.tsv`, each key and reference once and no η-template, and every
  name's term as `OUT/terms.tsv`. The loader then checks each body against its key as
  it checks Python's.
- *Parity.* For its own source front1 emits all 2,326 of `skijack.templates`'
  templates, key, arity and body alike. Every accepted corpus program emits Python's;
  the four scry and namespace programs give one key more each, a rule front1 makes
  where Python builds the same term without one. `run1 --emit` checks both, and
  `front1-check` runs it.

**Results, 2026-10-28**, front1 with SKIjack #40, `avon front0 --data`, wall clock the
best of three (one run for the fixed point), every output the same:

| run | SKI | `--discover` | Python's templates | front1's own |
|---|---:|---:|---:|---:|
| a one-line source: contractions | 1,693,941 | 176,960 | 69,410 | 74,411 |
| a one-line source: wall clock | 0.04 s | 1.93 s | 1.26 s | 0.81 s |
| front0's source: contractions | | past 3.5 GB | 32,817,600 | 32,946,393 |
| front0's source: wall clock | | | 2.23 s | 1.77 s |
| the fixed point: contractions | | | 410,925,316 | 412,552,742 |
| the fixed point: wall clock | | | 11.5 s | 11.3 s |

- *Faster to load.* front1's `template_terms.tsv` is one DAG shared across its
  references, 21 MB against Python's 123 MB.
- *Contractions 0.4% apart.* Where two rules compile to one term, Python's file lists
  both and its loader keeps the first line's body; front1 keeps the first rule its rule
  map yields. Both bodies are the key's, and their instances differ.
- *What emitting costs.* front1 compiling its own source with `--emit` takes
  566,401,252 contractions, 14.7 s and 1.44 GB: the templates' pass redoes each lifted
  rule's abstraction. A pill emits once per program it compiles.

## 8. The last two levers, measured (2026-10-29): neither taken

**Discovery told references from plumbing by running: twice the steps.** The cue
syntax lacks is which closed nodes behave as functions. A run gives it: discovered
templates run once, recording the keys that fired, and discovery runs again keeping
each fired key whole wherever it sits inside another key, a call and not plumbing to
invert. Built on a branch and measured, share mode to normal form, every normal form
SKI's:

| program | `--discover` | with the fired keys kept whole |
|---|---:|---:|
| the corpus, the 43 halting runs | 145,620 | 286,662 |
| `tests/data/nats` | 8,170 | 18,790 |
| `tests/data/lists` | 1,010 | 1,954 |
| `tests/data/listops` | 907 | 2,302 |
| `tests/data/bits` | 1,461 | 3,652 |
| `tests/data/quot` | 11,859 | 29,580 |

Inverting into a reference is not the cost §6 took it for: the body so made inlines
the callee and saves its instance on every call, where a reference kept whole pays a
fire more. With sharing (§6), it is the second cue that names references and makes
discovery slower; the gap to the compiler's templates is not in references. The code
is not kept.

**Compiled template bodies: the writes they would keep are the cost.** A profile of
front1's fixed point (4,642 samples, master `ed2b360`) puts 1,741 of them, 37.5%, in
the two functions that write template instances, `case_join` and `tmpl_defer`. An
instance writes its body's open applications, 3.3 on average (86,182,573 over front0's
source's 25,949,842 template fires, weighting each template's open applications by its
fires), each an 8-byte node allocated and written. A body compiled to straight-line
code writes every one of them still; it saves only decoding each operand, a shift, a
mask and a table load beside the node it writes. That is a part of the 37.5% small
enough not to repay a code generator, so the bodies stay instruction lists.

## 9. Risks

- Step 2's runs never join a case (§6.10). A join changes how a case's instance is
  written, not its head, so the counts are a plain run's; the wall clock is not.
- Steps 2 and 3 measured front1 alone. SKIlark's interpreted programs and the corpus
  pass functions differently, and step 3's verdict holds only for the workloads
  measured.
- Discovery's bodies differ from the compiler's where inversion takes a reference
  apart; the corpus and the fixtures bound the cost (5 to 100% more steps than the
  compiler's templates, 2.3 times on the corpus), front1 alone measures 2.5 times.
- The specialization key is a site by templates, not by program location: two callers
  that pass the same function share a specialization, and one that passes many
  functions gains little.
- A known function at a formal can be a partial application built at run time from
  values; specializing on the function captures its arguments as formals, so the
  instance still writes them.
