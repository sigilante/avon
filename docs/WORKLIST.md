# Worklist

What remains, in the order we mean to take it. `DESIGN.md` §11.1 records what is built;
this file records what is next. Each item names its decision state and where its
design lives. Last revised 2026-10-29.

## Done since the last revision

- **The interpreter jet's adequacy, proved in Lean for `whnfF`** (2026-10-29;
  `LEAN-JETS.md` §8). Step 5, the plan's last, is done. `lean/Interp.lean` proves the
  ski-in-ski paper's step and fuel adequacy for the 618-atom `whnfF` the jet serves:
  `whnfF ⟨k⟩ ⟨M⟩` reduces to the encoding of lean-ski's `evalF k M`. Lean prints
  `whnfF` and its constructors, and `make interp-lean-check` requires them to be the
  conformance dictionary's, byte for byte. The other four cores (`wf5Abs`,
  `wf5Omg`, `wfQ`, `wfN`) stay unproved, as approved.

- **Y in one step, proved in Lean** (2026-10-29; `LEAN-JETS.md` §7). Step 4 is done.
  `lean/Fix.lean` proves that a run mixing `--fix`'s rewrite with weak steps stays
  convertible with the plain run, so a normal form it reaches is SKI's (`fix_normal`,
  which DESIGN §6.11 had only argued), and Y's simulation up to lean-ski's `Tr`
  with Y a jet at the compiler's recursion sites (`fix_simulation`), decided for
  lean-ski's compiled `sum` and `loop`. Under Avon's tree identity the simulation is
  false, for a closure that happens to compile to Y (`closure_spells_Y`,
  `first_B_false`), so B takes Y as a jet, as approved. `make fix-lean-check` runs it, and weekly. Next: the
  interpreter jet's adequacy theorem (step 5).

- **Templates, proved in Lean** (2026-10-29; `LEAN-JETS.md` §6). Step 3 is done.
  `lean/Templates.lean` models `tmpl.c`'s load check and `tmpl_instance`, proves the
  check is lean-ski's bracket abstraction and an accepted template's fire a reduct
  of its redex (`template_fire`), and replays the loader with SHA-256 digests in
  Lean: `make templates-lean-check` requires its counts to be Avon's on the five
  shipped sets and eight changed copies. The plan's "replace the check in C" was
  dropped: discovery makes templates at run time, so the check stays in C, now
  proved. Next: Y's simulation theorem (step 4).

- **Lists and bit strings, proved in Lean** (2026-10-29; `LEAN-JETS.md` §5). Step 2
  is done. `lean/Words.lean` now proves all fifteen word operations' terms (numerals,
  `len` .. `drop`, `beq`, `bget`, `ideq`) and models `list_fire` and `bits_walk`,
  proving them sound. Lean prints every pin `words.c` holds, byte for byte the old
  ones. The proofs corrected a claim: a bit-string fire that stops early leaves a
  term convertible with the redex, not a reduct of it, since Curry's Y reaches its
  knot only one way; `reduce.c` and DESIGN §6.10 now say so. Next: templates checked
  by Lean (step 3).

- **The numeral words, proved in Lean** (2026-10-29; `LEAN-JETS.md`). The plan for
  proving Avon's C jets is `docs/LEAN-JETS.md`; its step 1 is done. `lean/Words.lean`
  proves each of the seven numeral operations' pinned terms reduces to its operation's
  numeral on every pair of Scott numerals, and `word_fire`'s `uint64_t` arithmetic
  gives the same values. Lean prints the pins as `src/word_pins.h`, which `words.c`
  now includes; `make words-lean-check` reruns the proofs and compares the print, and
  joins the weekly lean-ski job. Next: list words and bit strings (step 2).

- **Discovery leaves Y to `--fix`** (2026-10-29; `SKA.md` §6). Discovery found Y's own
  term a key, so `--discover --fix` refused to start ("Y is already another jet"). With
  `--fix` on it now skips Y's key: `tests/data/nats` to head normal form falls from
  8,170 steps to 7,193. The README, the tour and DESIGN §6.9 now name all three
  template producers: Python's expander, front1 and discovery.

- **SKA's last two levers, measured** (2026-10-29; `SKA.md` §8). Discovery that keeps
  the keys a run fired whole, as references, takes the corpus's 43 halting runs to
  286,662 steps against 145,620: inlining a reference saves its instance. Compiled
  template bodies would keep the cost: 37.5% of the fixed point's samples write
  instances, 3.3 open applications each, and straight-line code would still write them.
  Neither is taken. The stats build crashes on front1 runs, as it did before this arc
  (small item 8).

- **front1's own templates** (2026-10-28; avon #91, SKIjack #40; `SKA.md` §7). front1's
  `ROk` carries each rule's template as its expander abstracts it, made only when read,
  and `front0 --emit` writes them as the files `--templates` reads: for its own source,
  all 2,326 of `skijack.templates`', key, arity and body alike. With them front1 runs
  front0's source in 1.77 s against 2.23 s with Python's file, every output the same. A
  pill holding front1 has its templates with no Python.

- **Templates discovered, and the levers measured** (2026-10-28; `SKA.md` §4 and §6).
  `--discover` inverts bracket abstraction to find templates in a term with no
  compiler's files, each body checked against its key as a loaded one is. The corpus's
  43 halting runs take 145,620 steps against SKI's 640,853 and the compiler's
  templates' 63,774, every normal form SKI's; front1's heavy runs, past 3.5 GB with
  them, keep the compiler's files. Of the levers step 2 left: every case on a value is
  joined already, and the thunks a formal holds are template calls the reducer makes
  next, so neither takes a new mechanism.

- **front1's tokens dispatch: the arity cap is 64** (2026-10-28; `SKA.md` §4, DESIGN
  §6.8). The 90% site of step 2's known functions was not `forceAll`'s chain but `tok`,
  a 34-way sum whose constructors take 34 and 35 arguments, past the cap of 32: a case
  on a token peeled 33 layers, one template instance each. At 64 the 34 constructors are
  templates and dispatch: front0's source 33,814,092 contractions to 32,817,600, the
  fixed point 411,048,920 to 406,467,740, every output the same. `word` in SKIlark now
  has room for 63 one-field constructors.

- **Subject knowledge analysis: the plan, the template load and the measurement**
  (2026-10-28; [`SKA.md`](SKA.md)). `SKA.md` maps Afonin's two SKA articles onto Avon:
  templates are its recovered functions and the load-time matcher its compile-time jet
  matching, and a formal at a template body's head is the one indirect call left.
  - *The template load.* It was the matcher hashing every program node with SHA-256.
    `av_jets_match` now matches by trees alone, against a dictionary of the jets'
    terms the arena keeps (DESIGN §6.5). front0's source runs in 2.4 s against 5.1, the
    fixed point in 11.3 s against 14.4, every output the same. No cache was needed.
  - *The measurement.* `--jet-stats` counts template instances by their body's head
    and what a formal there held. On the fixed point 97% of instances call a formal:
    58% of those a case, 33% an unevaluated application, 3% a known function, and the
    head completes only 266,162 such calls. Specialization on known functions (`SKA.md`
    §5) is not taken.

- **Stage 8's prelude gap** (2026-10-28; SKIjack #39). front1 installs `natDiv`,
  `natRem` and the list operations as the expander's prelude does; the expander no
  longer gives an operation installed for another's use the program's name. Every
  corpus program, all 482 edge programs, 1,300 random and 500 typed programs agree,
  and the fixed point covers 1,529 names. `tests/pins.sh` moves SKIjack to the merge.

- **Drivers, durably: `avon boot --drivers`** (2026-10-28; DESIGN §9.2). A kernel run
  in a pier, each answer logged as its payload before its reply is applied; reopened,
  the run replays from snapshot 0 through the walk, writing nothing again, and goes
  live at the first request the log does not answer. `tests/drivers_check.sh` runs
  its 17 worlds in a pier as well as in memory, reopens each finished pier, and kills
  echo mid-run and resumes it (53 runs); `tests/test_drivers.c` stops runs at every
  request and resumes them.

- **Data jets for Stage B's hot spots: bit strings** (2026-10-28; DESIGN §6.10, "Bit
  strings"). With templates and data jets a third of front1's run is bit strings, its
  names and its stores' keys. Equality, the lookup in a trie the bits key, and names'
  equality run natively where a program's function is front1's term, pinned and
  admitted by running, reading only operands that are values already. front1's fixed
  point: 633,573,940 contractions to 411,048,920, 53 s to 47 s, every hash the same.
  `--jet-stats` counts each template's fires and each constructor's dispatches. The
  template load, then 4.3 s of a 5.5 s run on front0's source, is done above.

- **Drivers, and SKIlark's I/O through them** (2026-10-27; avon #78, SKIjack #33 and
  #34, SKIlark #30 and #31). `avon run --kernel` runs a kernel as a program, performing
  the standard cards (DESIGN §9.2); SKIjack's reference drivers are the oracle, released
  in 0.2.5. SKIlark's stage 15 door makes a program or a Joy file such a kernel, its
  writer and reader in SKI. `tests/pins.sh` moves SKIlark to `1025e36`; the fixtures are
  as before (fixtures-check, 236 files), since the door adds nothing the exporters
  write.

- **SKIlark's I/O words and SKIjack 0.2.4** (2026-10-26; SKIlark #27 to #29, SKIjack
  #30, #31). SKIlark gains `put putch putchars get argc argv getenv clock abort quit`:
  an I/O word ends a run with `RIO`, the word, the stack and the rest of the program, and
  a host answers it. `result` gains that constructor, so the workloads' manifest reads
  `RIO/3` beside `RVal/1 RErr/0 RTime/0`. SKIjack 0.2.4 adds `SKIJACK_AVON_STRATEGY=share`.
  `tests/pins.sh` moves SKIjack to `c319619` and SKIlark to `7376632`; the fixtures
  regenerate from them (fixtures-check, 203 files). The workloads use no I/O word and take
  the same 959,160 contractions; `step` is 76,646 atoms in the census, from 75,673, whose
  smoke row is re-recorded; `jets/joy.tsv` keeps 74 terms.

- **SKIlark's stages 9 to 11** (2026-10-26; SKIlark #24 to #26). SKIlark gains the
  reference's remaining pure words: `div pick condlinrec condnestrec casting` derived, and
  `compare name body intern strtol format` as `ext` words, `name`'s, `intern`'s and the
  number-text words' code coming only with programs that use them. `tests/pins.sh` moves
  SKIjack to its 0.2.3 release (`c57bb81`) and SKIlark to `ec28dce`; the workloads,
  which use none of them, take the same 959,160 contractions, `step` 632 a call and
  75,673 atoms in the census, whose smoke row is re-recorded; `jets/joy.tsv` keeps 74
  terms.

- **List words** (2026-10-25; skijack #27, #28). Data jets hold closed Scott lists as
  chains of list words, the numeral words' shape (`AV_JET_LIST`, its length in the id
  field, its term the cell), dispatching as a two-field constructor, fused as one; and
  run skijack's `listLength`, `listAt`, `listAppend`, `listTake` and `listDrop`
  natively on them, each pinned by term and admitted on small lists.
  `tests/data/listops` and `test_data` check them against their terms; `tests/pins.sh`
  moves SKIjack to `0640fb4`. DESIGN §6.14 records it.

- **SKIlark's `ext`: `size` and `at` in the kernel** (2026-10-25; SKIlark #21). `word`
  gains `Ext ext`, its thirtieth constructor, and `ext` holds the kernel's further
  words in a sum of their own, the first `size` and `at`, which the interpreted form no
  longer derives: `[1 2 3] size` takes 1,895 contractions, from 82,459. Its one-field
  constructors take 31 arguments, under the cap of 32, which `test_workloads` checks.
  `tests/pins.sh` moves SKIlark to `9fa703d`; the workloads, which use neither word,
  take 959,160 contractions, from 941,408; the census and jetstat smoke rows are
  re-recorded.

- **SKIlark divides natively** (2026-10-25; SKIlark #19; skijack 0.2.2). SKIlark's
  `divN` and `remN` call skijack's `natDiv` and `natRem`, which this runtime runs
  natively: `200 200 * 7 rem` takes 138 contractions, from 108,716. `tests/pins.sh`
  moves SKIjack to the 0.2.2 release (`0537d69`) and SKIlark to `0a2e6ea`; the
  interpreted workloads regenerate 136 bytes smaller, at the same 941,408
  contractions, and the census smoke row is re-recorded for `step`'s 57,570 atoms.

- **SKIlark's library words and numbers** (2026-10-25; SKIlark #17 and #18; skijack #25,
  avon #70). SKIlark derives the reference's library words and computes its naturals with
  skijack's operations, which this runtime runs natively on words; skijack gains `natDiv`
  and `natRem`, and Avon runs them. `tests/pins.sh` moves SKIlark to `e3f29f5`; the
  workloads take 941,408 contractions and `joy.tsv` lists 74 terms; the census and
  jetstat smoke rows are re-recorded. DESIGN §6.7, §6.8 and §6.14 take them.

- **SKIlark's sidestep: type tests and sets under the cap** (2026-10-24; SKIlark #11 to
  #13). SKIlark merges its five literal constructors into `Lit item` and gains Joy's
  `typeof`, the type tests, sets of 0 to 63 and a kernel `not`, the complement, with
  no change to Avon: `word` has 29 constructors, so its one-field constructors take 30
  arguments, under the cap of 32. `tests/pins.sh` moves SKIlark to `a53dc73`;
  `tests/workloads/skilark/` and `jets/joy.tsv` regenerate from it (`fixtures-check`,
  193 files). The workloads take 882,928 contractions, from 742,609; `joy.tsv` lists the
  kernel's 28 Joy words of a 29-way sum (73 terms), which `test_workloads` checks Avon
  reads as constructor jets of 30 arguments at most; the census and jetstat smoke rows
  are re-recorded. DESIGN §6.7 and §6.8 take the new workloads, and §6.14 records the
  cap's decision.

- **SKIlark's combinators, characters and strings** (2026-10-24; SKIlark #9 and #10).
  SKIlark's kernel gains `stack`, `unstack`, `Def`, characters and strings, and the
  reference implementation's comparison and truth values; Joy's recursion combinators
  are derived. `tests/pins.sh` moves SKIlark to `eb90896`; `tests/workloads/skilark/`
  and `jets/joy.tsv` regenerate from it (`fixtures-check`, 193 files). The workloads take
  742,609 contractions; `joy.tsv` lists the kernel's 30 Joy words of a 31-way sum (74
  terms), which `test_workloads` checks Avon reads as constructor jets of 32 arguments at
  most, the cap; the census and jetstat smoke rows are re-recorded. DESIGN §6.7 and §6.8
  take the new workloads, and §6.14 plans SKIlark's data jets.

- **SKIlark's lists** (2026-10-23; SKIlark #8). SKIlark's quotations become Joy's lists:
  words are symbols, a fourth kind of stack item, and the kernel adds `uncons`, `null`
  and `small` while `succ`, `pred`, `max`, `min`, `and`, `or` and `not` become derived
  words. `tests/pins.sh` moves SKIlark to `4bf06ae`; `tests/workloads/skilark/` and
  `jets/joy.tsv` regenerate from it (`fixtures-check`, 193 files). The workloads take
  564,740 contractions; `joy.tsv` lists the kernel's 23 Joy words of a 24-way sum (67
  terms), which `test_workloads` checks Avon reads as constructor jets of 25 arguments at
  most, under its cap of 32; the census and jetstat smoke rows are re-recorded. DESIGN
  §6.7 and §6.8 take the new workloads.

- **SKIlark toward Joy in full** (2026-10-23; SKIlark #6 and #7). SKIlark's kernel adds
  Joy's arithmetic on signed integers, truth values, `branch` and `ifte`, and retires its
  own `ifz`. `tests/pins.sh` moves SKIlark to `9d6fb9e`; `tests/workloads/skilark/` and
  `jets/joy.tsv` regenerate from it (`fixtures-check`, 193 files). The workloads take
  558,847 contractions; `joy.tsv` lists the kernel's 27 Joy words of a 28-way sum (78
  terms), which `test_workloads` checks Avon reads as constructor jets of 29 arguments at
  most, under its cap of 32; the census and jetstat smoke rows are re-recorded. DESIGN
  §6.7 and §6.8 take the new workloads.

- **SKIlark on Church fuel** (2026-10-23; SKIlark #4 and #5). SKIlark's kernel bounds a
  run with a Church numeral, the loop's body applied *n* times, in place of a Scott
  numeral computed as it is consumed, so its fuelled runs cost about what its unfuelled
  ones do. `tests/pins.sh` moves SKIlark to `6900741`; `tests/workloads/skilark/` and
  `jets/joy.tsv` regenerate from it (`fixtures-check`, 193 files). The workloads fall from
  928,398 contractions to 333,013, every count `test_workloads` checks; `joy.tsv` loses
  `mul`, which the kernel no longer has (34 terms); the census and jetstat smoke rows are
  re-recorded. DESIGN §6.7 adds the rerun and §6.8's jetstat table takes the new
  workloads: all three dictionaries absorb 40.0% of SKIlark's, up from 37.5%.

- **Inlining by default in Avon's exports** (2026-10-30). The Reduceron ports' `run.py`
  and the exporters of `tests/fixtures/`, `tests/data/`, `tests/kernel/` and
  `tests/drivers/` compile with skijack's inlining pass; `--no-inline` writes what they
  wrote before. The ports' counts with data jets are BENCHMARK "Inlining"'s inlined ones,
  1.12 times faster by geometric mean. Eighteen fixtures regenerate; `test_wire`'s corpus
  is 283 terms (285), `templates-lean-check`'s sets 144 accepted and 78 skipped (137 and
  56), and five smoke rows are re-recorded. `tests/selfhost/` and `tests/zkwords/` keep
  the pass off. skijack's own default, front1 and lean-ski's statements are unchanged.
- **Plain SKI at half rate on OrdList and Taut: the collector** (2026-10-30). They
  collect for 44 to 45% of their time, copying live sets of 21 and 11 million nodes at
  31 to 49 ns a node; without the collector every port runs 57 to 62 million
  contractions a second (BENCHMARK, "Plain SKI at half rate"). A nursery would copy
  long-lived nodes once; not started.
- **The collector forwards in from-space; `--aggressive-heap`** (2026-10-30). A
  collection writes each node's forwarding over it in from-space, an IND whose r is
  `AV_NONE`, so it reads one array and allocates only its to-space. `--aggressive-heap`
  (`reduce`, `batch`, `front0`) grows the arena while the live set passes a quarter of
  it: OrdList's plain SKI collects 27 times, not 59, at 3.5 GB against 2.0. Every count
  and state is the same (`an_aggressive_heap_collects_less_and_agrees`). Timed on
  2026-10-31: OrdList 20.16 s against 29.89, Taut 26.35 against 29.07 (BENCHMARK).

- **lean-ski at `ab92b47`** (2026-10-31). `tests/pins.sh` moves past `b4ba210` by
  lean-ski #67 (`compPChain_complete_log`: the Poseidon2 circuit is complete for
  `p2chain`) and #69 (`compJ_fs_open4ROMMC_fri_sat`, `compP_fs_open4ROMMC_fri_sat`:
  every hypothesis of the jet and Poseidon2 Fiat–Shamir bounds met at once, with salt
  commitments that hide and bind nothing). Lean proofs and documentation only; ski-air
  and every table format are unchanged. The worklist's open Fiat–Shamir item for these
  two circuits is closed: lean-ski#63 proved it.

- **lean-ski at `b4ba210`** (2026-10-30). `tests/pins.sh` moves past `c4cd2f2` by
  lean-ski #66: `p2chain` calls the jet exactly twice (`runP_calls_two`,
  `p2chain_twice`), and the Poseidon2 circuit's Fiat–Shamir theorems take the call
  count, so they hold for it. Lean proofs and documentation only; ski-air is unchanged
  but for a comment. `witness-check` (43 witnesses, 5 open terms; its corpus proofs need
  more than 4 GB), `jet-witness-check`, `probe-witness-check`, `zk-jet-witness-check`,
  `p2-witness-check` and the five `*-lean-check`s pass at the pin.

- **lean-ski at `c4cd2f2`** (2026-10-30). `tests/pins.sh` moves past `paper-v9` by
  lean-ski #64 (witnesses for terms with atoms) and #65 (`p2chain`, two jet calls).
  `witness-check` now runs five open terms through `aircheck`, and `p2-witness-check`
  runs `p2chain`.

- **lean-ski at `paper-v9`, now public** (2026-10-23). `tests/pins.sh` moves to `fb65141`:
  lean-ski's public release, past `paper-v8` by its satisfiability witnesses for the
  hidden-term and composed Merkle-committed bounds and its CI. The five checks the pin
  serves pass there, against a checkout one documentation commit past it. The README and
  docs link lean-ski where they called it not yet public.

- **SKIjack and SKIlark on Avon** (2026-10-22 and 23; SKIjack #20 and #21, SKIlark #1 and
  #2; skijack 0.2.1 on PyPI). skijack's
  `fast_reduce`, where every reduction of both runs, sends its runs to Avon's copy mode
  with `SKIJACK_REDUCER=avon` and `AVON` naming the binary, one `batch --dag` line out
  and one back, or to both, compared, with `check`. Every one of the 15,976 reductions
  SKIjack's suite makes outside its front-end tests agrees with aviary, status, count and
  term; both suites pass under `check` and under `avon`, and each repository's CI runs
  them on Avon. `python -m skilark --reducer avon` runs a program on it; SKIlark requires
  skijack 0.2.1, the release that carries the switch. `tests/pins.sh` moves to SKIjack
  `72fb280` (`v0.2.1`) and SKIlark `bafb6d6`, where `fixtures-check` (193 files),
  `selfhost-check`, `front0-check` and `front1-check` pass. A pin also accepts a
  descendant that changes CI workflows (`.github/`), which no check reads, so both
  masters pass: past the pins they change only READMEs and, in SKIjack #23 and SKIlark
  #3, the workflow that skips prose-only changes.

- **The DAG form out** (2026-10-22; `RUNTIME.md`, "Reducing"). `reduce --dag` and `batch
  --dag` print the term reached as `dag <id>=<rhs> ... @<root>`, each node once, the
  form every command reads; with `--dag`, `batch` answers every line, a term it cannot
  run with `!`. A program keeps one `batch` open and reduces through it with sharing
  kept both ways: SKIjack's `SKIJACK_REDUCER=avon` does. On 27 fixtures, both strategies,
  jets on and off, both stopping points and two fuels, the 1,296 terms read back equal
  the printed ones.

- **CI green on Linux** (2026-10-22, #59). Every run had failed since CI began. glibc
  hid POSIX under `-std=c11` (the Makefile defines `_DEFAULT_SOURCE`); `qsort` ran on
  empty, unallocated arrays; four ranking sorts left ties to an unstable `qsort`, so
  `jetstat` printed tied rows in another order on Linux; and `test_cli` closed stdout,
  which a process can reopen, where it now opens it read-only.

- **Publication files** (2026-10-22). An MIT licence; the README's quick start, input
  syntax, checks and their outside checkouts; `docs/README.md` as the index, with a
  getting-started tour, a map of the source and a guide to the checks; `DESIGN.md`'s
  status, reading guide and terms; and CI that skips documentation-only changes.

- **Smoke as skijack-2 has it** (2026-10-22, #56). #55 changed two recorded outputs,
  `jets` (139 jets registered where 135 were) and `jetstat` (tied rows in the new
  digests' order); `make smoke` is 29/29 again.

- **The defect lemma's check through frame traces** (2026-10-22; `DESIGN.md` §22).
  The frame-trace plan's last item: `--defect` counts D as the pure-S paper's check
  of its defect lemma does, and `client.py defect N` runs it over `avon enum`. On
  sizes 1 to 11 every term's count equals the definitions' and the totals equal the
  paper's mode `defect` (`make hider-check`); sizes 12 to 16, 13.4 million terms and
  2.97 billion steps, show no fall of D and D >= 1 at all 40.4 million confirmed
  records after a y-step, size 16 in 126 s.

- **skijack-2: 128-bit structural hashes** (2026-10-21; `DESIGN.md` §5, SKIjack #18).
  The §5 hash kept 16 hex digits, 64 bits, within a birthday search's reach of anyone
  choosing both terms. It keeps 32 now, under the version `skijack-2`: `av_digest` is
  two words, the dashboard, templates, words, interpreters, the census, the profile and
  front0's reader carry it whole, and the dashboard's index probes by its first word.
  `SKIJACK_PIN` moves to the commit that writes it, bringing SKIjack's literals,
  binders, Stage B and number bound; every fixture regenerates (`fixtures_check.sh`:
  193 files), and the corpus dictionary has 286 rows, four from the new `literals`
  program. The P2 report computes `P`'s hash from the term it loaded.

- **An entry is its term, not its digest** (2026-10-21; `DESIGN.md` §6.5). `jet_entry_for`
  and registration took any dashboard entry under a digest as the offered term's, so a
  64-bit collision between a template key and a dictionary row merged the two jets. A
  hit now counts only when the entry's term is the offered one; another term under the
  digest is refused as `jet_collision`. `test_jets` pins both paths without searching
  for a collision.

- **Comments and messages stand alone** (2026-10-11, #46 and #47). No comment or error
  message cites a `DESIGN.md` section or an `AUDIT.md` item; pointers to other
  projects' specifications stay. Smoke records the messages.

- **lean-ski at `paper-v8`** (2026-10-20). `tests/pins.sh` moves to `b7fae43`, past
  `paper-v4` by lean-ski #28–#49: the split predicates remade with secret witnesses and
  heights that hold every witness (#34), hiding tables of at least `2^9` rows (#31),
  and the Fiat–Shamir and Merkle work in the random oracle model. lean-ski now refuses
  POP and INSTW budgets below `2^9`, so `zk_jet_witness_check.sh` asks `2^9` for `and`
  and `or` where it asked `2^8`. The five checks the pin serves pass at `b7fae43`.

- **Pins tolerate documentation** (2026-10-11). `pin_check` accepts a checkout past its
  pin when every commit since, and every tracked change, touches only documentation:
  `*.md`, `*.tex` and `*.txt`, but not lean-ski's statement, witness and corpus `.txt`
  files, which the checks read. A WORKLIST commit in lean-ski or a `.tex` edit in the
  paper's repository no longer stops the checks. The pin must be an ancestor of the
  checkout; a rename counts on both sides.

- **lean-ski at master, past `paper-v4`** (2026-10-11). `tests/pins.sh` moves to
  `5614cb4`: `paper-v4` (`3e30892`), the lean-ski the Zero-knowledge SKI paper
  describes, and one WORKLIST change (#25). Its release script stops unless each of
  Avon's four jetted witness tables is ski-air's, byte for byte (lean-ski #22, #23). No
  Lean source changed since `paper-v2`; the five checks the pin serves pass at both
  `3e30892` and `5614cb4`. The checks default to a lean-ski checkout at
  `~/Code/ski/lean-ski`; `LEAN_SKI` names another.

- **lean-ski at `paper-v2`** (2026-10-11; `ZK-JETS.md` §1 and §9). lean-ski's jet table
  no longer licenses a template that compiles to a bare `S`, `K` or `I`. `tests/pins.sh`
  moves to that commit, `79c7026`, and the five checks it serves pass there. Avon writes
  every jetted witness table byte for byte as ski-air does, and lean-ski #22 remakes its
  release from Avon's tables. `zk_jet_witness_check.sh` takes the too-small POP budget
  from the run's pops, and requires Avon's refusal to name the budget. It had taken the
  statement's budget less one, which `split8`'s 7,154 pops now fit.

- **The Poseidon2 jet, end to end** (2026-10-03 and 04; `ZK-JETS.md` §8, `DESIGN.md`
  §6.12). `avon witness` writes `p2pre` and `p2commit` tables byte for byte ski-air's
  (#8, #9); share mode runs lean-ski's `P` natively with `--p2` (#10); and the C is
  printed from a Lean proof that it computes the specification on every `uint32_t`
  state (`lean/P2Prog.lean`, `AvonP2.permuteC`, #11).

- **Chained Poseidon2 calls** (2026-10-04; `DESIGN.md` §6.12). `P (P x)` fires both
  calls natively, innermost first, in one walk down the chain: two steps and 0.03 s for
  test vector 1, against 981 million steps and 11 s when the outer call declined. A
  decline now checks the jet node's term too; before, a node made after the bind ran
  `P`'s registered term in place of its own over anything but a state.
- **Entropy for kernels** (2026-10-04; `DESIGN.md` §9.1, SKIjack SPEC §4.1). Per
  request: a pier booted with `--entropy` answers each `[0 id]` in a poke's effects
  list with the event `[0 [id bits]]`, 128 Scott Booleans, logged first, and boot's own
  request with the first event; `--entropy=FILE` for tests. Per request rather than with
  every event because a proved poke carries its whole event as private witness, and
  most events need no bits. lean-ski proves a poke of a reply with the bits private
  (2026-10-05, `Ski/Entropy.lean`).

- **`--memory`** (2026-10-05, #18; `DESIGN.md` §6.11, "Shared"). One `Y g` per
  generator, never written, and one shared unfolding: peak memory of a few MB where
  `--fix` holds hundreds, at about `--fix`'s time. Safe cycles parked on their measured
  ceiling (item 4). Integer literals proposed to SKIjack (issue #7).

## Next

1. **Subject knowledge analysis** ([`SKA.md`](SKA.md)): every step decided. Built: the
   template load, the measurement, discovery and front1's own templates. Measured and
   not taken: specialization (§5), new mechanisms for cases and thunks (§4), discovery
   told references by running, and compiled template bodies (§8).

## Done: the order agreed 2026-10-05

1. **CI**: done 2026-10-05 (#19). `make check` on Linux for every pull request, and
   macOS too on master. The checks that need lean-ski or skijack checkouts stay manual.
2. **Check entropy against §9.1**: done 2026-10-05 (#20).
3. **Stage 8** (item 3) through M4: done 2026-10-05. Every corpus program compiles to
   Python's terms, hash for hash. The checkers, M5 and M6, follow the audit.
4. **A codebase audit**: done 2026-10-05 (`AUDIT.md`), by reviewers in parallel: failure paths, documentation
   against code, the build and its gates, the security edges, the shape of
   `reduce.c` and `main.c`. Slated into it: plain SKI's residual 1.9 to 3.9% since
   deferred roots (code generation), and deferral's 8 to 39 MB of extra peak memory with
   the same live set (the allocator).
5. **Fixes and hygiene refactors** from the audit's findings: done 2026-10-11 (#24 to
   #44), each its own pull request, in `AUDIT.md`'s order. Every item is closed: 25
   fixed, and the two measured (25, 26) closed with deferral retained.

## In progress

### 0. The papers' measurements

Collected 2026-10-04: proof sizes and verify times (`ZK-JETS.md` §1), Poseidon2 on
all three vectors, and the interpreter jet's wall clock (`BENCHMARK.md`, "The
interpreter jet's wall clock"). Measuring the last found `av_equal` allocating on
every call; keeping its first stack and set on the C stack took T2 with the jet
from 0.95 ms to 0.41 ms. A statement with two jet calls, lean-ski's `p2chain h`,
measures 1,317 rows, proved in 1.44–1.48 s and verified in 1.89 s (lean-ski #65; Avon's
table byte for byte ski-air's). Open, with lean-ski:
- ski-air timing the proof's check apart from Lean's statement checks, since jets
  make verification slower (`split8` 23.0 s against 12.6) and the split is not
  measured.

### 1. Strictness: measured; the levers it found (`BENCHMARK.md`, "What becomes of an instance's cells")

Measured 2026-10-02 with `make stats` on the five Reduceron ports and the front end:

- **Primitive-redex speculation:** dropped. No numeral operation has both numerals
  held when its cell is written; the operands are thunks.
- **Head strictness:** not now. Thunks are 8 to 20% of cells, 50 to 91% are forced,
  and update in place already writes a forced value over its cell, so eager evaluation
  would save a revisit, not a node.
- **Case of a known value: built** (2026-10-02, `DESIGN.md` §6.10, "A case joined to
  its instance"). It is exact: every count and state is unchanged. It runs 0 to 9%
  faster (`BENCHMARK.md`, "A case joined to its instance"), but retires more
  instructions where most attempts fail. A cheaper test for "the formal is
  unevaluated" would recover them. Not yet tried on top of deferred roots, which changed
  the same instance path.
- **Spine cells: built** (2026-10-04, `DESIGN.md` §6.13, "Deferred roots"). An
  instance leaves its root and spine in the stack, written only when something else
  could read them. Every count and state is the same, and the five Reduceron ports
  run 5.8 to 14.5% faster (`BENCHMARK.md`, "Deferred roots"). Measured first: 55 to 95%
  of spine cells sit under a head that steps at once.

## Later

### 3. Stage 8: the full language's front end (`DESIGN.md` §20.3)

SKIjack-0's front end compiles itself in Avon. At scoping the rest ran only in Python:
cores, macros, signatures, quotation, scries, namespace literals and the type checker. Most
of the work is SKIjack programs in skijack's repository; Avon runs them and checks them
on the corpus, hash for hash. M1 to M6 are built, and front1 installs the prelude's later operations too.

Scoped 2026-10-05, against skijack `6a870ac`. The SKIjack-0 front end
(`selfhost/front0.ascii.ski`) is 406 lines; Python's front end about 7,100. Sizes
are estimates, in lines of SKIjack:

| milestone | adds | size (estimated at scoping) | corpus programs matching (estimated) |
|---|---|---:|---:|
| M1 | wider lexer and parser, plain cores, hygienic macros, signatures parsed and dropped, the birds `B`, `C`, `W`, `Y`, the numeral operations | 150–250 | 5 of 17 |
| M2 | interpreter generation (`generate.py`): step and loop equations, names built at run time | 150–250 | 10 |
| M3 | quotation and level-1 runs: object leaves, encoding, `\|-`, fuel | 100–160 | 13 |
| M4 | scries, path literals, namespace literals | 60–110 | all 17 |
| M5 | Stage A (`check.py`): refusal parity, errors with a class | 250–400 | — |
| M6 | Stage B (`typecheck.py`): Hindley–Milner over an explicit store, equirecursive unification | 400–700 | — |

**M1 to M4, built 2026-10-05** (skijack `front1.ascii.ski`, `run1.py`; `make
front1-check`; `DESIGN.md` §20.3). Every corpus program agrees, hash for hash, and the
fixed point covers 1,009 names. Twelve edge programs aviary's environment once decided
(binders named as defined names, a binder twice, a recursion's name rebound, a binder
named as a later definition) agree since skijack fixed the reference on 2026-10-21: a
binder is a binder, whatever name it spells. Open: front1's term grew from 265,145 nodes
to 635,173, so Python compiles it in 48 seconds; the audit did not take it up.

**M5, built 2026-10-27** (skijack `front1.ascii.ski` and `run1.py`; avon `front0.c`;
`DESIGN.md` §20.3). Stage A runs over the parsed program, as Python checks before it
expands: 166 lines of front1, comments and generated names included, against the 250 to
400 scoped. Each refusal carries its class, `RErr n`. Its reference is Stage A over
Python's parse, then the expander with checking off. Every corpus program, all 432 edge
programs (97 of them M5's, each check passed and failed, and the order of the first
problem), 991 of 1,000 random programs of the full language, 100 of a second seed and
200 of SKIjack-0 agree; the other 9 are too heavy for front1 to finish, and the three
measured were as heavy for front1 before M5. front1 did not install `natDiv`, `natRem` or
the list operations, which the expander's prelude gained after M4; it has since
2026-10-28 (SKIjack #39).

**M6, built 2026-10-28: Stage B** (skijack `front1.ascii.ski` and `run1.py`; `DESIGN.md`
§20.3). Stage B runs over the generated, macro-expanded program, its types nodes in a
store keyed by number, the first problem ending it with class 7: 504 lines of front1,
comments, types and generated names included, against the 400 to 700 scoped. front1
agrees where both can witness: a Python refusal for its recursion limit is not compared.
Every corpus program, all 472 edge programs (43 of them M6's), 1,300 random programs and
500 typed ones agree, and the fixed point covers 1,520 names with templates and data jets
in 2.46 GB. Since, front1 installs `natDiv`, `natRem` and the list operations
(2026-10-28, SKIjack #39), whose Stage B accepting edges are in: all 482 edge programs and
500 typed ones agree, and the fixed point covers 1,529 names.

Checking never changes the terms, so M1 to M4 are each checked against
`skijack.compile(..., check=False)` on the corpus as they land, with `run0.py`'s
random and edge programs extended. The front end stays a separate program from
`front0`, whose fixed point stays as it is; the reader `avon front0` serves both while
the result's shape is kept. Hard parts, from the scoping: no parametric types, so
every table is its own trie (generate them, as `tables.py` does); names built at run
time need the intern table kept past lexing; Python's output order (compare as a
map, or reproduce it).

### 4. Safe cycles for Y: parked 2026-10-05 (`DESIGN.md` §6.11)

Measured first (`BENCHMARK.md`, "Y shared (`--memory`)" and "The ceiling for a
true cycle"):
- Nearly all of a port's live set is Y's unfoldings. `--memory` (one shared `Y g`
  per generator, acyclic) cuts peak memory to 4 to 8 MB, at `--fix`'s time.
- A true cycle, grafted onto today's code, would take 1.12 times less time than
  `--fix` by geometric mean (1.00 to 1.25), with `--memory`'s memory.

Parked on that: 12% does not pay for what a safe cycle needs.
- indirection writes checked never to close a loop (`av_res` and the collector
  spin on one);
- re-entry of a knot under evaluation turned into fuel, as SKI runs forever;
- a normal-form pass that refuses infinite terms;
- no cycle leaving a reduction: every exit, kernel pokes included, breaking each
  knot's back-edges, or every walk and snapshot learning cycles;
- copy mode and the witness without cycles; for proofs, a lean-ski heap semantics.

If taken up: cycles inside `reduce` and `batch` only, broken at every exit, kernels
refusing the flag; measure the cost of breaking them before going further.

### 7. SKIlark's data jets: planned 2026-10-24 (`DESIGN.md` §6.14)

SKIlark's sums already dispatch in one step; its numbers miss the native operations and
its lists have no data jet. In order: SKIlark's arithmetic on the prelude's operations,
its operands cased into words first (SKIlark alone; `200 200 *` from 8,360,922 steps to
160,085); `natDiv` and `natRem` in the prelude and in `words.c`; list words with the
prelude's list operations; and the proofs, §18.2's word cells and a list cell. The cap
stays at 32: SKIlark's sets came in under it (the sidestep, 2026-10-24), and two `word`
slots remain for list kernel words before markers and `AV_JET_ARITY_MAX` must rise
together or `word` split.

## Handed to lean-ski

### 5. The proof gaps (`DESIGN.md` §11.1, "Open")

- Witnesses for terms with atoms (§17.3): plain witnesses built and checked at the pin (lean-ski #64, Avon #109); jetted and probed ones still refuse atoms.
- Scry beyond a resume loop's final run.
- Witness rows for the numeral and constructor jets and the one-step Y. The Y row's
  `Tr` simulation is proved with Y a jet at the compiler's recursion sites
  (`lean/Fix.lean`, §6.11). Poseidon2 has them (`ZK-JETS.md` §8).
- Assumed: Fiat–Shamir soundness past the counting step (`logup_fs`), the hiding of
  every commitment but the first, and ChaCha20's pseudorandomness (`ZK-JETS.md` §7).

The Poseidon2 tables' constraints are done in lean-ski: for `p2pre` and `p2commit`,
the honest tables satisfy every AIR (`compPG_complete_log`, `compP_complete_log`,
`compPC_complete_log`).

When lean-ski changes a table format or the prover's inputs, Avon matches it and
reruns `make zk-jet-witness-check`.

## Small items

### 8. The stats build crashes on front1

Found 2026-10-29: `make stats` builds, and `build/stats/avon front0` on front1 stops with
a bus error even on a one-line source, as it does at `298c252`, before the SKA arc; a
small `reduce` completes. Open, unexamined; the stats build is diagnostic only.

### 6. From the reviews of avon PR #3

None of these changes a result.

- **Probed 2026-10-04:**
  - `enum --base` with an empty file prints nothing and says so; a malformed
    line now names its file and line, and no longer adds a false "out of memory".
  - `dag` input of 1.2 million nodes, right-deep, left-spined and an exponential
    tree shared as a DAG, under ASan in both strategies: clean, under 0.6 s each.
  - `--records` near `SIZE_MAX` wrapped `n + CONF` and confirmed every record;
    fixed (`trace.c`, `confirmed`), with a test of four windows past the horizon.
- **Noted, left as they are:**
  - `word_admit`'s 10,000,000-step cap counts a slow operation as refused;
  - SKIjack's inliner falls back silently when it hits its budget or depth.

## Parked

- **SKIjack PR #2, the Rust port.** Out of scope for the SKIjack repository; parked
  2026-10-02. Its manifest is 19 commits behind master.
