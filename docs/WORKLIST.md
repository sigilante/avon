# Worklist

What remains, in the order we mean to take it. `DESIGN.md` §11.1 records what is built;
this file records what is next. Each item names its decision state and where its
design lives. Last revised 2026-10-02.

## In progress

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
  unevaluated" would recover them.
- **Spine cells: a design question.** They are 61 to 65% of the cells instances
  write. The Reduceron pushes the spine onto the stack and updates shared redex
  roots lazily. Avon writes the whole result over the redex root at once. Leaving
  that rule needs update frames and its own plan (§2, §3.1). Share mode is never
  proved, so the proofs are untouched.

## Decided, to build

### 2. Entropy for kernels (`DESIGN.md` §9, to be written as §9.1)

Decided:
- **128 bits** per entropy event, for a research proof of concept, not production
  security.
- **Per-request delivery.** A kernel emits an effect asking for entropy, and the pier
  answers with an event carrying fresh bits from `getentropy`, logged before it is
  applied. `avon boot` gives a boot seed the same way. There is no ratchet in the
  kernel.
- **Entropy is only ever event data, never a reduction primitive.** Replay, the
  conformance counts, the jets' licence and every proof depend on it.
- `--entropy=FILE` replaces `getentropy` for reproducible tests.
- The log, and so the pier, is as secret as the bits it holds.
- In a proved poke, the bits are a private witness (lean-ski).
- Kernel entropy never feeds the prover's seed (`ZK-JETS.md` §7).

Open:
- **Encoding.** Recommended: 128 Scott Booleans, which are pure SKI and are the shape
  of lean-ski's private witness tables. The alternative is data-jet words, which are
  compact but exist in share mode only.
- **The request and reply shapes.** A change to SKIjack's kernel interface,
  `SPEC.md` §4.1, agreed with SKIjack.

Steps:
1. Write §9.1.
2. Agree the shapes in SKIjack.
3. Build the pier's request and reply loop, the boot seed and `--entropy=FILE`.
4. Add kernel tests: replay gives the same bits, and a request is answered once.

## Later

### 3. Stage 8: the full language's front end (`DESIGN.md` §20.3)

SKIjack-0's front end compiles itself in Avon. What remains is cores, macros,
signatures and quotation. It is the one unfinished stage.

### 4. Safe cycles for Y (`DESIGN.md` §6.11)

`--fix` unfolds Y acyclically and cannot share the unfolding. The cycle experiment
(`experiment-knot`) showed that sharing is worth 1.20 times by geometric mean, and
that an unguarded cycle changes answers and hangs. A safe cycle needs:
- black holes, so that a cyclic redex that needs itself stops at FUEL;
- walks that tolerate cycles, or a proof that none reaches them;
- copy mode left without cycles;
- before a witness can use one, a lean-ski heap semantics for cycles.

It needs its own plan.

## Handed to lean-ski

### 5. The proof gaps (`DESIGN.md` §11.1, "Open")

- Witnesses for terms with atoms (§17.3).
- Scry beyond a resume loop's final run.
- Witness rows for data jets and the one-step Y, with the `Tr` simulation theorem
  (§6.11).
- Fiat–Shamir and ChaCha20's pseudorandomness, both assumed (`ZK-JETS.md` §7).

When lean-ski changes a table format or the prover's inputs, Avon matches it and
reruns `make zk-jet-witness-check`.

## Small items

### 6. From the reviews of avon PR #3

None of these changes a result.

- **Not yet probed:**
  - `enum --base` with an empty or malformed file;
  - `dag` input of 10⁶ nodes or more, under ASan;
  - a huge `--records` value on a long fuel-limited run.
- **Noted, left as they are:**
  - the reservation `assert`s in `jets.h` vanish in release builds;
  - `word_admit`'s 10,000,000-step cap counts a slow operation as refused;
  - SKIjack's inliner falls back silently when it hits its budget or depth.

## Parked

- **SKIjack PR #2, the Rust port.** Out of scope for the SKIjack repository; parked
  2026-10-02. Its manifest is 19 commits behind master.
