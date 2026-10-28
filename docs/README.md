# Avon's documentation

| file | answers |
|---|---|
| [`GETTING-STARTED.md`](GETTING-STARTED.md) | How do I run it?  A tour of the commands, each with its output. |
| [`RUNTIME.md`](RUNTIME.md) | What does each command, option and file do, and what does each exit status mean? |
| [`ARCHITECTURE.md`](ARCHITECTURE.md) | Where in the source does each part live, and how does a term move through it? |
| [`TESTING.md`](TESTING.md) | What does each check prove, and what does it need? |
| [`DESIGN.md`](DESIGN.md) | Why is Avon built this way?  The design, its decisions, and what was built when. |
| [`BENCHMARK.md`](BENCHMARK.md) | How fast is it?  Every measurement, with the commit it was taken at. |
| [`ZK-JETS.md`](ZK-JETS.md) | How do jets enter a zero-knowledge proof?  Statements, tables and their checks. |
| [`WORKLIST.md`](WORKLIST.md) | What has been done lately, and what is next? |
| [`LEAN-JETS.md`](LEAN-JETS.md) | Which of Avon's C jets are proved in Lean, what each proof covers, and what is next? |
| [`SKA.md`](SKA.md) | What does subject knowledge analysis offer an SKI runtime, and what did Avon take from it? |
| [`AUDIT.md`](AUDIT.md) | The codebase audit of 2026-10-05, closed 2026-10-11; a record, with line numbers as they were. |

## Reading order

- **To use Avon:** the top-level `README.md`, then `GETTING-STARTED.md`,
  then `RUNTIME.md` as the need arises.
- **To change Avon:** `ARCHITECTURE.md`, `TESTING.md`, then the sections
  of `DESIGN.md` for the part you change.  `DESIGN.md` opens with a guide
  to which of its sections are plan, record and current design, and the
  terms it uses.
- **To check a claim:** `BENCHMARK.md` and `ZK-JETS.md` name the commit
  and the command behind each figure; `DESIGN.md` §11.1 records what each
  stage was accepted on.

Section numbers such as §6.9 refer to `DESIGN.md`.
