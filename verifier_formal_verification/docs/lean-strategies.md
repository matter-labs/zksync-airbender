# Lean strategies: operating, proving, specifying

How to work on the Lean side (`lean/`): run the checks, keep proofs in `slop/` fast and modular, keep the spec in
`human/` short and complete. General rules only; the file map is in [`../README.md`](../README.md), the trust layout
in [`architecture.md`](architecture.md).

The project proves Airbender's guest binaries correct: `human/` states what they must compute on the Airbender
machine (RV32IM as Sail defines it, plus Airbender's changes and its precompiles, called delegations); `slop/`
proves it. The trusted base is the Lean kernel, Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`), the official Sail RISC-V model, and what `human/` states.

**No `sorry`, anywhere.** Not in `human/`, not in `slop/`, not in tests or helpers, not temporarily in a commit. Work
in progress stays uncommitted until it is proven. This is enforced, not just a convention: every library is built
with `-E hasSorry`, which turns Lean's "declaration uses `sorry`" warning into an error (Lean's analogue of
`#![forbid(unsafe_code)]`).

---

## 1. Operating the system

### 1.1 `verify.sh` is the definition of "done"

`./verify.sh` rebuilds the guest binaries and every generated artifact (Lean images, code lists) and checks they
match what is committed; builds the spec and proofs; checks every final theorem by name, statement and axioms;
checks the equivalence of our spec with Sail; runs the images on sample inputs. Anything it does not check does not
count.

- **Every final theorem is in its check list.** A theorem that exists but is not listed is not verified. When you
  add a statement to `human/`, add it to the list in the same change.
- **Axioms are checked exactly.** Only the three standard axioms. No `sorry`, no `bv_decide` or `native_decide`
  (they add axioms). `omega`, `bv_omega`, `decide`, `decide +kernel` are fine.
- **Generated files are compared to the git index.** Stage (`git add`) regenerated files before running, or the
  check fails on a stale index.
- **The Sail model is pinned and fetched, not committed.** Changes to how Sail is configured (which extensions it
  offers) go through its config; every behavioural difference from Sail lives in Lean (3.1).
- **The trust checks run on every build of the final theorems** (3.5): statements only from `human/` and the trusted
  libraries, `human/` imports nothing else, no escape hatches outside the listed tactic code, only standard axioms.

### 1.2 Iterating quickly

- One file, dependencies already built: `lake env lean <file>`. A module and its imports: `lake build <Module>`.
  Never build the whole workspace to check one file.
- Profile a slow file with `set_option profiler true` and `profiler.threshold` in a scratch copy; read where the
  time goes (simp, omega, kernel type checking, symbolic evaluation) before changing anything.
- Measure per-module build times from `lake build` output, and the critical path (the longest chain of module times
  through the import graph). Wall time is bounded by the critical path, not the sum.
- Measure on a quiet machine. Timings under parallel load are off by 2–4×; compare CPU (user) time when you can't.

### 1.3 Lake has no early cutoff

Lake rebuilds every module downstream of a changed file, even for a comment edit (`touch` alone does not trigger
it; it hashes content). So:
- An edit to a widely imported file costs a large rebuild. Keep such files small and stable, and keep imports narrow.
- A proof should import the smallest module that states what it needs (an interface or contract), not the module
  that proves or defines everything (2.1, 2.2).
- The machine includes its delegation (precompile) semantics, so an edit to a delegation definition rebuilds
  everything that depends on the machine. Batch such edits.

### 1.4 Toolchain: latest stable, upgraded deliberately

Track the latest stable Lean release (not release candidates) with the Mathlib tag made for it. Lean evolves fast,
and newer releases bring features and performance. Pin both, so every check is reproducible, and upgrade as one
deliberate change: bump the toolchain and Mathlib together, update what depends on them (patches to pinned
libraries, version-matched tools), fix what breaks, run `verify.sh`, commit. Never mix an upgrade with other work, so
breakage and timing changes are attributable.

### 1.5 Backup checker: rarely

`backup-check.sh` replays every declaration of `human/` and `slop/` through a second, fresh kernel with `leanchecker`,
which ships with the pinned toolchain (`--fresh` also replays Mathlib and Sail). It guards against tactics or other
metaprograms that might add declarations without the kernel. It takes tens of minutes, so it is not part of
`verify.sh` and not run per commit: run it only at major milestones, such as before tagging or publishing a result.

### 1.6 Working with several agents or sessions

- One writer per worktree at a time. Two sessions (or a forked session) on the same files overwrite each other and
  race on the build. Stop one before the other continues.
- Parallel agents get disjoint files. Shared helpers they create go in new modules; existing shared modules are only
  extended, never changed under another agent.
- After parallel work, reconcile: one version of each helper (2.5), no unused declarations (2.6), then one
  `verify.sh` run and one commit.

---

## 2. Keeping `slop/` fast and modular

Budget: about 10 s per module, 30 s at most. A slow proof is a design problem, not a limit to raise.

### 2.1 Do less prover work first

The order of remedies for a slow proof:
1. **Lemmas proven once instead of per-instance reasoning.** If a fact is re-derived at each use (one `bv_omega`
   per address, one unfolding per call), state it once in general form, prove it once, cite it. Represent repeated
   structure as data (a list of stores, a list of calls) and prove lemmas over the list.
2. **Interfaces instead of unfolding.** A proof must not unfold a table, a decoder or a large definition. It uses one
   lemma stating the property it needs. Then extending the table re-proves only that lemma.
3. **Symbolic execution for straight-line code.** Use the verified symbolic executor on whole blocks rather than
   stepping one instruction at a time with `simp`.
4. **Only then split for parallelism** (2.3).

### 2.2 Contracts separate from proofs

What a caller relies on (a function's precondition and postcondition, a frame's invariants) goes in its own small
module. Callers import the contract, not the callee's proof, so callee and caller build in parallel and a change to
one proof does not rebuild the other.

### 2.3 Splitting is second-line

Splitting a file does not reduce work: each module pays its import loading, so total CPU goes up. It only shortens
wall time, and only for a proof that is already lean but long and serial, is on the critical path, and has idle
cores to run on. Off the critical path it only costs. For a long symbolic block there is a tool that cuts its check
into parts built in parallel and glues them back with unchanged statements; use it under the same conditions.

### 2.4 Proof hygiene

- Kernel evaluation (`decide +kernel`, `rfl` on computations) is fast on closed terms and slow or stuck with free
  variables. Split cases first, then evaluate closed facts. Put one small evaluated fact per definition in its own
  lemma and reuse it.
- `rw` closes goals by `rfl`, which can unfold large definitions; prefer `simp only [...]` with named lemmas when the
  remaining goal is big.
- Avoid context-wide tactics in big contexts: `simp_all`, `set`. Use `simp only` with names, and plain equations
  (`obtain ⟨x, hx⟩ : ∃ x, x = … := ⟨_, rfl⟩`).
- `split`/`split_ifs` also split `if`s hidden inside definitions and proof terms; use `by_cases` with a named
  hypothesis where that matters.
- Heartbeat limits are regression guards: set a small explicit limit a little above the measured cost, never `0`.
  A proof that hits it got slower and should be fixed, not given more budget.

### 2.5 One helper per job

Reuse first. Before writing a helper lemma or tactic, look for one that does the job, and extend it rather than add
a parallel one with a different shape. Generic helpers live in the shared toolkit; helpers specific to one function
live next to its proofs. Two versions of the same helper are a defect to merge. The one exception is performance: a
specialised helper is fine where the generic one is measurably slower, and the reason is noted next to it.

### 2.6 No unused Lean

Every module and every declaration must be used by a final theorem. Delete demos, debug commands, exploratory
proofs and dead lemmas; do not keep a file "for later". A check worth keeping (a sanity fact about the machine) is
stated in `human/` and made part of a final theorem, so it is both used and verified. Find dead code by computing the
transitive closure of the constants the final theorems use and listing declarations outside it.

---

## 3. Keeping `human/` short, readable and complete

`human/` is what a reviewer reads; everything in `slop/` follows from its statements. It should be short enough to
read in full and need no Lean expertise beyond definitions.

### 3.1 Standard definitions plus deviations

Build the spec on well-known, independently maintained definitions, and state our objects as short lists of
deviations from them:
- the machine: the official Sail RISC-V model, plus each change from it marked in place where the machine is
  defined, and an equivalence theorem showing the readable spec is that machine;
- hash functions: RFC 7693 (Blake2s), FIPS 202 (Keccak-f[1600]);
- arithmetic: Mathlib (`ZMod`, polynomials).

This serves both sides: the reviewer reads a few lines of deviation instead of a whole definition, and the proofs
show "equal to the standard, except for these cases" instead of re-deriving the standard.

### 3.2 Small partial steps, then composed theorems

An operation performed in steps (a precompile called many times, such as a Blake2s round or a Keccak step) is
specified as one small definition per step, partial on purpose. Using a step outside its documented protocol is undefined behaviour: the
spec says what the step does and claims nothing else. Separate theorems state that the steps, used as documented,
compose to the standard operation. The reviewer checks small definitions; the composed theorems carry the meaning.

### 3.3 Direction of trust

The model must accept at least everything the real system accepts. Then "no run reaches a bad state" in the model
covers every run of the real system; a model that rejects something the system accepts would make such claims
vacuous for those runs. Where the model is wider than the reference (Sail) or than another implementation, list the
difference explicitly. The equivalence with Sail is a check on `human/`, not a replacement for reading it: it is
how wrong spec lines get found.

### 3.4 Everything trusted is visible in `human/`

A reader must be able to see, in `human/`, every assumption the final theorems rest on. One file in `human/` lists
them: the Lean kernel and its standard axioms, each external library the spec is stated in (with where it is
pinned), the generated artifacts and how they are checked, the standards transcribed (and the test vectors that check
the transcription), and the sources of system-specific facts. The same file holds, as Lean data, the list of trusted
libraries and the list of tactic modules allowed to use `unsafe`/`partial` code, so the checks read exactly what the
reader reads.

Proof-search code is not trusted: the kernel re-checks everything it produces. It may use `unsafe` evaluation or
`partial` functions, but only in the modules that file lists.

### 3.5 What the trust checks enforce

- Every theorem whose statement is a `human/` definition uses only the standard axioms, and its statement mentions
  nothing defined outside `human/` and the trusted libraries.
- `human/` imports only itself and the trusted libraries; it never imports proofs.
- No module of ours declares an `axiom`, uses `sorry`, or uses native evaluation (`native_decide`, `bv_decide`);
  `unsafe`, `partial`, `implemented_by` and `extern` appear only in the listed tactic modules.

Adding a library, an assumption or a tactic module is a change to that `human/` file, visible in review.

### 3.6 What goes where

| `human/` | `slop/` |
|---|---|
| Machine state, decoder rows, one line of behaviour per instruction kind | Lemmas about the machine, the executor, tactics |
| Contracts and what programs should compute | Per-function proofs of those contracts |
| Final statements, including the sanity facts that pin down the machine | The proofs those statements name |
| Standard definitions and the deviations from them | Generated code and generated lemmas |

- A definition that is only a proof convenience belongs in `slop/`.
- If a `human/` line needs a comment to be understood, restate it as a standard definition plus a deviation.
- Edit `human/` rarely and deliberately; every edit rebuilds what depends on it (1.3).

---

## 4. Checklist for a change

1. Put each new statement or definition in the right layer (3.6).
2. Reuse helpers; if one is missing, add it to the shared toolkit in general form (2.5).
3. Prove general facts once and cite them (2.1); keep contracts separate from proofs (2.2).
4. Measure the module (1.2); if it is slow, do less work before splitting (2.1, 2.3).
5. Check that nothing you added is unused (2.6), that every new final theorem is in `verify.sh` (1.1), and that a new
   library, assumption or tactic module is listed in the trust file (3.4).
6. Stage generated files, run `./verify.sh`, commit with Conventional Commits.
