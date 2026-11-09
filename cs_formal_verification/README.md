# Circuit verification

Lean proofs that Airbender's circuits (the no-cache constraint JSON in `cs/compiled_circuits/`) implement our own
RV32 specification (`RV.step`/`RV.run`, [RV32.lean](lean/human/Human/ISA/RV32.lean)): RV32IM without the signed M
operations, plus Airbender's custom operations and delegations. The specification is tied to the official Sail
RISC-V model by a separate equivalence ([Sail leaf](lean/human/Human/ISA/Sail/Theorems.lean)); no circuit claim mentions Sail.

**Check everything:** `./verify.sh` (prepares the pinned Clean, builds the spec and all proofs, checks that the spec
does not import the proofs, runs the regressions and the axiom audits, checks every module's [build budget](#build-budget),
checks the review guides).

## Layout

- `lean/human/` — **what a human reads**: everything a claim's meaning depends on. The circuit models, references,
  artifacts and interface assumptions (`Human/Circuits/`), the shared context (`Human/Helpers/`, starting from
  `Human/Helpers/Properties.lean`), whole-trace execution contracts (`Human/Trace/`) and the JSON importer that turns
  an artifact into CleanCore constraints (`Human/Import/`), and the RV32 specification (`Human/ISA/`). `human/` is the
  spec (`Human.*`) plus CleanCore, our transcription of Clean. It imports Lean, Mathlib (including Batteries) and itself; the one exception
  is [CleanCore/Equivalence.lean](lean/human/CleanCore/Equivalence.lean), a leaf that imports Clean to prove
  each CleanCore definition equal to Clean's. Nothing in `human/` imports it, so Clean is not in the spec's import
  closure. The Sail model (the generated SailRV32 and lean-sail) is imported only by `Human/ISA/Sail/*` and
  [Configuration.lean](lean/human/Human/Helpers/Core/Configuration.lean). `./verify.sh` step 1 checks that `human/` imports
  neither `slop/` nor `test/`. Its directory READMEs are the review guide.
  The final statements are `def …Claim : Prop` in the RVTheorems, RVCallerTheorems and Theorems modules under `Human/`
  (and `Human/Trace/RVSoundness.lean`), imported by `lean/human/Human.lean`.
- `lean/slop/` — everything else (kernel-checked, not meant to be read): supporting calculations, proof assembly and
  artifact guards (`Slop/`), and the proofs of the final statements (`Slop/Final/`, laid out like `Human/`;
  `test/Checks/Claims.lean` checks each theorem against its `…Claim` by name and type, and its axioms).
- `lean/test/` — regressions and fixtures (`Tests/`), the axiom audits (`Checks/`).
- `sail/` — the Sail tooling, used only by the equivalence leaf `Human/ISA/Sail/`: `regen.sh` generates the official Sail RISC-V RV32 model (sail-riscv, Sail and lean-sail
  pins in [PINS.md](sail/PINS.md); machine config `config/airbender-base.json`) into the gitignored
  `lean/sail-rv32/`; `fetch-lean-sail.sh` fetches the pinned lean-sail with our Lean 4.35 patches (no upstream licence,
  so never committed).
- `lean/sail-rv32/` — the Lake package `sail_rv32` (the generated model, not committed; its `lakefile.toml`,
  `PROVENANCE.txt` and config copy are). `lean/check_review.py` — review-guide and audit-coverage check.
- `docs/` — [status](docs/VERIFICATION_STATUS.md), [trust and review boundaries](docs/TRUST_AND_REVIEW.md),
  [plan](docs/FORMAL_VERIFICATION_PLAN.md), and the pinned Airbender reference (`docs/airbender/00-master.md`).
- `docs/shared/` — 1:1 copy of `verifier_formal_verification/docs/`, kept in sync, not edited here; in particular
  [Lean strategies](docs/shared/lean-strategies.md), the rules for operating, proving and specifying in Lean.

## What is checked

[Verification status](docs/VERIFICATION_STATUS.md) lists every circuit, checked coverage
and open tasks. It is updated after each completed task.

The proof path is:

```text
no-cache JSON → native Clean constraints → our RV32 spec (RV.step, RV.run)
```

Claims are conditional on explicit interfaces. The imported richer constraints are
the current target; compiled-gate and cryptographic argument soundness are deferred.

## Read these first

The [Review guide](lean/human/Human/README.md) has two routes:
[individual circuit review](lean/human/Human/Circuits/README.md) and
[whole-trace review](lean/human/Human/Trace/README.md).
Directory READMEs explain the relevant references, mappings, assumptions and scope.

[Properties](lean/human/Human/Helpers/Properties.lean) defines soundness,
completeness and the observable circuit relation. Shared helpers are grouped by
[topic](lean/human/Human/Helpers/README.md); properties do not require decoder or
memory-history review. Supporting calculations remain in `slop/`. The [import guide](lean/human/Human/Import/README.md)
says what of `Human/Import/` to read: one trusted transcription step (headed `TRUSTED: review`), the meaning of the
JSON as pure functions, and claims proving that the JSON parser rejects malformed input and duplicate keys and that
every imported definition is the meaning of its transcribed artifact. `Human/Import/Exec/` (parser, emitters) needs
no review: each file names the claims that fix its behaviour.

## Clean, the RV32 spec and Sail

Lean and Mathlib are `v4.35.0`. Clean is pinned at tag `v4.35.0`
(`b41c196b10cf0f389d2badf5e19e1435e78e6d98`), built from source (`LAKE_NO_CACHE=1` in `verify.sh`; Clean would
otherwise download its release's prebuilt files).
We use Clean's native `Expression`, `FlatOperation.assert`, `StaticTable`, `FlatOperation.lookup`,
`Environment` and `ConstraintsHoldFlat`, and its Keccak-f[1600] and BLAKE3 references.
The witness-generation DSL and full `FormalCircuit` bundle are not used. The spec imports these from
[CleanCore](lean/human/CleanCore.lean), a transcription of the Clean definitions used, proved equal to Clean's
in [CleanCore/Equivalence.lean](lean/human/CleanCore/Equivalence.lean) (deviations listed there).
Airbender's two-16-bit-limb representation is preserved.

The reference is our RV32 spec: [State.lean](lean/human/Human/ISA/State.lean) (registers, PC, ROM image, RAM, input
stream), [RV32.lean](lean/human/Human/ISA/RV32.lean) (`RV.step`, `RV.run`) and
[Delegations.lean](lean/human/Human/ISA/Delegations.lean) (the precompiles); each difference from standard RV32IM is marked
`-- Airbender:` there. [Vectors.lean](lean/human/Human/ISA/Vectors.lean) checks the BLAKE2s and Keccak-f[1600] published
test vectors, and [DelegationRuns.lean](lean/human/Human/ISA/DelegationRuns.lean) states what the delegation call runs compute.

The official Sail RISC-V model (pins in [PINS.md](sail/PINS.md)), generated to Lean by [regen.sh](sail/regen.sh) into
`lean/sail-rv32/SailRV32/`, is used only to justify the spec. The [equivalence leaf](lean/human/Human/ISA/Sail/Theorems.lean)
states three facts, proved in `slop/Slop/ISA/Equiv/`: `DecodeIsSailClaim` (Sail's decoder decodes every word of the
spec's encoding table to the same instruction), `StepIsAirbenderClaim` (one `RV.step` is one step of the Airbender
machine, Sail's `execute` plus the listed changes, on everything a program can see) and `MachineChecksClaim`
(Sail's reset, what Airbender overrides and one machine step on representative words).
[Provenance and regeneration](sail/README.md) record model/compiler/runtime pins. Generation fidelity (Sail to Lean)
is trusted, not proved.
Representation lemmas live in `Slop/Arithmetic/Word.lean`.

## Build budget

[Lean strategies](docs/shared/lean-strategies.md) section 2 sets the budget: about 10 s per module, 30 s at most.
`verify.sh` fails any module of the build targets over 30 s ([module_budget.py](lean/scripts/module_budget.py)). A
module's time is the CPU time (user + sys) of its `lean` process compiled alone, imports built.

The 30 s are CPU time on the reference machine, the Apple M3 Max (14 cores) this project is developed on. Before checking,
the gate compiles a pinned calibration file ([budget_calibration.lean](lean/scripts/budget_calibration.lean), Lean
core only: kernel reduction, `omega`, `simp`; its sha256 is pinned in the script) and scales the limit by its CPU time
here / there (`CALIBRATION_REFERENCE_S` = 4.0 s, the lowest of 20 runs on the reference machine with Lean 4.35.0,
which ranged 3.98-4.83 s; lowest of three runs here, run at once; factor clamped to 0.5-4). A runner twice as slow per core gets 60 s. On the
reference machine itself (identified by OS, architecture, CPU model and core count) the factor is capped at 1.05:
there it is 1 by definition, and load or thermal throttling inflated the measurement to as much as 1.23. The
ledger keeps raw CPU times; the limit and the factor are printed and written at the end of `module-budget.tsv`.
Changing the calibration file or the toolchain needs a new reference time measured on the reference machine (Lean
4.35 compiles the file in 4.0 s where 4.34.1 took 5.5 s, while our modules' total CPU time rose by 2%). Wall time is not
used: under parallel load it is off by 2–4×, and a module that elaborates in parallel finishes in less wall time
than it costs. Load only inflates CPU time (efficiency cores, shared caches), so a module under budget under load
is under budget alone. Three stages, each paying only for what the one before could not settle:
1. During `verify.sh`'s `lake build` a sampler reads each compiling module's CPU time from `ps` every 0.5 s.
2. Every target module is looked up in a ledger keyed by module and Lake's input hash (`depHash`, which covers the
   source and every import): an entry is valid exactly as long as Lake would not rebuild the module. A module with
   no entry (restored from Lake's artifact cache, or built outside `verify.sh`) is compiled again outside Lake,
   four at a time (`MODULE_BUDGET_JOBS`), its CPU time read exactly (`wait4`).
3. A module over budget in 1 or 2 is compiled again alone, at most twice; the lower time counts. Over the scaled
   limit alone (`MODULE_BUDGET_S` = 30 s on the reference machine) fails.

The ledger is the file `<LAKE_CACHE_DIR>.module-cpu.tsv`, beside (not inside) Lake's shared artifact cache, so
worktrees sharing the cache measure each module once per input hash; without the cache it is
`lean/.lake/module-cpu.tsv` (`MODULE_BUDGET_LEDGER` overrides). Without a ledger, stage 2 measures every module once:
about one cold build of CPU. `lean/.lake/module-budget.tsv` lists every module's time after a run, slowest first. The script needs Python 3.11 or
later (it reads the lakefile with tomllib).
Fix a module over budget by restructuring its proof (lean-strategies 2.1), never by raising the limit.

## Reproduce

```sh
./verify.sh
```

CI runs the same `verify.sh` in an ubuntu:24.04 container (`.github/workflows/lean-formal-verification.yml`);
[ci/README.md](ci/README.md) describes the job, its caches, its memory per thread count, and how to reproduce it
locally in Docker.

The audit lists theorem axiom dependencies. The checked claims use only standard
Lean axioms; no `sorry` or project axioms are admitted. Importer tests check rejection paths; the import's
correctness is the claims of the import guide, up to its trusted transcription step. Subsequent work is in [the plan](docs/FORMAL_VERIFICATION_PLAN.md).
The [review check](lean/check_review.py) uses Lean's compiled declaration locations to require an explicit
axiom root for every source-declared public theorem in `Human/` and `Slop/Final/`. It also resolves
guide declaration names and local file/heading links. Source-only Rust/Sail names
are listed separately in the script; their fidelity remains a trust boundary.
It also checks context/trace import separation.

For the integrated trace proof and regressions:

```sh
cd lean
lake build Tests.TraceImport Checks.TraceAxioms
lake env lean test/Checks/TraceAxioms.lean
```

This focused target checks ADD/SUB, word-memory and jump/branch/SLT native
clock/port artifacts, rollover/rejection fixtures and timestamp/address/value importer guards. The primary public surface is
[Trace/RVSoundness.lean](lean/human/Human/Trace/RVSoundness.lean) (proof in
[slop](lean/slop/Slop/Final/Trace/RVSoundness.lean)), with the native
matching and initial-clock conditions in [Context/Model.lean](lean/human/Human/Helpers/Context/Model.lean).
The history fixtures ([TraceHistory](lean/test/Tests/TraceHistory.lean), [PooledHistory](lean/test/Tests/PooledHistory.lean))
check rejection of an unmatched previous-write timestamp, complete per-address paths with interleaved accesses and
changing values, and that a changed operand/result pair satisfies the local ADD constraints but is rejected by
native matching because the fabricated read has no matching previous write.
The nonzero-register fixture checks the explicit initialization writes required
by Clean's zero-initial online-memory semantics.
The [initial-image constructor](lean/human/Human/Helpers/Memory/InitialImageRV.lean) reads
the public `RV.State` directly (a cell outside `RV.readable` makes the construction fail). The modeled word-ROM
table fixtures ([TraceROM](lean/test/Tests/TraceROM.lean)) check rejection of a wrong value and of a missing address.

With the Lean 4 VS Code extension, open `lean/` and inspect a scratch
file in the Infoview:

```lean
import Human.Circuits.AddSub.Artifact
#print Airbender.AddSub.importedConstraints
```
