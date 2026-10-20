# Circuit verification

Lean proofs that Airbender's circuits (the no-cache constraint JSON in `cs/compiled_circuits/`) implement RISC-V as
the official Sail model specifies it (or the pinned custom spec for Airbender's own operations).

**Check everything:** `./verify.sh` (prepares the pinned Clean, builds the spec and all proofs, checks that the spec
does not import the proofs, runs the regressions and the axiom audits, checks the review guides).

## Layout

- `lean/human/` — **what a human reads**: everything a claim's meaning depends on. The circuit models, references,
  artifacts and interface assumptions (`Human/Circuits/`), the shared context (`Human/Helpers/`, starting from
  `Human/Helpers/Properties.lean`), whole-trace execution contracts (`Human/Trace/`) and the JSON importer that turns
  an artifact into Clean constraints (`Human/Import/`). It imports only Mathlib, Clean, the Sail model and itself
  (`./verify.sh` step 1). Its directory READMEs are the review guide.
- `lean/slop/` — everything else (kernel-checked, not meant to be read): supporting calculations, proof assembly and
  artifact guards (`Slop/`), and the public claim theorems (`Slop/Final/`, laid out like `Human/`).
- `lean/test/` — regressions and fixtures (`Tests/`), the axiom audits (`Checks/`).
- `lean/sail-rv32/` — the generated Sail RV32 slice (Lean) with its provenance; `sail/` — its generator
  (`sail/generate_sail.py`, `sail/sail_slice.ml`, `sail/SailPlatform.lean`) and the reviewed upstream Sail sources (`sail/sail-riscv/`).
- `sail/fetch-lean-sail.sh` — fetches the pinned lean-sail with our Lean 4.34 patch (`sail/patches/`; no upstream
  licence, so never committed); `lean/check_review.py` — review-guide and audit-coverage check.
- `docs/` — [status](docs/VERIFICATION_STATUS.md), [trust and review boundaries](docs/TRUST_AND_REVIEW.md),
  [plan](docs/FORMAL_VERIFICATION_PLAN.md), and the pinned Airbender reference (`docs/airbender/00-master.md`).

## What is checked

[Verification status](docs/VERIFICATION_STATUS.md) lists every circuit, checked coverage
and open tasks. It is updated after each completed task.

The proof path is:

```text
no-cache JSON → native Clean constraints → Sail execution (or pinned custom spec)
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
memory-history review. Supporting calculations remain in `slop/`; `Human/Import/` has a
separate fidelity boundary.

## Clean and Sail

Lean and Mathlib are `v4.34.1`. Clean is pinned at tag `v4.33.1`
(`93c9d1ef45be9f687214625d7857889cf2485504`); the modules used here build unchanged on Lean `v4.34.1`.
The original Keccak permutation reference compiles unchanged; the [Theta column](lean/human/Human/Circuits/Keccak/Theta.lean) and [two-call Chi row](lean/human/Human/Circuits/Keccak/Chi.lean) claims use its `thetaXor` and `chi` directly. We use Clean's native
`Expression`, `FlatOperation.assert`, `StaticTable`, `FlatOperation.lookup`,
`Environment` and `ConstraintsHoldFlat`.
The witness-generation DSL and full `FormalCircuit` bundle are not used.
Airbender's two-16-bit-limb representation is preserved.

The reference uses [unmodified upstream Sail clauses](sail/sail-riscv/source/model/extensions/I/base_insts.sail)
and [their generated Lean definitions](lean/sail-rv32/SailRV32.lean).
The original ADD/SUB clause is `execute(RTYPE(...))`; ADDI is `execute(ITYPE(...))`;
LUI/AUIPC use `execute(UTYPE(...))`. The Lean interface calls the generated
`execute_RTYPE`, `execute_ITYPE` and `execute_UTYPE` directly.
Unsigned division uses the original `execute_DIV`/`execute_REM` clauses from
[the M-extension source](sail/sail-riscv/source/model/extensions/M/mext_insts.sail).
[Provenance and regeneration](lean/sail-rv32/README.md) record model/compiler/runtime
pins. The normal four-byte nextPC assignment is extracted verbatim from upstream
`run_hart_active` and compiled by Sail, then composed with execution and `tick_pc`.
Extraction and path selection remain unchecked connections; full fetch/exception
handling and memory arguments are outside the claim. Standard instructions have no local replacement spec;
custom arithmetic uses the [pinned project definitions](docs/airbender/00-master.md#supported-instruction-set-and-custom-operations).
Representation and execution lemmas live in `Slop/Arithmetic/Word.lean` and
`Slop/Sail/RiscV.lean`.

## Reproduce

```sh
./verify.sh
```

The audit lists theorem axiom dependencies. The checked claims use only standard
Lean axioms; no `sorry` or project axioms are admitted. Importer tests are not
proofs of faithful parsing. Subsequent work is in [the plan](docs/FORMAL_VERIFICATION_PLAN.md).
The [review check](lean/check_review.py) uses Lean's compiled declaration locations to require an explicit
axiom root for every source-declared public theorem in `Human/` and `Slop/Final/`. It also resolves
guide declaration names and local file/heading links. Source-only Rust/Sail names
are listed separately in the script; their fidelity remains a trust boundary.
It also checks context/trace import separation and the documented proof-assembly dependencies.

For the integrated trace proof and regressions:

```sh
cd lean
lake build Tests.TraceImport Checks.TraceAxioms
lake env lean test/Checks/TraceAxioms.lean
```

This focused target checks ADD/SUB, word-memory and jump/branch/SLT native
clock/port artifacts, rollover/rejection
fixtures and timestamp/address/value importer guards. The primary public surface is
[Trace/Soundness.lean](lean/slop/Slop/Final/Trace/Soundness.lean), with the native
matching and initial-clock conditions in [Trace/Model.lean](lean/human/Human/Helpers/Context/Model.lean).
The history fixtures check rejection of an unmatched previous-write timestamp
and complete per-address paths with interleaved accesses and changing values.
A changed operand/result pair satisfies the local ADD constraints but is rejected
by native matching because the fabricated read has no matching previous write.
The nonzero-register fixture checks the explicit initialization writes required
by Clean's zero-initial online-memory semantics.
The [initial-image constructor](lean/human/Human/Helpers/Memory/InitialImage.lean) reads
public Sail state directly. Its fixtures check nonzero GPRs, x0, little-endian
RAM and rejection of missing cells; extraction proves initial bounds and uniqueness.

With the Lean 4 VS Code extension, open `lean/` and inspect a scratch
file in the Infoview:

```lean
import Human.Circuits.AddSub.Artifact
#print Airbender.AddSub.importedConstraints
```
