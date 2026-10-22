# Circuit verification

## What is checked

[Verification status](VERIFICATION_STATUS.md) lists every circuit, checked coverage
and open tasks. It is updated after each completed task.

The [findings audit](FINDINGS.md) records accepted counterexamples and unresolved
bindings, with links to their assumptions and evidence.

The proof path is:

```text
no-cache JSON → native Clean constraints → Sail execution (or pinned custom spec)
```

Claims are conditional on explicit interfaces. The imported richer constraints are
the current target; compiled-gate and cryptographic argument soundness are deferred.

## Read these first

The [Review guide](Airbender/Review/README.md) has two routes:
[individual circuit review](Airbender/Review/Circuits/README.md) and
[whole-trace review](Airbender/Review/Trace/README.md).
Directory READMEs explain the relevant references, mappings, assumptions and scope.

[Properties](Airbender/Review/Helpers/Properties.lean) defines soundness,
completeness and the observable circuit relation. Shared helpers are grouped by
[topic](Airbender/Review/Helpers/README.md); properties do not require decoder or
memory-history review. Supporting calculations remain in Proofs; Import has a
separate fidelity boundary.

## Clean and Sail

Clean is pinned at `1e563b9c27991b3795eb440c1ee0757edb4ce8b1`.
[Preparation](scripts/prepare_clean.py) checks original source hashes before applying
Lean `v4.31.0` compatibility fixes: a tactic import, factory registration metadata,
and explicit proof reductions. Constraint semantics, algorithms and theorem
statements are unchanged; repaired proof terms are kernel-checked and axiom-audited.
The original Keccak permutation reference compiles unchanged; the [Theta column](Airbender/Review/Circuits/Keccak/Theta.lean) and [two-call Chi row](Airbender/Review/Circuits/Keccak/Chi.lean) claims use its `thetaXor` and `chi` directly. We use Clean's native
`Expression`, `FlatOperation.assert`, `StaticTable`, `FlatOperation.lookup`,
`Environment` and `ConstraintsHoldFlat`.
The witness-generation DSL and full `FormalCircuit` bundle are not used.
Airbender's two-16-bit-limb representation is preserved.

The reference uses [unmodified upstream Sail clauses](vendor/sail-riscv/source/model/extensions/I/base_insts.sail)
and [their generated Lean definitions](generated/sail-rv32/SailRV32.lean).
The original ADD/SUB clause is `execute(RTYPE(...))`; ADDI is `execute(ITYPE(...))`;
LUI/AUIPC use `execute(UTYPE(...))`. The Lean interface calls the generated
`execute_RTYPE`, `execute_ITYPE` and `execute_UTYPE` directly.
Unsigned division uses the original `execute_DIV`/`execute_REM` clauses from
[the M-extension source](vendor/sail-riscv/source/model/extensions/M/mext_insts.sail).
[Provenance and regeneration](generated/sail-rv32/README.md) record model/compiler/runtime
pins. The normal four-byte nextPC assignment is extracted verbatim from upstream
`run_hart_active` and compiled by Sail, then composed with execution and `tick_pc`.
Extraction and path selection remain unchecked connections; full fetch/exception
handling and memory arguments are outside the claim. Standard instructions have no local replacement spec;
custom arithmetic uses the [pinned project definitions](vendor/airbender/00-master.md#supported-instruction-set-and-custom-operations).
Representation and execution lemmas live in `Proofs/Arithmetic/Word.lean` and
`Proofs/Sail/RiscV.lean`.

The Blake2 round query proofs reuse [generic row expressions](Airbender/Proofs/Blake2G/FrameQueryEntries.lean)
and [row arithmetic](Airbender/Proofs/Blake2G/FrameQueryRows.lean). Separate
[bindings](Airbender/Proofs/Blake2G/FrameQueryBindings.lean) check the actual imported G
lookups; each native column and diagonal call checks its own imported expressions,
then supplies its frame to the shared arithmetic. Existing public theorem statements
and actual table membership obligations remain unchanged. Definition-only modules and
family-local native effects avoid the combined delegation-operation implementation.
The [focused boundary check](scripts/check_proof_boundaries.py) verifies these source
import paths without compiling.

## Reproduce

Run from `formal_verification/lean`:

```sh
python3 scripts/prepare_clean.py
python3 - <<'PYTESTS'
from pathlib import Path
import subprocess
modules = [".".join(path.with_suffix("").parts)
           for path in sorted(Path("Tests").rglob("*.lean"))]
subprocess.run(["lake", "build", "Airbender", "airbender_import",
                "airbender_tests", "Airbender.Checks.Axioms", *modules], check=True)
PYTESTS
lake env lean Airbender/Checks/Axioms.lean
lake exe airbender_tests
python3 scripts/check_review.py
python3 scripts/check_proof_boundaries.py
```

The audit lists theorem axiom dependencies. The checked claims use only standard
Lean axioms; no `sorry` or project axioms are admitted. Importer tests are not
proofs of faithful parsing. Subsequent work is in [the plan](FORMAL_VERIFICATION_PLAN.md).
The [review check](scripts/check_review.py) uses Lean's compiled declaration locations to require an explicit
axiom root for every source-declared public theorem in `Review/`. It also resolves
guide declaration names and local file/heading links. Source-only Rust/Sail names
are listed separately in the script; their fidelity remains a trust boundary.
It also checks context/trace import separation and the documented proof-assembly dependencies.

For the integrated trace proof and regressions:

```sh
lake build Tests.TraceImport Airbender.Checks.TraceAxioms
lake env lean Airbender/Checks/TraceAxioms.lean
```

This focused target checks ADD/SUB, word-memory and jump/branch/SLT native
clock/port artifacts, rollover/rejection
fixtures and timestamp/address/value importer guards. The primary public surface is
[Trace/Soundness.lean](Airbender/Review/Trace/Soundness.lean), with the native
matching and initial-clock conditions in [Trace/Model.lean](Airbender/Review/Helpers/Context/Model.lean).
The history fixtures check rejection of an unmatched previous-write timestamp
and complete per-address paths with interleaved accesses and changing values.
A changed operand/result pair satisfies the local ADD constraints but is rejected
by native matching because the fabricated read has no matching previous write.
The nonzero-register fixture checks the explicit initialization writes required
by Clean's zero-initial online-memory semantics.
The [initial-image constructor](Airbender/Review/Helpers/Memory/InitialImage.lean) reads
public Sail state directly. Its fixtures check nonzero GPRs, x0, little-endian
RAM and rejection of missing cells; extraction proves initial bounds and uniqueness.

With the Lean 4 VS Code extension, open this project folder and inspect a scratch
file in the Infoview:

```lean
import Airbender.Review.Circuits.AddSub.Artifact
#print Airbender.AddSub.importedConstraints
```
