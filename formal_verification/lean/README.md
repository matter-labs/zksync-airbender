# Circuit verification

## What is checked

[Verification status](VERIFICATION_STATUS.md) lists every circuit, checked coverage
and open tasks. It is updated after each completed task.

The proof path is:

```text
no-cache JSON → native Clean constraints → Sail execution (or pinned custom spec)
```

Claims are conditional on explicit interfaces. The imported richer constraints are
the current target; compiled-gate and cryptographic argument soundness are deferred.

## Read these first

The source tree follows the review boundary:

```text
Airbender/
  Review/    definitions, assumptions, artifact selection and public claims
  Proofs/    supporting proofs checked by Lean
  Import/    JSON parser, coefficient decoding and emission; audit separately
  Checks/    axiom audit
```

Start with a trace claim and its public boundary. Its implementation lives in
`Proofs/`; reading the calculation lemmas is optional. The restricted
arithmetic/word-memory trace and several separate family traces are checked;
their pooled composition remains open. The next priority is one small composed
review contract, deriving circuit interfaces through shared memory history.

| Question | Entry point |
| --- | --- |
| What is proved for a whole trace? | [Trace claims](Airbender/Review/Trace/Theorems.lean): `native_boot_soundness` covers ADD/ADDI/SUB/LUI/AUIPC + LW/SW from the native zero-initialized seed. `airbender_soundness` supports a general physical image; `sail_soundness` uses unchanged Sail and excludes LW-to-x0. |
| What inputs and assumptions does it use? | [Public boundary and explicit ISA profile](Airbender/Review/Trace/Execution.lean), [native boot boundary](Airbender/Review/Trace/NativeMemory.lean). |
| How do external reads compose? | [Independent stream boundary and custom clause](Airbender/Review/Trace/NonDeterminism.lean); the mixed-trace claim proves exact stream consumption. |
| What do the shared definitions mean? | [Soundness](Airbender/Review/Properties.lean), [word encoding](Airbender/Review/Word.lean), [fields](Airbender/Review/Field.lean), [Sail interface](Airbender/Review/Sail.lean). |
| What is covered elsewhere or still open? | [Circuit and task tables](VERIFICATION_STATUS.md), with links to each family's claims. |
| What requires separate trust review? | [Trust boundaries](TRUST_AND_REVIEW.md): importer, Sail generation, modeled tables and logical argument enforcement. |

Trace proofs derive operand bounds from public initialization, preserved writes
and latest-write/read consistency. They also derive the row decoder and register
interfaces. These are not caller-supplied per-row assumptions. Public initial
state/program, field and platform conditions, and logical matching remain explicit.
The status tables identify additional unresolved conditions, including jump
terminal-PC normalization, that any pooled claim must retain until discharged.

Local circuit claims, such as [ADD/SUB](Airbender/Review/AddSub/Theorems.lean),
still expose conditional row interfaces for reuse by the trace proofs. Their
operand bounds are internal proof obligations, not the trace review contract.
Named columns are checked against artifact metadata; faithful JSON import itself
is trusted. Upstream sources remain in `vendor/`, `generated/` and `.lake/packages`.

## Clean and Sail

Clean is pinned at `1e563b9c27991b3795eb440c1ee0757edb4ce8b1`.
[Preparation](scripts/prepare_clean.py) checks original source hashes before applying
Lean `v4.31.0` compatibility fixes: a tactic import, factory registration metadata,
and explicit proof reductions. Constraint semantics, algorithms and theorem
statements are unchanged; repaired proof terms are kernel-checked and axiom-audited.
The original Keccak permutation reference now compiles; the [Theta column claim](Airbender/Review/Keccak/Theta.lean) uses its `thetaXor` directly. We use Clean's native
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

## Reproduce

Run from `formal_verification/lean`:

```sh
python3 scripts/prepare_clean.py
lake build
lake env lean Airbender/Checks/Axioms.lean
lake exe airbender_tests
```

The audit lists theorem axiom dependencies. The checked claims use only standard
Lean axioms; no `sorry` or project axioms are admitted. Importer tests are not
proofs of faithful parsing. Subsequent work is in [the plan](FORMAL_VERIFICATION_PLAN.md).

For the restricted subset's native timestamp/memory milestones:

```sh
lake build Tests.TraceImport Airbender.Checks.TraceAxioms
lake env lean Airbender/Checks/TraceAxioms.lean
```

This focused target checks ADD/SUB, word-memory and jump/branch/SLT native
clock/port artifacts, rollover/rejection
fixtures and timestamp/address/value importer guards. The public surface is
[Trace/Theorems.lean](Airbender/Review/Trace/Theorems.lean), with the native
matching and initial-clock conditions in [Trace/Model.lean](Airbender/Review/Trace/Model.lean).
The history fixtures check rejection of an unmatched previous-write timestamp
and complete per-address paths with interleaved accesses and changing values.
A changed operand/result pair satisfies the local ADD constraints but is rejected
by native matching because the fabricated read has no matching previous write.
The nonzero-register fixture checks the explicit initialization writes required
by Clean's zero-initial online-memory semantics.
The [initial-image constructor](Airbender/Review/Trace/InitialImage.lean) reads
public Sail state directly. Its fixtures check nonzero GPRs, x0, little-endian
RAM and rejection of missing cells; extraction proves initial bounds and uniqueness.

With the Lean 4 VS Code extension, open this project folder and inspect a scratch
file in the Infoview:

```lean
import Airbender.Review.AddSub.Artifact
#print Airbender.AddSub.importedConstraints
```
