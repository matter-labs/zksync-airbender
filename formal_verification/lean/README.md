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

Start in `Review/`. Public theorems refer to their implementations in `Proofs/`.
`Theorems.lean` contains soundness claims; numeric constraint lemmas stay in
`Proofs/`. For branches, read [the claim](Airbender/Review/JumpBranchSlt/Theorems.lean)
and [its contract](Airbender/Review/JumpBranchSlt/Branch.lean): satisfying the imported
constraints under the listed interfaces implies the original Sail branch step.
Named columns are checked against the artifact metadata in `Artifact.lean`.
The importer is an unchecked connection to the source JSON. Upstream code stays
in `vendor/`, `generated/` and `.lake/packages`; see the trust boundaries below.

| Question | Entry point |
| --- | --- |
| What does soundness mean? | [Shared properties and circuit relation](Airbender/Review/Properties.lean) |
| What do words and field parameters mean? | [Word encoding](Airbender/Review/Word.lean), [field selection](Airbender/Review/Field.lean) |
| Which constraints, mapping and assumptions? | [ADD/SUB model](Airbender/Review/AddSub/Model.lean), [comparison model](Airbender/Review/JumpBranchSlt/Model.lean) |
| What do lookups enforce? | [Native Clean range tables](Airbender/Review/RangeChecks.lean), [shared fixed tables](Airbender/Review/Lookups.lean) |
| How can global state matching supply PC bounds? | [Shared PC-state contract](Airbender/Review/PCState/Model.lean) and [range-transfer claim](Airbender/Review/PCState/Theorems.lean) |
| Which Sail behavior? | [Sail interface](Airbender/Review/Sail.lean) |
| Which custom arithmetic behavior? | [Modular definitions and contracts](Airbender/Review/AddSub/Modular.lean) |
| What is proved for one BLAKE2 G row? | [Combined row contract](Airbender/Review/Blake2G/Row.lean), `Row.soundness` in [the public claims](Airbender/Review/Blake2G/Theorems.lean) |
| What is proved for extended BLAKE2 control? | [Combined row contract](Airbender/Review/Blake2Round/Row.lean), `Row.soundness` in [the public claims](Airbender/Review/Blake2Round/Theorems.lean). Preparation/SIGMA, eight G calls, both writebacks, x12 and all forty addresses share one imported witness; source-word/pointer bounds, caller round mask and memory transport remain interfaces. |
| What is proved for bigint delegation? | [Control](Airbender/Review/Bigint/Control.lean), [additive](Airbender/Review/Bigint/Additive.lean) and [equality](Airbender/Review/Bigint/Equality.lean) and [multiplication](Airbender/Review/Bigint/Multiplication.lean) and [address](Airbender/Review/Bigint/Addresses.lean) contracts, [public claims](Airbender/Review/Bigint/Theorems.lean). All seven pure 256-bit operations checked, including both product halves and overflow (multiplication: BabyBear), with actual written limbs and x12 responses. Modeled-setup claims derive ranges from native lookups; native port addresses/alignment checked under pointer bounds; setup binding, memory transport and full ABI remain open. |
| What is the actual theorem? | [ADD/SUB soundness](Airbender/Review/AddSub/Theorems.lean), [comparison soundness](Airbender/Review/JumpBranchSlt/Theorems.lean) |
| What requires trust or further review? | [Trust boundaries](TRUST_AND_REVIEW.md) |

The theorem's premise has three parts:

| Part | Meaning |
| --- | --- |
| Enforced constraints | 30 assertions from `structured_statements` and six 16-bit queries from `range_check_16_lookup_expressions` |
| Word mapping | Input limbs and destination index encoded into named variables; destination/final-PC limbs decoded as canonical field values |
| Interface assumptions | Decoded selectors/preprocessing, operand/immediate bounds, initial-PC bounds and agreement with Sail register/PC reads |

Operand bounds remain decoder/memory obligations: these six queries cover result,
final-PC and modular-comparison limbs, not the input operands. The static range
table supplies its own rows; Clean lookup membership proves the result bounds.
Operand-bound assumptions apply only to nonzero destination writes.
The imported equations prove Boolean execute/selector flags; the decoder still
supplies instruction identity and exclusivity.
The cryptographic lookup argument and compiled-gate correspondence remain pending.
`SoundnessUnder` applies the shared soundness definition directly. [Artifact.lean](Airbender/Review/AddSub/Artifact.lean) is the import declaration;
[Proofs.lean](Airbender/Proofs/AddSub.lean) holds the calculation details.

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

This focused target checks both native clock/port artifacts, rollover/rejection
fixtures and timestamp/address/value importer guards. The public surface is
[Trace/Theorems.lean](Airbender/Review/Trace/Theorems.lean), with the native
matching and initial-clock conditions in [Trace/Model.lean](Airbender/Review/Trace/Model.lean).
The history fixtures check rejection of an unmatched previous-write timestamp
and complete per-address paths with interleaved accesses and changing values.
A changed operand/result pair satisfies the local ADD constraints but is rejected
by native matching because the fabricated read has no matching previous write.
The nonzero-register fixture checks the explicit initialization writes required
by Clean's zero-initial online-memory semantics.

With the Lean 4 VS Code extension, open this project folder and inspect a scratch
file in the Infoview:

```lean
import Airbender.Review.AddSub.Artifact
#print Airbender.AddSub.importedConstraints
```
