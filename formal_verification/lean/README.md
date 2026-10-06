# Circuit verification

## What is checked

For ADD, ADDI and SUB, **every assignment satisfying the imported constraints**
produces the destination word required by the actual Sail RV32 execution clause,
under explicit decoder, range and register-read assumptions. Sail retires
successfully with the same state effects as writing that word through its register
accessor. Two satisfying assignments with the same inputs have equal result limbs.

The proof path is:

```text
no-cache JSON → native Clean constraints → arithmetic lemmas → Sail execution
```

Clean is the only expression/constraint model used by these proofs. There is no
local arithmetic interpreter or translation-equivalence layer.

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
The importer is an unchecked connection to the source JSON. Upstream code stays
in `vendor/`, `generated/` and `.lake/packages`; see the trust boundaries below.

| Question | Entry point |
| --- | --- |
| What do soundness and determinism mean? | [Shared properties and circuit relation](Airbender/Review/Properties.lean) |
| What do words and field parameters mean? | [Word encoding](Airbender/Review/Word.lean), [field selection](Airbender/Review/Field.lean) |
| Which constraints, mapping and assumptions? | [Circuit model](Airbender/Review/AddSub/Model.lean) |
| Which Sail behavior? | [Sail interface](Airbender/Review/Sail.lean) |
| What is the actual theorem? | [Soundness and determinism, generic and BabyBear](Airbender/Review/AddSub/Theorems.lean) |
| What requires trust or further review? | [Trust boundaries](TRUST_AND_REVIEW.md) |

The theorem's premise has three parts:

| Part | Meaning |
| --- | --- |
| Enforced constraints | All 30 assertions in `importedConstraints`, generated from the JSON's `structured_statements` |
| Word mapping | Which assignment variables represent the input and output limbs |
| Interface assumptions | Decoded selectors/preprocessing, 16-bit limb bounds and agreement with Sail register reads |

These assumptions are needed because decoder and lookup guarantees have not yet
been proved. They supply the inputs' interpretation; the constraints force the
arithmetic result. `SoundnessUnder` and `DeterminismUnder` use the shared properties
directly. [Artifact.lean](Airbender/Review/AddSub/Artifact.lean) is the import declaration;
[Proofs.lean](Airbender/Proofs/AddSub.lean) holds the calculation details.

## Scope

- Covered: ADD/ADDI/SUB destination-word soundness and observable word determinism;
  destination register must be nonzero.
- Generic: Clean `FiniteField` with characteristic greater than `196608`.
  Shared algebra lemmas retain their weaker field/ring requirements.
- Concrete: BabyBear, using the original JSON coefficient serialization.
- Pending: PC/full architectural step, `x0` preprocessing, other instruction
  branches, completeness, decoder/lookups/memory and compiled-gate correspondence.
- Large-field proof lemmas are reusable; actual Proth120 JSON import is pending.

## Clean and Sail

Clean is pinned at `1e563b9c27991b3795eb440c1ee0757edb4ce8b1`. Its required modules
build unchanged under our existing Lean/Mathlib `v4.31.0` pins. We use its native
`Expression`, `FlatOperation.assert`, `Environment` and `ConstraintsHoldFlat`.
The witness-generation DSL and full `FormalCircuit` bundle are not used.
Airbender's two-16-bit-limb representation is preserved.

The reference uses [unmodified upstream Sail clauses](vendor/sail-riscv/source/model/extensions/I/base_insts.sail)
and [their generated Lean definitions](generated/sail-rv32/SailRV32.lean).
The original ADD/SUB clause is `execute(RTYPE(...))`; ADDI is `execute(ITYPE(...))`.
The Lean interface calls `execute_RTYPE` and `execute_ITYPE` directly.
[Provenance and regeneration](generated/sail-rv32/README.md) record model/compiler/runtime
pins. This is a register/effect slice with 32-bit words; PC sequencing and memory
are outside its current scope. There is no local arithmetic-specification relation.
Representation and execution lemmas live in `Proofs/Arithmetic/Word.lean` and
`Proofs/Sail/RiscV.lean`. Determinism follows from soundness and uniqueness of this
same Sail specification.

## Reproduce

Run from `formal_verification/lean`:

```sh
lake build
lake env lean Airbender/Checks/Axioms.lean
lake exe airbender_tests
```

The audit lists theorem axiom dependencies. The checked claims use only standard
Lean axioms; no `sorry` or project axioms are admitted. Importer tests are not
proofs of faithful parsing. Subsequent work is in [the plan](FORMAL_VERIFICATION_PLAN.md).

With the Lean 4 VS Code extension, open this project folder and inspect a scratch
file in the Infoview:

```lean
import Airbender.Review.AddSub.Artifact
#print Airbender.AddSub.importedConstraints
```
