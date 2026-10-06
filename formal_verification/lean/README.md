# Circuit verification

## What is checked

For ADD, ADDI, SUB, LUI and AUIPC, **every assignment satisfying the imported constraints**
produces the destination word required by the actual Sail RV32 execution clause,
under explicit decoder, operand-bound and register/PC-read assumptions. Sail retires
successfully with the same state effects as writing that word through its register
accessor. Result-limb bounds follow from the imported range lookups.
Writes to x0 (including NOP) preserve Sail's state: original reads must succeed,
but their values and encoded immediates need not equal the circuit's zero operands.
ADDMOD/SUBMOD/MULMOD/FMAMOD destination values are proved against the pinned
project specification, including canonical reduction and Montgomery scaling.
Their architectural register/PC binding is still pending.

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
| What does soundness mean? | [Shared properties and circuit relation](Airbender/Review/Properties.lean) |
| What do words and field parameters mean? | [Word encoding](Airbender/Review/Word.lean), [field selection](Airbender/Review/Field.lean) |
| Which constraints, mapping and assumptions? | [Circuit model](Airbender/Review/AddSub/Model.lean) |
| What do range lookups enforce? | [Native Clean range table](Airbender/Review/RangeChecks.lean) |
| Which Sail behavior? | [Sail interface](Airbender/Review/Sail.lean) |
| Which custom arithmetic behavior? | [Modular definitions and contracts](Airbender/Review/AddSub/Modular.lean) |
| What is the actual theorem? | [Soundness, generic and BabyBear](Airbender/Review/AddSub/Theorems.lean) |
| What requires trust or further review? | [Trust boundaries](TRUST_AND_REVIEW.md) |

The theorem's premise has three parts:

| Part | Meaning |
| --- | --- |
| Enforced constraints | 30 assertions from `structured_statements` and six 16-bit queries from `range_check_16_lookup_expressions` |
| Word mapping | Input limbs and destination index encoded into named variables; result limbs decoded as canonical field values |
| Interface assumptions | Decoded selectors/preprocessing, operand/immediate bounds, AUIPC PC bounds and agreement with Sail register/PC reads |

Operand bounds remain decoder/memory obligations: these six queries cover result,
final-PC and modular-comparison limbs, not the input operands. The static range
table supplies its own rows; Clean lookup membership proves the result bounds.
Operand-bound assumptions apply only to nonzero destination writes.
The imported equations prove Boolean execute/selector flags; the decoder still
supplies instruction identity and exclusivity.
The cryptographic lookup argument and compiled-gate correspondence remain pending.
`SoundnessUnder` applies the shared soundness definition directly. [Artifact.lean](Airbender/Review/AddSub/Artifact.lean) is the import declaration;
[Proofs.lean](Airbender/Proofs/AddSub.lean) holds the calculation details.

## Scope

- Covered: ADD/ADDI/SUB/LUI/AUIPC destination effects, including x0/NOP preprocessing,
  and logical 16-bit range membership.
- Generic standard arithmetic: prime field `ZMod p`, with `p > 196608`.
  Shared algebra lemmas retain their weaker field/ring requirements.
- Concrete: BabyBear, using the original JSON coefficient serialization.
- Custom arithmetic: all four modular destination-value branches in BabyBear.
  Operand residues and decoded selectors are interface premises; canonical output
  follows from the imported equations and range checks.
- PC equations: a satisfying assignment advances PC by four without 32-bit overflow,
  assuming bounded initial limbs. Final bounds follow from lookups. The serialized
  inverse coefficient is checked for BabyBear; the generic lemma requires that identity.
- Pending: PC/full architectural step, other instruction
  branches, completeness, decoder, lookup/memory arguments and compiled-gate correspondence.
- Large-field proof lemmas are reusable; actual Proth120 JSON import is pending.

## Clean and Sail

Clean is pinned at `1e563b9c27991b3795eb440c1ee0757edb4ce8b1`. Its required modules
build unchanged under our existing Lean/Mathlib `v4.31.0` pins. We use its native
`Expression`, `FlatOperation.assert`, `StaticTable`, `FlatOperation.lookup`,
`Environment` and `ConstraintsHoldFlat`.
The witness-generation DSL and full `FormalCircuit` bundle are not used.
Airbender's two-16-bit-limb representation is preserved.

The reference uses [unmodified upstream Sail clauses](vendor/sail-riscv/source/model/extensions/I/base_insts.sail)
and [their generated Lean definitions](generated/sail-rv32/SailRV32.lean).
The original ADD/SUB clause is `execute(RTYPE(...))`; ADDI is `execute(ITYPE(...))`;
LUI/AUIPC use `execute(UTYPE(...))`. The Lean interface calls the generated
`execute_RTYPE`, `execute_ITYPE` and `execute_UTYPE` directly.
[Provenance and regeneration](generated/sail-rv32/README.md) record model/compiler/runtime
pins. PC accessors and `tick_pc` are also generated, but full PC sequencing and memory
are outside its current scope. Standard instructions have no local replacement spec;
custom arithmetic uses the [pinned project definitions](vendor/airbender/00-master.md#supported-instruction-set-and-custom-operations).
Representation and execution lemmas live in `Proofs/Arithmetic/Word.lean` and
`Proofs/Sail/RiscV.lean`.

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
