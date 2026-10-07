# Circuit verification

## What is checked

For ADD, ADDI, SUB, LUI and AUIPC, **every assignment satisfying the imported constraints**
produces the destination word and final PC required by the normal decoded four-byte
Sail RV32 path, under explicit decoder, input-bound and register/PC-read assumptions.
The theorem checks the same native state effects as the projected register and PC
writes. Result and final-PC bounds follow from imported range lookups; the PC
advance excludes 32-bit overflow.
Writes to x0 (including NOP) discard the destination and still advance PC. Original
reads must succeed, but need not equal the circuit's preprocessed zero operands.
ADDMOD/SUBMOD/MULMOD/FMAMOD destination values are proved against the pinned
project specification, including canonical reduction and Montgomery scaling.
Native Sail register and PC effects are checked for all four, including old-
destination reads, source/destination aliasing and x0 preprocessing. The custom
arithmetic definition is locally written against the project spec, not an upstream
Sail instruction clause.
Nondeterminism writes have the project-specified architectural no-op and PC effects;
witness-generation hints and application I/O are excluded. Nondeterminism reads
still require an independent oracle-response interface.

Jump/branch/SLT has partial local coverage: imported equations, eight lookups,
flag bounds, timestamp carries and signed/unsigned destination bits. SLT, SLTI,
SLTU and SLTIU share one circuit model and theorem for
native Sail register/PC effects, including source/destination aliasing and 32-bit
PC wraparound. Operand bounds, initial low-PC bounds, four-byte alignment and the
final-PC high-limb bound remain explicit interfaces; the initial high-PC bound
comes from a lookup. Immediate words are bound to Sail's own sign extension.
Comparison writes to x0 instead use ADD/SUB's NOP preprocessing. One
[discarded-write contract](Airbender/Review/AddSub/Discarded.lean) covers all retained
RTYPE/ITYPE clauses, requiring successful original reads without operand-value
agreement or bounds. It proves native state preservation and PC advance, without
32-bit PC overflow, from that imported ADD/SUB row. Local branch conditions,
PC selection, wraparound and taken-target alignment are also proved. Local JAL/JALR
link and target equations cover PC+4 wrapping, x0 masking and JALR bit-0 cleanup;
the imported bit-1 check enforces four-byte target alignment. Architectural
branch/jump soundness is pending a Sail external-function binding; see the plan.
Fixed-table rows are modeled from Rust; their source
binding is unproved. See [its model](Airbender/Review/JumpBranchSlt/Model.lean) and
[its public claims](Airbender/Review/JumpBranchSlt/Theorems.lean).

Unsigned mul/div now imports all 43 equations and 16 range/fixed-table queries.
DIVU/REMU **for zero and nonzero divisors** have native Sail register/PC soundness, including
aliasing and a 16-bit PC carry; the PC advance excludes 32-bit overflow. The zero
flag, quotient/remainder result, output bounds and carry bounds are derived from
the imported relation. Decoder selection, dividend/initial-PC bounds and successful
native reads remain interfaces; divisor bounds follow from lookups. The four imported byte columns also imply an exact
integer product-plus-remainder relation for every selector, using a shared
arithmetic lemma with `p ≥ 2^29`. A proved strict remainder bound gives unique
unsigned division. Native Sail multiplication soundness is pending.
Start with [the division contract](Airbender/Review/MulDiv/Model.lean)
and [public claims](Airbender/Review/MulDiv/Theorems.lean).

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
| Which constraints, mapping and assumptions? | [ADD/SUB model](Airbender/Review/AddSub/Model.lean), [comparison model](Airbender/Review/JumpBranchSlt/Model.lean) |
| What do lookups enforce? | [Native Clean range tables](Airbender/Review/RangeChecks.lean), [shared fixed tables](Airbender/Review/Lookups.lean) |
| Which Sail behavior? | [Sail interface](Airbender/Review/Sail.lean) |
| Which custom arithmetic behavior? | [Modular definitions and contracts](Airbender/Review/AddSub/Modular.lean) |
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

## Scope

- Covered: ADD/ADDI/SUB/LUI/AUIPC destination and PC effects, including x0/NOP
  preprocessing, and logical 16-bit range membership. Fetch, interrupts and exceptions
  are outside the decoded-path claim.
- Generic standard theorem: prime field `ZMod p`, with `p > 196608` and the
  serialized PC-inverse identity. Destination arithmetic does not require that identity.
  Shared algebra lemmas retain their weaker field/ring requirements.
- Comparisons: SLT/SLTI/SLTU/SLTIU, with `p ≥ 4194304`, explicit decoder/read
  interfaces, PC alignment and the final high-PC bound. Native Sail defines signed
  ordering and immediate sign extension; the theorem permits 32-bit PC wraparound.
- Unsigned division: DIVU/REMU for all divisors, with `p ≥ 2^29` and the
  serialized PC-inverse identity; BabyBear discharges the identity. Remaining M
  cases, including their x0 decoder routing, are pending.
- Concrete: BabyBear, using the original JSON coefficient serialization.
- Custom arithmetic: all four modular branches in BabyBear, with native register
  and PC effects. Operand residues, decoded selectors and successful register/PC
  reads are interface premises; canonical output follows from imported constraints.
- PC equations: a satisfying assignment advances PC by four without 32-bit overflow,
  assuming bounded initial limbs. Final bounds follow from lookups. The serialized
  inverse coefficient is checked for BabyBear; the generic lemma requires that identity.
- Pending: full fetch/exception path, nondeterminism-read/delegation effects, other instruction
  families, completeness, decoder, lookup/memory arguments and compiled-gate correspondence.
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
