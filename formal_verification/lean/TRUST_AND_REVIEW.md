# Trust and review boundaries

**Review definitions and assumptions for meaning; let Lean check the proofs.**
A proof does not establish that its definitions express the intended claim or
that an imported object faithfully represents the source artifact.

## Origin and status

| Component | Origin | What needs checking |
| --- | --- | --- |
| Lean kernel and standard axioms | Reused foundation | Accepted proof-checking foundation |
| Mathlib and Clean | Pinned upstream dependencies in `.lake/packages` | Definitions must fit their use; their proof terms are checked by Lean |
| Sail instruction semantics and runtime | Upstream source in `vendor/sail-riscv` and pinned `lean-sail` dependency | Selected configuration and our architectural projection |
| Project profile and custom-operation specification | Unmodified source in `vendor/airbender`, with revision/hash | Meaning of custom operations and applicability to this circuit revision |
| Generated Sail Lean model | `generated/sail-rv32` | Compiler/pruning fidelity is not proved; metadata/docs are locally produced |
| Properties, mappings, contracts, Sail interface and public claims | Our `Airbender/Review` code | Human review of intended meaning and scope |
| JSON parser, coefficient conversion, emitter | Our `Airbender/Import` code | Faithful import/emission is not proved; coefficient cast equivalence is proved |
| Algebra, Sail support and circuit proofs | Our `Airbender/Proofs` code | Lean checks the proof terms; routine review starts with the public claims |

Clean directly supplies the expression and constraint semantics. Our source-format
JSON schema is parser data, not a second arithmetic model. There is no local
expression evaluator or equivalence bridge to Clean. The 16-bit table in
[RangeChecks.lean](Airbender/Review/RangeChecks.lean) enumerates all limbs through
Clean's `StaticTable`; its membership characterization is kernel checked.
Its rows are a handwritten reconstruction of [Airbender's range setup generator](../../prover/src/gkr/virtual_polys/range_check.rs),
selected with 16 bits in [the prover](../../prover/src/gkr/prover/mod.rs).
That reconstruction and the importer's binding of range queries to it require review;
their correspondence with the Rust setup is not proved.
Generated-table extraction is a deferred task in [the plan](FORMAL_VERIFICATION_PLAN.md#deferred-milestones).

## Small review surface

All first-read definitions and claims are under `Airbender/Review/`:

1. [Shared properties and circuit relation](Airbender/Review/Properties.lean):
   arbitrary witnesses, declared observables, and explicit interface conditions.
   [Word encoding](Airbender/Review/Word.lean) and [field selection](Airbender/Review/Field.lean)
   define the representations used by these claims.
2. [Circuit model](Airbender/Review/AddSub/Model.lean): imported constraints,
   variable mapping and external decoder/range/register obligations.
3. [Sail interface](Airbender/Review/Sail.lean): original instruction inputs,
   fixed initial state, successful retirement and native destination/PC effects.
4. [Public theorems](Airbender/Review/AddSub/Theorems.lean): conditional soundness
   for generic prime fields and BabyBear, against the Sail specification.
   [Custom modular definitions](Airbender/Review/AddSub/Modular.lean) give the four
   project-specific word operations, native register/PC effects and interface assumptions.

Supporting proofs are in `Airbender/Proofs/`; their correctness is machine checked.
Import code remains a separate audit obligation in `Airbender/Import/`.
The assumptions do not assert the arithmetic result or carry bits. Current
coverage is ADD/ADDI/SUB/LUI/AUIPC destination and PC effects on the normal decoded
four-byte path, including x0/NOP preprocessing. The destination index is mapped to the JSON's
decoder variable. Discarded writes require successful original Sail reads, without
equating those values to the preprocessed zeros; operand bounds are unnecessary there.
Result and final-PC bounds follow from imported static range queries;
operand/immediate and initial-PC bounds remain external. AUIPC uses Sail's actual
PC read and U-type immediate construction under explicit mapping contracts.
The serialized PC inverse
is checked for BabyBear and explicit in the generic theorem. The normal-path
initialization and `tick_pc` connection are proved over generated/native semantics;
fetch/interrupt/exception handling, completeness and contract discharge remain pending.
The timestamp theorem similarly checks the serialized inverse and proves field
carry equations. Timestamp range queries are not emitted yet; no integer ordering
claim follows. Execute = 0 does not itself establish architectural stuttering:
the imported local relation admits advancing PC and nonzero destination limbs.
Custom modular soundness covers canonical BabyBear values and native register/PC
effects, including Montgomery multiplication, FMAMOD's old-destination read,
aliasing and x0 preprocessing. Standard and custom claims share the native step
relation and retirement proof. The small handwritten custom arithmetic definition
must be checked against the pinned project document; it is not an upstream Sail clause. Local delegation zero values
and read timestamps are checked; dispatch identity and memory effects remain
interface obligations. Nondeterminism-write soundness checks the project-specified architectural no-op
and PC retirement; source-hint/application-I/O behavior is outside the claim.
Nondeterminism-read agreement with a fixed response needs an external binding.
Conditional composition applies to standard and custom rows, requires an explicit
match of native states and does not discharge the execution/memory argument.

Jump/branch/SLT uses the same import and Clean semantics. Its
[public claims](Airbender/Review/JumpBranchSlt/Theorems.lean) cover local arithmetic
and native Sail SLTU register/PC effects. All four fixed comparison/cleanup queries
are now emitted; timestamp queries are still excluded. The table rows in
[ComparisonLookups.lean](Airbender/Review/ComparisonLookups.lean) reconstruct the
Rust generators symbolically and share the unproved table-provenance gap.
A checked counterexample shows that the local relation does not enforce a 16-bit
final-PC high limb; SLTU soundness explicitly assumes that state/ROM bound and
four-byte input alignment. Its initial high-PC bound follows from a lookup, and
PC wraparound is supported. Decoder identity and agreement with successful native
Sail operand/PC reads remain interface obligations; x0, signed/immediate comparison,
branch and jump coverage is pending.

## Unchecked connections

- **JSON → Clean objects:** inspect [Parse.lean](Airbender/Import/Parse.lean),
  [Schema.lean](Airbender/Import/Schema.lean),
  [Coefficients.lean](Airbender/Import/Coefficients.lean),
  [Embed.lean](Airbender/Import/Embed.lean) and
  [the artifact declaration](Airbender/Review/AddSub/Artifact.lean).
  Range-query addresses are resolved through `placement_data`; missing or ambiguous
  logical variables are rejected. The kernel checks the emitted Clean object, not
  import fidelity or the correspondence with the compiled lookup argument.
- **Sail → generated Lean:** inspect [generation](scripts/generate_sail.py),
  [the slicing adapter](scripts/sail_slice.ml) and
  [provenance](generated/sail-rv32/provenance.json).
  The generator extracts the unique normal `F_Base` nextPC assignment verbatim from
  pinned `run_hart_active` into `extracted_base_pc.sail`, then compiles it with Sail.
  Review that extraction and the chosen decoded four-byte path: the complete fetch
  driver, interrupt handling and exceptional branches are not imported into this claim.
  Pins/hashes identify files; they do not certify extraction, compilation or pruning.

Compiled-gate correspondence, cached equivalence, lookup/memory arguments and
protocol soundness are separate milestones in [the plan](FORMAL_VERIFICATION_PLAN.md).
Use [the axiom audit](Airbender/Checks/Axioms.lean) to check the actual proof dependencies.
