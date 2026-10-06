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
| Generated Sail Lean model | `generated/sail-rv32` | Compiler/pruning fidelity is not proved; metadata/docs are locally produced |
| Properties, mappings, contracts, Sail interface and public claims | Our `Airbender/Review` code | Human review of intended meaning and scope |
| JSON parser, coefficient conversion, emitter | Our `Airbender/Import` code | Faithful import/emission is not proved; coefficient cast equivalence is proved |
| Algebra, Sail support and circuit proofs | Our `Airbender/Proofs` code | Lean checks the proof terms; routine review starts with the public claims |

Clean directly supplies the expression and constraint semantics. Our source-format
JSON schema is parser data, not a second arithmetic model. There is no local
expression evaluator or equivalence bridge to Clean.

## Small review surface

All first-read definitions and claims are under `Airbender/Review/`:

1. [Shared properties and circuit relation](Airbender/Review/Properties.lean):
   arbitrary witnesses, declared observables, and explicit interface conditions.
   [Word encoding](Airbender/Review/Word.lean) and [field selection](Airbender/Review/Field.lean)
   define the representations used by these claims.
2. [Circuit model](Airbender/Review/AddSub/Model.lean): imported constraints,
   variable mapping and external decoder/range/register obligations.
3. [Sail interface](Airbender/Review/Sail.lean): original instruction inputs,
   fixed initial state, successful retirement and destination-write effects.
4. [Public theorems](Airbender/Review/AddSub/Theorems.lean): conditional soundness
   and determinism, including generic fields and BabyBear, against the same Sail specification.

Supporting proofs are in `Airbender/Proofs/`; their correctness is machine checked.
Import code remains a separate audit obligation in `Airbender/Import/`.
The assumptions do not assert the arithmetic result or carry bits. Current
coverage is ADD/ADDI/SUB destination words, with a nonzero destination. PC, full
architectural steps, `x0`, completeness and contract discharge remain pending.

## Unchecked connections

- **JSON → Clean objects:** inspect [Parse.lean](Airbender/Import/Parse.lean),
  [Schema.lean](Airbender/Import/Schema.lean),
  [Coefficients.lean](Airbender/Import/Coefficients.lean),
  [Embed.lean](Airbender/Import/Embed.lean) and
  [the artifact declaration](Airbender/Review/AddSub/Artifact.lean).
  The kernel checks the theorem over the emitted Clean object, not import fidelity.
- **Sail → generated Lean:** inspect [generation](scripts/generate_sail.py),
  [the slicing adapter](scripts/sail_slice.ml) and
  [provenance](generated/sail-rv32/provenance.json).
  Pins/hashes identify files; they do not certify the compiler or pruning.

Compiled-gate correspondence, cached equivalence, lookup/memory arguments and
protocol soundness are separate milestones in [the plan](FORMAL_VERIFICATION_PLAN.md).
Use [the axiom audit](Airbender/Checks/Axioms.lean) to check the actual proof dependencies.
