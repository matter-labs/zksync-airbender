# Circuit formal verification plan

## Objective and first deliverable

Prove ADD/ADDI/SUB soundness against reused Sail RV32 semantics for arbitrary
assignments satisfying the richer constraints imported from the generated no-cache
JSON. Keep decoder, range and register/memory interfaces explicit. The witness
generator is not an assumption of soundness.

The first deliverable covers the full declared instruction step. The current
prototype proves the destination-word operation; PC and `x0` preprocessing still
need to be connected. Compiled gates and protocol soundness are later claims.

## Design decisions

- Import the generated JSON directly into native **Clean** expressions and flat
  assertions and lookups. Clean is the sole expression/constraint model for circuit proofs.
- Reuse the actual **Sail** standard-instruction semantics. Keep arithmetic
  calculations inside proofs; custom operations need an explicit project spec.
- Keep shared definitions of soundness and completeness. Conditional
  statements apply those definitions directly. Separate
  constraint satisfaction, observable mapping and external assumptions.
- Reuse Mathlib/Lean/Clean lemmas before introducing equivalent infrastructure.
  Circuit families should establish artifact-specific premises and reuse shared proofs.
- For lookups, reuse Clean's `StaticTable` and native lookup semantics. For later
  memory/state proofs, start with `Clean.Utils.SourceSinkPath` (balanced transitions
  imply a path), `Clean.Utils.OfflineMemory` (offline/online memory consistency),
  and `Clean.Table.Inductive` for ordered row composition where its interface fits.
  Prove the Airbender-specific encoding, timestamp, initialization and argument
  premises; retain Sail as the instruction reference.
- Parameterize proof lemmas over the field. Our circuit interface uses
  prime fields `ZMod p` for canonical word decoding; ADD/SUB lifting requires
  `p > 196608`. This covers both field sizes; shared algebra lemmas retain weaker
  field/ring requirements.
- Start from `_layout_no_caches_gkr`. Cached helper equivalence follows later.
  SSA witness-generation artifacts and schedules are outside this proof target.
- Keep original upstream source, generated reference files and our code separate.
  Put definitions, assumptions and public claims in `Airbender/Review/`, supporting
  proofs in `Airbender/Proofs/`, and the unchecked JSON pipeline in `Airbender/Import/`.
  Minimize the code and documentation a reviewer must read. Keep one public
  reference interface, with encoding and execution lemmas in the proof area.

## Current proof path and assumptions

```text
no-cache JSON → Clean assertions + static lookups → arithmetic lemmas → Sail execution
```

All 30 retained equations and six 16-bit range queries are emitted as transparent
Clean operations, parameterized by the prime modulus. Queries are mapped from
physical addresses to logical variables through `placement_data`. Clean's native
satisfaction theorem supplies both assertion equations and lookup membership.
No duplicate local interpreter or translation bridge remains.

The ADD/ADDI/SUB theorem assumes:

- active row and decoded selector/preprocessing values;
- bounded 16-bit operand and immediate limbs (decoder/memory obligations);
- input-word encoding and canonical output decoding through named variables;
- actual Sail register reads matching those words, and
  Sail sign extension of the ADDI immediate.

The result equation, carry bits and result-limb bounds are derived from the imported
relation. The six range queries cover result, final-PC and modular-comparison limbs;
they do not bound input operands. Soundness targets Sail directly. The initial
Sail state is fixed input. [The README](README.md) links the compact review entry points;
[the trust map](TRUST_AND_REVIEW.md) identifies unchecked connections.

## Implementation sequence

1. **Pin reused foundations.** Done for Lean/Mathlib, Clean and Sail. Clean's selected
   modules build unchanged under the existing toolchain. Its broader DSL/gadget/
   composition interfaces remain candidates for later obligations.
   `SourceSinkPath` also builds unchanged. Importing `OfflineMemory` currently fails
   on two instance declarations in `Clean.Circuit.Explicit` under Lean 4.31;
   resolve that compatibility issue before integrating its memory theorems.
2. **Define shared properties and interfaces.** Done: constraints, representation
   and assumptions are separate; conditional claims reuse the shared definitions
   directly. The model lists its contracts together; one short theorem file collects
   the public claims. Completeness is defined but not yet proved.
3. **Import the real artifact.** Done for BabyBear: strict schema decoding,
   Montgomery coefficient conversion, native Clean emission, embedded source bytes
   and variable-role guards. Import/emission fidelity remains a review obligation.
4. **Prove arithmetic and Sail destination-word behavior.** Done for ADD/ADDI/SUB,
   including the concrete BabyBear field instance.
5. **Import range checks and derive result bounds.** Done: all six 16-bit queries
   use native `StaticTable` membership, replacing the result-bound
   assumption. Input bounds still require decoder/memory contracts. The lookup
   argument itself and its compiled encoding are separate proof obligations.
6. **Finish the declared standard-instruction step.** Connect PC sequencing,
   architectural register projection and preprocessing of writes to `x0`.
7. **Review the complete claim.** Check interface assumptions, exact instruction
   and field coverage, artifact identity, and axiom dependencies.

## Subsequent milestones

1. Add LUI/AUIPC using the upstream Sail execution clauses and existing arithmetic
   lemmas; expose AUIPC's PC input explicitly.
2. Cover the family's modular arithmetic, delegation and nondeterministic I/O
   branches against reviewed custom-operation specifications and effect contracts.
3. Apply the same shared properties and foundations to the remaining circuit families.
4. Prove correspondence with compiled no-cache gates. Soundness needs compiled
   constraints to imply the richer constraints; equivalence also needs witness extension.
5. Prove cached-layout equivalence, including verifier helper expressions.
6. Discharge decoder/preprocessing and lookup-setup contracts.
7. Prove lookup-argument and memory-argument soundness; compose row results into
   whole-execution correctness.
8. Establish completeness for each declared circuit relation.
9. Treat verifier implementation refinement and cryptographic protocol soundness
   as separate downstream proofs, connected through explicit interfaces.

## Completion criteria

- Actual imported constraints, arbitrary witnesses and the pinned Sail reference.
- Shared property definitions and reusable lemmas; no copied per-family foundations.
- Explicit assumptions without the desired arithmetic conclusion.
- A compact review entry stating observables, instruction/field coverage and artifact identity.
- Kernel-checked proofs with no `sorry`, admitted project axioms or assumed
  compilation correspondence.
- Honest separation of conditional circuit claims, architectural coverage and
  protocol claims, with import/generation trust boundaries recorded.

## Pins and remaining inputs

- Base revision: `av_gkr_compiler`, `28ffe3ff0353edd9051485c2974b28b52b495dc4`.
- Artifact: `cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json`.
- Artifact SHA-256 (committed bytes): `084a58f08dd122160b548689383f74d4a790c782046f8a5bf43f9f287c22a620`.
- Lean/Mathlib: `v4.31.0`. Clean: `1e563b9c27991b3795eb440c1ee0757edb4ce8b1`.
- Sail model/compiler/runtime pins: [provenance](generated/sail-rv32/provenance.json).
- Authoritative project scope/custom-operation document: [provided specification URL](https://github.com/matter-labs/zksync-airbender/blob/mb_gkr_compiler/spec/top-down/00%20master.md#supported-instruction-set-and-custom-operations).
  It was unavailable during implementation; obtain and pin it before claiming
  conformance to project preprocessing/custom-operation scope.
- The actual large-field JSON import/profile remains to be implemented. Generic
  prime-field proofs do not establish that a Proth120 artifact was imported.

Source references: `cs/src/structured_expr.rs`, `cs/src/gkr_circuits/add_sub_family/`,
`cs/src/gkr_compiler/mod.rs`, `field/src/baby_bear/base.rs`, `field/src/proth120.rs`.
