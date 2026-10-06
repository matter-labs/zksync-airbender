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
- Parameterize shared proof lemmas over the field. Our circuit interface uses
  prime fields `ZMod p` for canonical word decoding; the current destination-word
  theorem requires `p > 196608`. New claims must account for field-dependent
  serialized constants. Keep artifact compatibility premises separate from reusable
  algebra; actual large-field artifact import remains pending.
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

**Table provenance gap:** the queries are imported, but the fixed 16-bit table
is reconstructed by hand from Airbender's Rust setup generator. Its rows are not
extracted, and the Rust-to-Lean table binding is unproved.

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
   assumption for the modeled table. Generated-table extraction remains pending.
   Input bounds still require decoder/memory contracts. The lookup
   argument itself and its compiled encoding are separate proof obligations.
6. **Finish the declared standard-instruction step.** Connect PC sequencing,
   architectural register projection and preprocessing of writes to `x0`.
7. **Review the complete claim.** Check interface assumptions, exact instruction
   and field coverage, artifact identity, and axiom dependencies.

## Next work: expand circuit coverage

**Draft for review; implementation is paused.** The next pass completes the ADD/SUB
family's instruction behavior, then applies the same work to other circuit families.
Lookup-table extraction, richer/compiled equivalence,
cached equivalence and cryptographic lookup/memory soundness are deferred.
Keep the existing table-provenance gap explicit while extending the proofs.

### A. PC update and a shared transition interface

1. **Inventory the actual PC relation.** Identify the imported PC assertions,
   initial/final variable roles, range queries and execution-flag behavior. Establish
   what is enforced even on inactive rows. Add role guards for variables used by proofs.
2. **Check field compatibility before generalizing.** The BabyBear JSON's PC
   assertions use the serialized inverse of 65536, whose signed representative is
   `-30720`. It is an inverse in BabyBear, not an inverse under arbitrary prime moduli.
   Prove the required identity for this artifact. Keep arithmetic lemmas generic
   with explicit inverse premises; preserve the existing generic destination theorem.
   Do not reinterpret or replace a serialized constant to make a theorem hold.
3. **Prove the PC equations from Clean satisfaction.** Recover the low-limb carry
   expression and its Boolean property, then the high-limb equation. Derive final-PC
   limb bounds from the existing imported lookups. Reuse field-to-natural and word
   lemmas; do not assume the desired PC increment.
4. **Resolve PC boundaries.** Prove the actual successor behavior, including a
   carry across the 16-bit boundary. Analyze the top of the 32-bit address space:
   the artifact has no explicit second wrap carry. Record whether satisfying rows
   exclude overflow rather than assuming wrapping or adding an artificial range
   precondition. Check the project's supported four-byte instruction profile.
5. **Bring in the actual Sail PC semantics.** The current generated slice retains
   only RTYPE/ITYPE execution roots and omits PC stepping. Find the smallest relevant
   upstream PC-update/retirement code, extend the existing generation slice as needed,
   and preserve its pins/provenance. Do not write a replacement PC specification.
6. **Extend the observable transition once.** Add initial/final PC to the shared
   instruction interface and map them to the imported variables and Sail state.
   Keep one Sail reference surface and the existing shared soundness definition.
   Separate PC input interpretation from enforced PC equations and external contracts.
7. **Compose destination and PC soundness.** Strengthen ADD/ADDI/SUB claims to cover
   destination effects and the proved PC transition against the reused Sail semantics.
   State exactly which fetch, decoding, memory and architectural-step obligations remain.

**Acceptance:** kernel-checked PC and combined soundness claims; explicit artifact
field coverage and overflow behavior; no new handwritten standard-instruction spec.

### B. Finish the standard branches in this family

8. **Add LUI.** Trace its decoder preprocessing into the existing addition selector.
   Extend the generated Sail slice to the upstream UTYPE clause. Prove the shifted
   immediate and zero-source mapping, reusing the existing addition calculation.
9. **Add AUIPC.** Select the imported PC-plus-immediate equations and connect them
   to Sail's original PC read and UTYPE execution. Reuse the PC input mapping,
   carry/word arithmetic and PC successor proof. Include word-boundary behavior.
10. **Cover NOP and writes to x0.** Airbender preprocesses discarded writes into
    addition with zero operands. Connect original instruction inputs to that
    preprocessing and Sail's zero-register behavior. State architectural effects
    rather than requiring a unique discarded ALU result. Keep these cases within
    the same reference interface and shared soundness property.
11. **Prove the register effects precisely.** Account for unchanged registers and
    operand/destination aliasing, including equal source registers and writes back
    to a source register. Reuse Sail's register semantics and existing write lemmas.
    Avoid another register-state wrapper or a parallel local machine model.

**Acceptance:** standard branch coverage for ADD, ADDI, SUB, LUI, AUIPC and the
relevant NOP/x0 preprocessing cases, with destination effects and PC behavior.

### C. Close local row obligations

12. **Review selector assumptions.** Derive Boolean and exclusion properties that
    the imported constraints actually enforce. Retain instruction selection and
    decoder guarantees as explicit contracts wherever the equations do not imply them.
    Include all nine decoder flags in the coverage inventory.
13. **Handle inactive rows.** Define the claim's scope when the execute flag is zero.
    Distinguish locally constrained dummy values from architectural effects; do not
    assume an inactive row stutters merely because the flag is zero. Prove the local
    masking facts needed by the exposed relation and list remaining argument contracts.
14. **Check cycle/timestamp behavior.** Inspect the machine-state layout and imported
    equations for locally enforced updates. Prove available facts with explicit bounds;
    if ordering or advancement comes only from another argument, record that dependency.
    This does not include proving the memory argument.
15. **Reduce interface assumptions.** Audit every premise used by the expanded
    proofs. Derive bounds from imported queries or native word decoding wherever
    justified; retain operand/immediate range guarantees not supplied by this circuit.
    Remove unused assumptions without weakening the stated architectural claim.

**Acceptance:** the model shows exactly what the local constraints prove and what
its decoder/memory/environment interfaces still promise.

### D. Cover the custom branches

16. **Pin and review the custom-operation specification.** Locate the authoritative
    project semantics for modular operations, delegation and nondeterministic I/O.
    Fix the target modulus, input/reduction policy and externally supplied values.
    Keep custom specifications small and separate from standard Sail behavior.
    If a specification is missing or ambiguous, record the blocker and continue
    independent work; do not substitute the witness generator as the specification.
17. **Prove canonical modular outputs.** Use the imported comparison equations and
    intermediate range queries to establish the required output range. Develop
    reusable reduction and carry lemmas, with artifact-specific field premises.
18. **Prove modular addition and subtraction.** Instantiate those lemmas for the
    two selectors and prove the reviewed custom relations. Cover reduction boundaries
    and state the valid input domain explicitly.
19. **Prove modular multiplication.** Derive its equation from the imported assertion
    and combine it with the canonical-output proof. Reuse the target-modulus machinery
    rather than duplicating a second arithmetic model.
20. **Prove modular fused multiply-add.** Expose the old destination/register input
    needed by this branch, relate it to the register interface, and reuse multiplication,
    reduction and canonical-output lemmas. Include destination/source aliasing cases.
21. **Cover nondeterministic read and write.** Expose oracle inputs and observable
    I/O events in the reviewed custom contract. Prove the local register/PC/effect
    relation; an external input must not be defined from the output witness to make
    soundness tautological. Do not reintroduce determinism as a circuit property.
22. **Cover delegation dispatch.** Prove the local dispatch identity and relevant
    register/PC effects against a reviewed request/response contract. Keep correctness
    of the delegated computation and its argument as explicit downstream obligations.

**Acceptance:** each remaining branch has a precise soundness claim or a documented
specification/interface blocker. Custom claims are not labeled as upstream Sail proofs.

### E. Consolidate and check the expanded model

23. **Compose family coverage.** Present one shared soundness statement whose cases
    cover the declared instructions and effects. Centralize selectors, variable roles,
    field premises and reused proof lemmas; keep routine calculation details in `Proofs/`.
24. **Check conditional row composition.** Reuse relation/list or suitable Clean
    composition lemmas to connect rows when their observable states are given to match.
    State that chaining premise explicitly. Proving that the execution argument
    establishes it remains deferred with memory/argument soundness.
25. **Review and machine-check.** Run scoped Lean checks during implementation and
    the full build/importer checks/axiom audit at integration points. Exercise concrete
    carry, borrow, PC-boundary, aliasing, x0, inactive-row and custom reduction cases
    where they expose a remaining risk. Confirm no `sorry`, new project axioms or
    unsupported full-step/large-field claims. Stop redundant testing once verified.
26. **Simplify the review surface.** Remove obsolete contracts, helper wrappers and
    duplicated statements. Keep the review path to shared properties, imported artifact,
    input/output mapping, external assumptions and public claims. Update the scope and
    trust notes concisely; document counterexamples and unresolved gaps explicitly.

### F. Expand to other circuit families

27. **Inventory and order the remaining families.** Match each no-cache layout to
    its standard instructions or custom operations. List branches, observables and
    external interfaces, and prioritize families that reuse the established machinery.
28. **Transfer the foundations to a second family.** Import its richer constraints
    directly into Clean and reuse the shared soundness property, Sail interface and
    arithmetic lemmas. Generalize helpers only where needed; do not copy the ADD/SUB
    model or introduce a second constraint interpreter.
29. **Repeat the coverage work for each family.** Prove its branches, PC behavior,
    register/effect semantics and local row obligations against Sail or the reviewed
    custom specification, as in phases A–D. Reuse established proofs wherever the
    equations or interfaces agree, including x0, aliasing and inactive-row handling.
30. **Audit assumptions and field coverage per artifact.** Derive guarantees supplied
    by imported constraints and lookups; expose the remaining decoder, memory and
    environment contracts. Check serialized coefficients before applying generic field
    lemmas. Keep deferred table provenance and argument proofs explicit.
31. **Integrate and review each family.** Apply phase E's machine checks and axiom
    audit, then expose a compact soundness claim through the same review structure.
    Maintain one coverage summary showing proved branches, effects, supported fields
    and remaining gaps; keep shared definitions and proofs in common modules.

**Acceptance:** the same verification contract and review path apply across circuit
families, with kernel-checked claims and explicit coverage rather than duplicated foundations.

### Execution rules after plan approval

- Work through the dependencies above; finish independent tasks when another task
  is blocked by unavailable specification or generation inputs.
- Commit coherent verified milestones using messages inferred from the changes.
  Summarize the actual proof coverage, remaining assumptions and checks for each.
- Keep field-specific artifact facts distinct from reusable generic algebra.
- Preserve the strict JSON import, sole Clean constraint model, reused Sail standard
  semantics and the `Review/` versus `Proofs/` versus `Import/` boundary.
- Do not start table extraction, compiled correspondence, cached equivalence or
  cryptographic argument proofs during this coverage pass.

## Deferred milestones

These remain tracked but are outside the next circuit-coverage pass.

1. **Extract fixed lookup tables.** Export rows and table identity from Airbender's
   actual Rust setup generator, then import that artifact into Clean's `StaticTable`
   and prove membership properties over the imported rows. Record generation
   provenance, validate query-to-table binding, and account for zero padding.
   Export/import fidelity and lookup-argument soundness remain separate obligations.
2. Prove correspondence with compiled no-cache gates. Soundness needs compiled
   constraints to imply the richer constraints; equivalence also needs witness extension.
3. Prove cached-layout equivalence, including verifier helper expressions.
4. Discharge the remaining decoder/preprocessing and lookup-setup contracts.
5. Prove lookup-argument and memory-argument soundness; compose row results into
   whole-execution correctness.
6. Establish completeness for each declared circuit relation.
7. Treat verifier implementation refinement and cryptographic protocol soundness
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
