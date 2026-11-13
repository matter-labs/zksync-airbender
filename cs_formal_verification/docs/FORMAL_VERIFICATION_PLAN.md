# Circuit formal verification plan

Finalization of the pending integration work is active, with an hourly follow-up.
The user resumed implementation after manual review on 13 October 2026. Current
coverage, checked counterexamples and machine-check results live in
[Verification status](VERIFICATION_STATUS.md).
[Directory review guide](../lean/human/Human/README.md) separates per-circuit and whole-trace reading.
[Trust and review boundaries](TRUST_AND_REVIEW.md) records provenance and unchecked
connections. Keep these documents as snapshots, without completed-work history.

## Integrated review contract

Start with the composed execution claim in
[Trace/RVSoundness.lean](../lean/human/Human/Trace/RVSoundness.lean) (proof in
[proven](../lean/proven/Proven/Final/Trace/RVSoundness.lean)) and its public inputs. The proof path is:

```text
public initialization → preserved write bounds → latest-write reads
                      → circuit operand bounds → RV32 spec execution (RV.step, RV.run)
```

The shared `RVRealizes` property states execution and terminal PC/cell realization
once. Keep public conditions visible: field compatibility, initial state/program/domain,
modeled tables, logical matching and unresolved terminal conditions. Derive local
bounds, reads, decoder selectors and row interfaces inside `Proven/`; never assume
desired reads, results or decoder answers.

Use Clean's original constraint semantics and our RV32 spec
([RV32.lean](../lean/human/Human/ISA/RV32.lean)): standard instructions, Airbender's custom
operations and delegations are all defined there, and every claim is stated against it. Sail
appears only in the [equivalence leaf](../lean/human/Human/ISA/Sail/Theorems.lean). External input streams remain
independent of the witness; explicit port connections do not establish circuit authentication of the stream.

`Human/Circuits/` owns row contracts, reference selection, artifact paths and named
mappings. `Human/Helpers/` owns initialized history, logical matching, public
boundaries and selected-row context; it is independent of whole-execution contracts.
Its property definitions remain the root entry point; `Core/`, `Decoder/`,
`Memory/` and `Context/` group the common review topics. Tables, delegation and
unified-machine context retain their separate groups.
`Human/Trace/` owns execution, terminal realization and composition.
Explain declaration roles and parameters briefly,
with field comments for substantive assumptions. `Proven/` owns calculation
interfaces, helper lemmas, proof assembly and mechanical guards; do not add proof
prose. `Import/` has a separate fidelity boundary. Consolidate identical contracts
without hiding instruction distinctions or artifact observables.

Preserve existing field scope, minimum moduli, serialized inverse conditions,
reference definitions and regression/axiom coverage. Do not change circuits,
dependencies, pins or generated artifacts as part of readability cleanup.

## Pending integration work

Coverage checked so far (per-circuit, whole-trace, worker, caller and window claims) is
listed in [Verification status](VERIFICATION_STATUS.md); this section keeps only what is open. Follow this
dependency order for coverage continuation and preserve the integrated review contract as coverage expands.

1. **Hash references on subspans.** Complete caller-only G, extended-BLAKE and Keccak
   references already reach native windows, joint cuts and prepared spans. Continue with
   broader preparation/protocol-shape binding (controller-region coverage, control flow and wraparound,
   nonliteral preparation); derive worker boundaries, ranges, intermediate states and schedules from the
   same initialized history, retaining public mode/span-size ABI, modeled tables and logical matching.
   Completion controls of extended BLAKE and Keccak do not restart their protocols.
2. **Whole mixed caller retirement.** Use the shared caller-cycle boundaries and
   fetch to compose caller/worker spans with ordinary/custom clause retirement.
   Bind full caller ABI only where the available inputs justify it. Recover exact
   instruction/call windows and terminal PC/cells from shared history; do not
   supply intermediate states or scheduling results as premises.
3. **Native unified ROM-shadow transport and invalid-call binding.** Carry the zero native ROM shadows
   through the unified caller claims. Resolve caller/control scope against available circuit inputs,
   retaining checked ABI gaps until justified.
4. **Remaining global boundaries.** Jump terminal-PC normalization needs richer
   teardown proof input; teardown values are bounded only under an open item (the cross-circuit
   memory-argument protocol is not formalised). Inactive padding needs global state/write
   obligations. Full fetch faults, interrupts and exceptional execution require a separate scope.

Checked ABI gaps must remain exposed: surplus zero-clock workers without a
caller (the circuit rejects active ones, the claims do not use this); and a bigint worker row with x12 = 0 and no control bit set, or with x12 = 65537, which the pinned Rust reference rejects
([fixture](../lean/test/Tests/UnifiedDelegation.lean)). These are logical
richer-artifact gaps, not whole-system or cryptographic bug claims.
Do not fix circuits or introduce assumed valid controls/nonzero invocation to
conceal them. Continue independent integration work when circuit inputs are missing.

## Deferred milestones

These require separately scoped work:

1. Extract fixed lookup rows and identities from the actual Rust setup generator,
   import them into Clean, and account for query binding, provenance and padding.
   Export/import fidelity and lookup-argument soundness remain separate.
2. Prove compiled no-cache constraints imply the richer constraints. Equivalence
   additionally needs witness extension; cached layouts and verifier helper
   expressions require their own correspondence.
3. Discharge Rust decoder/preprocessing and setup-generator correspondence.
4. Prove cryptographic lookup and memory argument soundness and connect them to
   execution claims. Keep verifier implementation refinement and protocol
   soundness as explicit downstream interfaces.
5. Prove completeness for each declared circuit relation.
6. Import and verify the actual large-field artifact and its own coefficients;
   generic prime-field proofs alone do not establish a Proth120 import.

## Verification and completion

For each coherent milestone, build the library, both executables and every
concrete `Tests/**/*.lean` module. Run the importer regressions and full axiom audit;
require no project warnings, `sorry` or project axioms. Preserve all existing
accepted/rejected fixtures and audit declarations, including axiom-free reports.
See [reproduction commands](../README.md#reproduce).

A completed change keeps arbitrary-witness claims over actual imported constraints,
explicit public assumptions and the pinned references. Its review entry identifies
observables and scope; compilation correspondence and protocol soundness are not
assumed. Update the status snapshot and commit coherent verified milestones with
Conventional Commits. Keep agent plans/audits in the gitignored `.agents/` directories.
