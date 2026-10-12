# Circuit formal verification plan

Circuit-coverage expansion resumes through the hourly continuation. Current
coverage, checked counterexamples and machine-check results live in
[Verification status](VERIFICATION_STATUS.md).
[Trust and review boundaries](TRUST_AND_REVIEW.md) records provenance and unchecked
connections. Keep these documents as snapshots, without completed-work history.

## Integrated review contract

Start with the composed execution claim in
[Trace/Soundness.lean](Airbender/Review/Trace/Soundness.lean) and its
[public inputs](Airbender/Review/Trace/PooledExecution.lean). The proof path is:

```text
public initialization → preserved write bounds → latest-write reads
                      → circuit operand bounds → original Sail execution
```

The shared `Realizes` property states execution and terminal PC/cell realization
once. Keep public conditions visible: field compatibility, platform/configuration,
initial state/program/domain, modeled tables, logical matching and unresolved
terminal conditions. Derive local bounds, reads, decoder selectors and row
interfaces inside `Proofs/`; never assume desired reads, results or decoder answers.

Use Clean's original constraint semantics and original Sail standard-instruction
clauses. Project custom operations use the pinned project specification. Keep the
unchanged-Sail discarded-load restriction distinct from the named Airbender
PC-only-NOP profile. External input streams remain independent of the witness;
explicit port connections do not establish circuit authentication of the stream.

`Review/` owns properties, reference selection, artifact paths, named mappings,
public inputs and primary claims. Explain declaration roles and parameters briefly,
with field comments for substantive assumptions. `Proofs/` owns calculation
interfaces, helper lemmas, proof assembly and mechanical guards; do not add proof
prose. `Import/` has a separate fidelity boundary. Consolidate identical contracts
without hiding instruction/profile distinctions or artifact observables.

Preserve existing field scope, minimum moduli, serialized inverse conditions,
reference definitions and regression/axiom coverage. Do not change circuits,
dependencies, pins or generated artifacts as part of readability cleanup.

## Pending integration work

Follow this dependency order for coverage continuation. Simplification is complete;
preserve the integrated review contract as coverage expands.

Native-clock cuts retain raw boundary timestamps and now realize both sides in
Sail from one public initialization. Boundary reads and suffix initialization are
derived from the actual prefix state; terminal reads and recomposed transport are
checked. Two cuts also derive canonical RV32 values and bounded raw timestamps
for native worker windows, retaining complete rows, their original constraints
and exact boundary matching. The unified caller-only span interface reuses these
results. Native boundary images now retain timestamps and derive canonical seed
values from actual Sail reads; all three complete hash references consume this
interface without resetting clocks.

1. **Hash references on subspans.** Reuse complete caller-only G, extended BLAKE and
   Keccak references for segmented spans. Derive worker boundaries, ranges,
   intermediate states and schedules from the same initialized history; retain
   public mode/span-size ABI, modeled tables and logical matching. Native-boundary
   bindings now derive G controls and extended-BLAKE round masks as well as Keccak
   controls; the public initialization entry points remain. Compose these complete
   references with selected caller/worker windows and their public ABI.
2. **Whole mixed caller retirement.** Compose caller/worker spans with existing
   actual current-state fetch and ordinary/custom clause retirement. Recover exact
   instruction/call windows and terminal PC/cells from shared history; do not
   supply intermediate states or scheduling results as premises.
3. **Native worker ROM and invalid-call binding.** Connect zero native ROM shadows
   to independent public bytes for worker operations. Resolve caller/control scope
   against available circuit inputs, retaining checked ABI gaps until justified.
4. **Remaining global boundaries.** Jump terminal-PC normalization needs richer
   teardown proof input. Inactive padding needs global state/write obligations.
   Full fetch faults, interrupts and exceptional execution require a separate
   scope and reference path.

Checked ABI gaps must remain exposed: surplus zero-clock workers without a
caller; issued bigint calls with public x12 = 0 or 65537; and a supported COPY
worker whose native ROM shadows differ from public bytes. These are logical
richer-artifact counterexamples, not whole-system or cryptographic bug claims.
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
See [reproduction commands](README.md#reproduce).

A completed change keeps arbitrary-witness claims over actual imported constraints,
explicit public assumptions and the pinned references. Its review entry identifies
observables and scope; compilation correspondence and protocol soundness are not
assumed. Update the status snapshot and commit coherent verified milestones with
Conventional Commits. Keep agent plans/audits in the gitignored `.agents/` directories.
