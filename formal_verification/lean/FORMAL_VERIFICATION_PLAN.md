# Circuit formal verification plan

ADDMOD/SUBMOD/MULMOD/FMAMOD have public decoding and initialized whole execution
with [pooled external reads/hints](Airbender/Review/Trace/Modular/README.md) and
[unified standard/TRIADD/XORROT execution](Airbender/Review/Trace/UnifiedReduced/ModularExecution.lean).
Both reuse the checked project arithmetic and existing native artifacts.

The user authorized an external contribution-mask boundary on 15 October 2026,
analogous to the canonical verifier-PC boundary. Its exact logical
state/memory/request binding, mask algebra and active-row projection are checked
and reuse the existing execution results. Rust/GKR/cryptographic enforcement
remains external. The hourly continuation is active. The user resumed implementation
after manual review on 13 October 2026. Current
coverage, checked counterexamples and machine-check results live in
[Verification status](VERIFICATION_STATUS.md).
[Directory review guide](Airbender/Review/README.md) separates per-circuit and whole-trace reading.
[Trust and review boundaries](TRUST_AND_REVIEW.md) records provenance and unchecked
connections. Keep these documents as snapshots, without completed-work history.

## Integrated review contract

Start with the composed execution claim in
[Trace/Soundness.lean](Airbender/Review/Trace/Soundness.lean) and its
[public inputs](Airbender/Review/Helpers/Context/PooledBoundary.lean). The proof path is:

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

`Review/Circuits/` owns row contracts, reference selection, artifact paths and named
mappings. `Review/Helpers/` owns initialized history, logical matching, public
boundaries and selected-row context; it is independent of whole-execution contracts.
Its property definitions remain the root entry point; `Core/`, `Decoder/`,
`Memory/` and `Context/` group the common review topics. Tables, delegation and
unified-machine context retain their separate groups.
`Review/Trace/` owns execution, terminal realization and composition. Three local
theorem modules retain the documented pooled proof-assembly dependency.
Explain declaration roles and parameters briefly,
with field comments for substantive assumptions. `Proofs/` owns calculation
interfaces, helper lemmas, proof assembly and mechanical guards; do not add proof
prose. `Import/` has a separate fidelity boundary. Consolidate identical contracts
without hiding instruction/profile distinctions or artifact observables.

Preserve existing field scope, minimum moduli, serialized inverse conditions,
reference definitions and regression/axiom coverage. Do not change circuits,
dependencies, pins or generated artifacts as part of readability cleanup.

## Pending integration work

The [finding register](FINDINGS.md#linear-and-open-pr-review--15-october-2026)
separates implementation bugs, temporary proof assumptions, intended external
interfaces and supported profiles. The user authorized temporary assumptions on
15 October 2026, with each underlying finding kept open until fixed or independently
shown enforced. AIH-334's EVM source check is now implemented and tested; formal
correspondence to its explicit distinct-selection interface remains external.
Apply the same distinction to decoder filler, request
participation, bigint controls, worker ROM and other reviewed defects. Open PRs
are proposals; inspect their code and validation before crediting a fix. Actual
bug fixes are authorized separately from the deferred formal-refinement work.

Conditional [native mixed-ROM composition](Airbender/Review/Trace/UnifiedReduced/NativeMixedROM.lean)
is checked: public boot inputs and the explicit F04 RAM-port contract give one
physical ordinary/caller/worker memory history and terminal public cells.
Full custom-call retirement still needs the reference connection described below;
the retained initialization/teardown artifact still lacks local proof input.
Independent shared-history composition is checked. Completed transport, cuts,
selected hash-reference composition and control preparation are recorded in
[Verification status](VERIFICATION_STATUS.md) and the review guides; do not restart
or repeat them here. Measure progress by closing these tasks or identifying their
specific external blockers, rather than by theorem, test or commit counts.

Freeze the currently checked instruction and preparation registries. Additional
operand-dependent operations, preparation variants and broader control-flow
profiles are optional extensions, not new requirements for this finalization.
Add one only when a concrete dependency of a closure task requires it, and record
that dependency before implementation. In particular, existing ADD/SUB instruction
soundness is complete within its published model; dataflow through another context
does not reopen that arithmetic proof.

Hash-span segmentation (closure 1) is checked within the existing unified public
prepared-protocol profile: public CSR occurrence coverage derives a disjoint,
exact partition of every issued hash worker/request across complete references
in one initialized history. Public mode, cuts, duration and code coverage remain
explicit inputs; acceptance alone does not force every execution into a complete
hash protocol. Zero-clock hash workers remain explicit residuals with their actual
prefix effects. See [the coverage result](Airbender/Review/Trace/UnifiedReduced/Segmentation.lean).
The remaining whole-execution/invalid-call boundaries are tasks 2–4 below, not
additional preparation variants.

2. **Whole mixed caller retirement — external ABI blocker.**
   [Shared cycle composition](Airbender/Review/Trace/UnifiedReduced/MixedCycles.lean)
   now places original ordinary/custom retirement, caller observations, every
   worker and the complete raw PC/clock path in one initialized history. The
   final retired-PC view agrees with all native terminal cells. Reads, operands,
   decoding and scheduling are derived; the existing public configuration,
   tracked-RAM domain and unchanged-Sail load profile stay explicit.
   `Caller.mixed_cycle_soundness` deliberately concludes an observational
   certificate, not successful full custom-CSR execution. Accepted bigint
   controls 0 and 65537 still violate the pinned ABI; unissued workers still have
   real prefix effects. Full custom retirement needs an actual binding or an
   explicit reference/scope decision. Another preparation variant cannot close it.
3. **Native worker ROM — conditional composition checked, enforcement open.**
   Public boot initialization, ordinary ROM interpretation, unchanged RAM-worker
   transfers and shared logical matching now compose. The F04 RAM-port contract
   remains explicit; arbitrary native acceptance still admits the ROM-shadow COPY
   discrepancy. Its implementation finding is not closed. Control/participation
   contracts likewise allow further conditional proof work on full custom calls;
   that integration must establish the actual reference transition, not just
   repeat current worker observations or selected arithmetic effects.
4. **Remaining global boundaries.** F01 terminal-PC normalization is resolved in
   the logical model under explicit canonical total-verifier boundary closure.
   Cryptographic enforcement and Rust/artifact correspondence remain deferred.
   Inactive padding is now erased under the user-authorized
   [external contribution-mask boundary](Airbender/Review/Helpers/Context/PaddingBoundary/README.md).
   The retained ADD/SUB row still has PC 0→4 and result 123; raw stuttering is
   neither assumed nor proved. Exact full-layout masked state/memory/request
   matching derives active acceptance and existing execution. Rust/artifact and
   cryptographic enforcement of that logical binding remain external. Full fetch faults, interrupts and
   exceptional execution belong to the separately scoped deferred path.

Preserve the demonstrated terminal-PC, zero-clock worker, bigint-control,
ROM-shadow and discarded-load cases. Issued bigint calls with public x12 = 0 or
65537 and the supported COPY ROM-shadow mismatch are checked model-level gaps,
not whole-system or cryptographic exploit claims. Temporary named control,
participation or RAM-port contracts may support conditional lemmas, but do not
establish general acceptance, validate the full CSR, or close these findings.
Do not assume desired results or alter the pinned references to hide a defect.
Implementation fixes must reject the bad cases while retaining the valid ones.
Padding is conditionally resolved
through its explicit new boundary; no compiler/verifier refinement is inferred. Deferred extraction,
cryptographic refinement and exceptional execution remain outside this task.

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
