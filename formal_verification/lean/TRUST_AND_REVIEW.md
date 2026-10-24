# Trust and review boundaries

The target is the imported richer no-cache relation built from this checkout,
with upstream `av_gkr_compiler` baseline revision
`4518846625730fabc4cd83744d4bd983a5e42b97`. The hash workers include the native
successful-call constraints recorded in the current source/artifact manifest.
[Verification status](VERIFICATION_STATUS.md) records completed validation and
material limits. The [historical integration record](TRUST_AND_REVIEW_HISTORY.md)
retains earlier experiments and narrower intermediate interfaces.

## Review entry points

Start with the [Review guide](Airbender/Review/README.md), then the selected
[circuit contract](Airbender/Review/Circuits/README.md) or
[whole-trace claim](Airbender/Review/Trace/README.md). Review contains the important
composed statements, original reference selection, observable mappings and public
assumptions. Supporting arithmetic and assembly proofs belong in Proofs; a
separate public wrapper for every internal subcircuit calculation is unnecessary.
Existing compatibility names and native BabyBear entrypoints remain useful.

[Pooled soundness](Airbender/Review/Trace/Soundness.lean) derives successful
ordinary execution and native terminal PC/cells from initialized matching.
[Unified full execution](Airbender/Review/Trace/UnifiedReduced/FullExecution.lean)
also composes complete bigint, BLAKE2 G, extended-round and Keccak references
with the supported straight-line ordinary registry.
[Native actual-path execution](Airbender/Review/Trace/UnifiedReduced/NativePathExecution.lean)
composes branches, JAL/JALR and repeated-PC loops with complete delegations
without an occurrence plan;
[complete spans](Airbender/Review/Trace/UnifiedReduced/PathSpanExecution.lean)
derive the full native worker partition/count and algorithms in one history
under their per-trace occurrence plan and complete protocol coverage.
The earlier entrypoints, accepted two-COPY loop and complete native G-loop
application passed the full ordinary source/runtime suite at `5b17af422`.
The native enforcement refresh has focused kernel checks recorded in the
verification status.
Separate declaration-origin auditing, transitive assurance controls and independent
kernel replay are also required.

## Checked scope boundaries

Claims retain explicit public program/state/configuration, tracked domain,
modeled lookup tables and exact logical matching. Reads, operand bounds,
decoder selections and worker participation are derived. A local request observation
is weaker than fulfilled worker effects or a complete reference span.

The native actual-path entrypoint derives supported hash controller positions,
round-mask validity and G base separation from the refreshed native constraints.
It covers controllers loaded or computed through arbitrary supported ordinary
instructions and requires no instruction/caller occurrence plan. Public program
bytes, initialized tracked memory, configuration/retirement and the separate
bigint command contract remain explicit. The older full-CSR profile retains
aligned straight-line code, and the older actual-path preparation profile retains
a per-trace occurrence plan. These execution claims require tracked data RAM at
or above the ROM limit. Complete grouped algorithms additionally need protocol
coverage and readonly gaps or computed stores disjoint from each protected block.
Standard boot-ROM-data copying remains outside these claims.

| Boundary | Current meaning |
| --- | --- |
| Canonical terminal PC | The [external verifier boundary](Airbender/Review/Helpers/Context/VerifierBoundary/README.md) supplies typed endpoint closure. Accepted state matching, the applicable boot/initial tuple, BabyBear field and representable timestamps are needed for its connection to native raw PC columns. It adds no local circuit range constraint. |
| Inactive padding | The [external contribution-mask boundary](Airbender/Review/Helpers/Context/PaddingBoundary/README.md) derives active acceptance/execution from exact masked tuple matching. Raw inactive PC/write values need not stutter. |
| Bigint commands | F02 remains an explicit valid-command contract. Accepted controls 0 and 65537 still fail the pinned full reference; observations alone do not validate their ABI. |
| Worker ROM | F04 remains an explicit RAM-port contract. The accepted COPY ROM-shadow discrepancy is preserved. |
| Worker participation | Current native BabyBear timestamp queries and initialized caller accounting derive participation. The historical zero-clock witness is rejected by current native acceptance; weaker intermediate interfaces retain their own stated scope. |
| Discarded loads | The original Sail claim retains the [discarded-LW restriction](Tests/DiscardedLoad.lean). The named Airbender PC-only-NOP profile is a distinct reference choice. |

The [finding register](FINDINGS.md) distinguishes checked counterexamples,
conditional proof closure and actual implementation enforcement. Temporary
assumptions do not close implementation defects, and unmerged proposals are not
validation. These cases establish no whole-system or cryptographic exploit.

## Sources and pins

| Component | Binding and obligation |
| --- | --- |
| Lean / Mathlib | Lean `v4.31.0` and the pinned Mathlib dependency in [lakefile.toml](lakefile.toml); actual axiom dependencies are audited. |
| Clean | Revision `1e563b9c27991b3795eb440c1ee0757edb4ce8b1`; [compatibility preparation](scripts/prepare_clean.py) guards original hashes and repairs proofs without changing constraint semantics or claims. |
| Sail model/compiler/runtime | Exact revisions, hashes, selected roots and generation boundary are recorded in [Sail provenance](generated/sail-rv32/provenance.json) and [regeneration notes](generated/sail-rv32/README.md). Original standard instruction clauses are preserved. |
| Platform | [Platform support](scripts/SailPlatform.lean) binds explicit device configuration and abstract terminal/reservation handlers. Native ROM/RAM routing and the upstream Sail test-device configuration are distinct bindings around the same instruction clauses. |
| Custom operations | The unmodified [project reference](vendor/airbender/00-master.md) is pinned at `2331d1c511f26c17be85879fbab02ab109aefd05` with its [provenance](vendor/airbender/provenance.json). Applicability to native artifacts remains a review obligation. |
| Imported circuits and tables | [Artifact provenance](artifacts/setup/README.md) records source hashes, native IDs, physical columns, regions, padding and retained circuit identities. Data checks do not prove the generator or parser correct. |

Fixed serialized coefficient equations force BabyBear under primality; generic
capacity/no-wrap arithmetic remains reusable. See the [field guide](Airbender/Review/Helpers/Core/README.md).
A different native field requires its own exported coefficients and checked bindings.

## Import and generation fidelity

[Parse](Airbender/Import/Parse.lean), [Schema](Airbender/Import/Schema.lean) and
[coefficient conversion](Airbender/Import/Coefficients.lean) decode native JSON
into Clean's original constraints and actual imported table data. Imported rows
are not replaced with handwritten mathematical recipes. Small semantic adapters
and checked characterizations connect those rows to their consumers.

Sail generation uses the pinned upstream compiler and selected original roots.
The normal four-byte nextPC assignment is extracted verbatim from the normal
F_Base path, then composed with execution and tick_pc. Translation, pruning,
extraction and path selection remain unchecked connections. Full fetch faults,
interrupts and exceptional execution are outside this slice.

## Modeled tables and logical arguments

Lookup and memory claims use explicit modeled tables and exact full-token logical
matching. Initialization adapters derive native zero seeds, selected-domain
geometry and register coverage; they do not select the intended public Sail state
or discharge separate register value/teardown obligations. See the
[memory guide](Airbender/Review/Helpers/Memory/README.md).

RAM GKR gates compute encoded token products. Equality of sampled products does
not deterministically imply token-multiset equality or establish cryptographic
soundness. Rust/setup correspondence, compiled/cached gate refinement, verifier
refinement, cryptographic enforcement and completeness remain separate work.

## Public state, profiles and external inputs

Public profiles supply initial PC/clock, program bytes, configuration, selected
cell domain and register boundary. Raw byte reads used to bind initial memory
are distinct from instruction-level device routing. Readonly public ROM and
native zero ROM shadows are transported explicitly; no boot copy theorem follows.

Worker-only interfaces retain both clockRoom and invocationHigh. Integrated
caller interfaces derive the corresponding bounds from native clocks/accounting;
actual read values and pointer bounds remain derived from initialized history.
Public modes, selected complete-reference protocols and coverage do not follow
from arbitrary native acceptance.

External streams are independent public inputs with explicit port connections;
the circuit does not authenticate a chosen stream. Original Sail discarded-load
semantics remain distinct from the named project profile. Consult the
[current plan](FORMAL_VERIFICATION_PLAN.md) for remaining and deferred work.
