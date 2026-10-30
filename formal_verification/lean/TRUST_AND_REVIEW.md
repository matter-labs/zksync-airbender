# Trust and review boundaries

The target is the imported richer no-cache relation built from this checkout,
with upstream `av_gkr_compiler` baseline revision
`c1a662222cafcd96db4383dce737edb79fa62b09`. The restored native delegation
relations admit invalid invocations outside the developers' supported-use domain;
lower-level conditional proofs retain the explicit
[F11 hash witness contracts](FINDINGS.md#f11--hash-witness-contracts-remain-unenforced).
The [supported-use entrypoint](Airbender/Review/Trace/UnifiedReduced/SupportedUseExecution.lean)
derives those bigint/hash conditions from public program safety and exact native
prefixes for bigint, G and extended round. Blessed split Keccak remains uncovered.
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

The [compiler review](Airbender/Review/Compiler/README.md) exposes arithmetic,
physical-row logical execution, retained-table supplied-program and explicit-platform
entrypoints, alongside the older compatibility wrappers. Native JSON readers and concrete capture
bindings live in Import; certificate checks and supporting calculations live in
Proofs. Captured-instance scope, exact tuple/state/RAM matching and public
boundaries remain explicit. Logical entrypoints derive helper/member validity
without canonical source framing; the older wrappers preserve their premises.
[Validation evidence](VERIFICATION_STATUS.md#validation-evidence) is the sole
maintained inventory of completed checks, measurements and pending assurance.

[Pooled soundness](Airbender/Review/Trace/Soundness.lean) derives successful
ordinary execution and native terminal PC/cells from initialized matching.
[Unified full execution](Airbender/Review/Trace/UnifiedReduced/FullExecution.lean)
also composes complete bigint, BLAKE2 G, extended-round and special5 Keccak references
with the supported straight-line ordinary registry.
[Native actual-path execution](Airbender/Review/Trace/UnifiedReduced/NativePathExecution.lean)
composes branches, JAL/JALR and repeated-PC loops with complete delegations
under the explicit F11 hash witness contracts and without an occurrence plan;
[complete spans](Airbender/Review/Trace/UnifiedReduced/PathSpanExecution.lean)
derive the full native worker partition/count and algorithms in one history
under their per-trace occurrence plan and complete protocol coverage.
The combined unified relation includes nondeterminism reads, modular MOPs and
delegation calls. Its native soundness proof remains open. The compiler
execution bridge still uses the retained four-entry decoder tables. No proved
whole-execution theorem covers a committed production verifier program yet.
Upstream #531 merged as `06c15f275` and is in this base. The unified base
entrypoint now returns the verified registers. New-base runtime validation
remains pending.
Focused compiler qualification passed in both cache modes. The final group
passed 497 checks. It reuses the unchanged finite-table cache. This result
does not replace the pending frontend build or transitive kernel replay.

A replay ledger is trusted evidence. Exact artifact/tool hashes bind a recorded
pass to its inputs but do not authenticate who produced that pass. CI therefore
reuses ledgers only on the default branch; other refs start with a fresh ledger
outside the checkout and replay dependencies too. The full Linux runtime and
cold-run feasibility of this policy remain unmeasured.

## Checked scope boundaries

Claims retain explicit public program/state/configuration, tracked domain,
modeled lookup tables and exact logical matching. Reads, operand bounds,
decoder selections and worker participation are derived. A local request observation
is weaker than fulfilled worker effects or a complete reference span.

The [supported-use entrypoint](Airbender/Review/Trace/UnifiedReduced/SupportedUseExecution.lean)
takes [ValidDelegationUse](Airbender/Review/Trace/UnifiedReduced/DelegationUse.lean), a
precondition on public code and all independent reference prefixes. It states the
registered wrapper shapes, entry safety and runtime controls/pointers, including
the blessed round masks' zero low limb. Exact native prefix matching and induction
derive the existing bigint/hash worker conditions. It assumes neither desired
execution nor outputs. The current covered registry excludes Keccak (F12); G
pointer separation remains a program obligation. It does not prove that the
verifier checks program safety or that an arbitrary binary satisfies the contract.
The theorem proves instruction-prefix execution; complete algorithm spans retain
their separate coverage and gap conditions.

The lower-level native actual-path entrypoint explicitly assumes the
[F11 hash witness contracts](FINDINGS.md#f11--hash-witness-contracts-remain-unenforced),
implemented by [HashCommands](Airbender/Review/Helpers/UnifiedReduced/NativeMemory.lean)
and its [four predicates](Airbender/Review/Helpers/Context/ExternalBoundary/HashABI.lean).
They constrain private worker-witness controller and pointer reads; the verifier
cannot check them merely from public inputs. They supply no outputs or execution
and are not derived from native acceptance alone. The exclusive round mask is also a witness premise in lower-level integrated
mixed-memory, native-ROM and call theorems. It is not a public input or a
consequence of native acceptance alone. The zero low limb is the
blessed callers' mask rule; arbitrary VM calls have a wider domain. Per-call G/round controls do not enforce
entry at counter/round zero, which the VM requires for a bundle. Complete spans
obtain entry from their per-trace protocol plan; the plan-free theorem proves local
reference calls without this bundle-entry guarantee. Controllers may be loaded or
computed through ordinary instructions; no occurrence plan is supplied. Public program
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
| Bigint commands | F02 controls 0/65537 are outside supported use. The supported-use execution entrypoint derives the worker binding from public reference-prefix validity; lower-level APIs keep the explicit command contract. General native rejection is not claimed. |
| Worker ROM | F04 ROM-pointer invocations are outside supported use. The physical execution profile retains its public tracked-RAM domain, while the lower-level native-ROM transport API keeps its address binding. The original COPY ROM-shadow witness is preserved. |
| Hash witness contracts | [F11](FINDINGS.md#f11--hash-witness-contracts-remain-unenforced) records the four lower-level witness premises and the native prefix bridge from public supported use. G separation remains explicit; no circuit repair is pending for the excluded UB cases. |
| Blessed Keccak coverage | [F12](FINDINGS.md#f12--blessed-keccak-path-is-outside-current-proof-coverage): the provided 361-call split wrapper and its three native workers are required, open obligations for the unrolled full unsigned target. Unified currently excludes special5 calls by public premise. Existing 649-call special5 results remain conditional circuit/protocol coverage. |
| Worker participation | Current native BabyBear timestamp queries and initialized caller accounting derive participation. The historical zero-clock witness is rejected by current native acceptance; weaker intermediate interfaces retain their own stated scope. |
| Discarded loads | The original Sail claim retains the [discarded-LW restriction](Tests/DiscardedLoad.lean). The named Airbender PC-only-NOP profile is a distinct reference choice. |

The [finding register](FINDINGS.md) distinguishes checked counterexamples,
conditional proof closure and actual implementation enforcement. Temporary
assumptions do not close implementation defects, and unmerged proposals are not
validation. These cases establish no whole-system or cryptographic exploit.

## Sources and pins

| Component | Binding and obligation |
| --- | --- |
| Lean / Mathlib | Lean `v4.31.0` and the pinned Mathlib dependency in [lakefile.toml](lakefile.toml). The environment axiom audit is a separate pending gate; direct reports are smoke checks. |
| Mathlib binary cache | Compiled Mathlib-workspace dependencies downloaded by lake cache get are trusted inputs. They are not rebuilt from source in this gate. Hash checks and kernel replay do not establish that a well-typed cached definition matches its pinned source. |
| Toolchain installer | CI downloads the official elan v4.2.4 executable archive for its Linux architecture and verifies its fixed SHA-256 before execution; [workflow pins](../../.github/workflows/formal-verification.yml). Lean remains pinned separately. |
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

The [shared literal importer](Airbender/Import/SetupLiteralTree.lean) retains
complete physical setup rows as literal nodes. It compares every decoded value
with the parsed source. It selects shared nodes by literal equality. It does
not infer an expected arithmetic formula. Kernel proofs check the node values
and derive the operation on all rows. The tree can encode a region whose length
is not a power of sixteen. It adds zero encoding slots after the last native
row. The region keeps its exact native length. Those extra slots cannot supply
table membership. Separate private column declarations keep elaboration bounded.
The JSON-to-canonical-table bridge remains open. Source parsing and exact RLE
column decoding now have kernel proofs for the three split captures. Physical
real-row membership in the canonical tables remains open. The kernel now
checks the physical padding cases. Parser validation supplies column coverage.
Exact final-block certificates supply zero values. Parity and theta/rho
include these rows in their canonical tables. Chi5 needs membership only for
native query tags 65 and 66. Its canonical table excludes the all-zero row.
The kernel checks this exclusion and guarded transport in both cache modes.
The original target, setup premises and canonical tables stay unchanged.
The kernel also checks all five chi5 source input columns and its complete
tag column. The controller source case has full canonical lookup membership.
Exact suffix decoding and the original parse validation supply its positions.
The five arithmetic output columns remain open.

The generated source expressions retain each original key, value and field
order. The frontend requires generation freshness and exact byte comparison
with each raw artifact. These checks verify imported values. They do not
supply theorem proofs. The kernel checks source parsing, each distinct RLE
block and complete column decoding. A negative control changes one retained
block and keeps the source bytes fixed. The kernel rejects that control.
The packed-checker pilot stays unchanged.

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
soundness. For all 22 captured compiled/cached instances, native base-field
arithmetic implies source arithmetic. New physical-row execution entrypoints take
actual arithmetic/active rows plus exact matching of actual native encoding-field
and leaf-weight tuples. Native field/mask/helper identities transport them to source
operands under full native arithmetic, while operand coverage and setup-column
bindings align their primitive/groups and setup. That composition derives authored
membership, helper bounds and Clean/decoder validity without a canonical frame.
The final compressed/sampled rational balance-to-exact-matching step remains an
abstraction, and natural multiplicities are not tied to physical field counters.
Exact state/RAM permutations and public boundary/seed contracts remain explicit. Supplied-program wrappers
require decoder-table equality with the retained capture; they do not establish
arbitrary new setup support. Older framed wrappers remain compatible. These new
connections compile across all 14 actual native row compositions and the public
wrappers; execution/public modules also pass selected-module replay at a 32 MiB
Lean thread stack. The selected frontend regression/freshness scope passes;
full assurance remains pending as described above. See the
[compiler premise table](Airbender/Review/Compiler/README.md#execution-premises).
Universal Rust/setup correspondence, verifier refinement, cryptographic enforcement
and whole-system completeness remain separate work.

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
