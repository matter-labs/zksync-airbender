# Trust and review boundaries

The native machine corollaries certify CPU rows only. They use cached CPU
certificates; bigint, extended-round, G and special5 worker equations remain
no-cache flat-constraint premises. Split Keccak uses direct imported worker
constraints and fixed-source certificates, without a compiler capture.
Compiler preservation covers 11 cached compilations.

The source and captured CPU relations are built from this checkout, with upstream `av_gkr_compiler` baseline revision
`c1a662222cafcd96db4383dce737edb79fa62b09`. The restored native delegation
relations admit invalid invocations outside the developers' supported-use domain;
lower-level conditional proofs retain the explicit
[F11 hash witness contracts](FINDINGS.md#f11--hash-witness-contracts-remain-unenforced).
The [supported-use entrypoint](Airbender/Review/Trace/UnifiedReduced/SupportedUseExecution.lean)
derives those bigint/hash conditions from public program safety and exact native
prefixes for bigint, G and extended round. The separate proved full unsigned
target also includes the blessed split Keccak path.
[Verification status](VERIFICATION_STATUS.md) records completed validation and
material limits. The [historical integration record](TRUST_AND_REVIEW_HISTORY.md)
retains earlier experiments and narrower intermediate interfaces.

## Production defects and temporary interfaces

PR #585 changes production crates only through additive artifact export code
and the serialization derives those exports need. Export-specific setup selection
lives inside the export example binary. Existing setup, proving,
GPU scheduling and verifier functions retain their base implementations.
The normal production path does not call the export code.

When verification exposes a production defect, record the source evidence and
required property in [FINDINGS.md](FINDINGS.md). State that property explicitly
as a temporary Lean interface assumption, linked to the finding, and keep the
conditional theorem's scope visible. This is a theorem premise, not a new Lean
axiom or evidence that production enforces the property. Retain the finding and
assumption until the production repair is validated and the relevant artifacts
are regenerated; do not repair production behavior in this PR.

AIH-334 is already fixed upstream by #548 in the base: the EVM verifier pins
window top bits and rejects differing preimage values. Its selection interface
retains formal deployment/layout correspondence. Decoder setup, preprocessing
and query agreement remain part of the external decoder binding. The finding
register distinguishes these obligations from open production defects.

## Review entry points

Start with the [Review guide](Airbender/Review/README.md), then the selected
[circuit contract](Airbender/Review/Circuits/README.md) or
[whole-trace claim](Airbender/Review/Trace/README.md). Review contains the important
composed statements, original reference selection, observable mappings and public
assumptions. Supporting arithmetic and assembly proofs belong in Proofs; a
separate public wrapper for every internal subcircuit calculation is unnecessary.
Native BabyBear entrypoints remain available.

The [compiler review](Airbender/Review/Compiler/README.md) exposes the three
production machine targets and their cached native certificate corollaries.
Native JSON readers and capture bindings live in Import.
Certificate checks and proof assembly live in Proofs.
Exact lookup, state and RAM matching remain explicit.
[Verification status](VERIFICATION_STATUS.md) records the current state.
The earlier dated log is in [verification history](VERIFICATION_HISTORY.md).

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
The three [machine targets](Airbender/Review/Compiler/MachineTargets.lean)
are proved. The unified relation includes external reads, modular MOPs and
complete delegation calls. The full unsigned relation includes blessed split
Keccak. The native adapters cover the six unrolled CPU families and the unified
circuit. The [native acceptance adapter](Airbender/Proofs/GKRProtocol/NativeMachineAcceptance.lean)
closes the CPU and decoder premises. The [three native corollaries](Airbender/Review/Compiler/Theorems.lean)
compose it with the target proofs. The canonical graph uses public program setup.
Item 3 has stopped. The existing checkers remain. Linux validation runs last.

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

## Target instance scope

Each target quantifies one `InitializationWitness`, one window assignment and
one initialization/teardown acceptance premise. Several windows are allowed
within that instance. The Rust unrolled verifier accepts a list of standalone
instances; the unified verifier accepts several trailing initialization-carrying
instances. Both check distinct windows across the concatenated list. The current
Lean boundary and boot-seed proofs do not aggregate that list. Generalization
requires per-instance native witnesses/parameters, concatenated RAM tokens and
global window distinctness; it remains pending as [F13](FINDINGS.md#f13--target-initialization-and-submitted-instance-scope).

The quantified CPU/worker data must represent all submitted circuit instances
in the claimed profile. Full unsigned `workerFamilies` permits bigint, extended
round and G in the standard pool, plus its represented split pool; special5
instances are absent. Reduced permits only extended-round workers and no split
pools. Unified has the four-family standard pool and no split pools. These are
premises on submitted instances. Public no-call premises do not alone establish
absence of excluded submitted worker types; that derivation is not claimed.

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
execution nor outputs. This unified registry excludes special5; the full unsigned
target includes the blessed split registry under its own public-use contract. G
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
| Blessed Keccak coverage | [F12](FINDINGS.md#f12--blessed-split-keccak-coverage-and-validation-boundary): the proved full unsigned target composes all three split workers and the 361-call wrapper. [The native split permutation statement](Airbender/Review/Trace/Workers/Keccak/SplitPermutation.lean) reaches Clean's `keccakPermutation`. Special5 is excluded from the three machine targets and retains its separate 649-call results. |
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
The JSON-to-canonical-table bridge is proved for all three split sources.
The kernel checks source parsing, exact RLE decoding and canonical membership.
Parity and theta/rho include physical padding.
The chi5 certificate uses native query tags 65 and 66.
Those tags exclude zero padding, which its canonical table does not contain.
The original target, setup premises and canonical tables stay unchanged.
The full unsigned proof uses all three source certificates.

The generated source expressions retain each original key, value and field
order. The frontend requires generation freshness and exact byte comparison
with each raw artifact. These checks verify imported values. They do not
supply theorem proofs. The kernel checks source parsing, each distinct RLE
block and complete column decoding. A negative control changes one retained
block and keeps the source bytes fixed. The kernel rejects that control.
The AND result now follows from a proved packed checker for the original Block
statement. See the [selected measurements](VERIFICATION_HISTORY.md#verified-checker-measurements).
The setup-column pilot proves exact block equality with a second kernel-checked
certificate. Columns 2, 4, 5, 6 and 7 use projections of complete capture
certificates. The four wide columns use balanced numeric trees. The checker
validates branch sizes, exact block equality and all requested row counts.
Kernel layout and conversion proofs bind each tree to both native sides.
All public declaration names and theorem statements stay the same. The pending
environment audit must record the changed module origins. Other fact families
still need migration.

Both AddSub arithmetic captures use one closed checker result each. Sixteen arithmetic
captures use direct numeric data. Separate kernel equalities bind that
data to all original source expressions, lowered residuals, computed extensions
and certificates. Further bindings check normalized source rows and both complete normalized
gate sides.
A final binding checks sorted address keys. The numeric checker reads materialized trees. It validates tree
sizes, strict key order, every translation identity and every gate equality.
Its soundness theorem derives the exact original Boolean statement. Public
corollaries retain the original theorem types. The exporter and payload hashes
supply no proof. The kernel checks every data binding and the capture result.
Both cache modes remain required. Bigint and Keccak keep their established
proofs while the dense numeric path remains open.

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
