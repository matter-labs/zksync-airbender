# Trust and review boundaries

**Review definitions and assumptions for meaning; let Lean check the proofs.**
The kernel checks proofs about emitted objects. It does not establish that those
objects faithfully represent Rust artifacts or express the intended system claim.
[Verification status](VERIFICATION_STATUS.md) is the coverage and gap inventory;
[the plan](FORMAL_VERIFICATION_PLAN.md) contains pending work.

## Review entry points

The [directory review guide](Airbender/Review/README.md) separates
[individual circuits](Airbender/Review/Circuits/README.md) from
[whole-trace execution](Airbender/Review/Trace/README.md). Subdirectory READMEs
identify the local claim, relevant helpers and scope boundaries.

Start with [the property definitions](Airbender/Review/Helpers/Properties.lean).
They depend only on Clean and state soundness, completeness and the circuit relation.
The helper topics are `Core/`, `Decoder/`, `Memory/` and `Context/`; tables,
delegation and unified-machine context retain their own groups.

For individual circuit soundness, start with its `Circuits/<family>/` model and
local claim, then [shared history inputs](Airbender/Review/Helpers/Context/Interfaces.lean),
[public initialization](Airbender/Review/Helpers/Context/Boundary.lean),
[accepted native matching](Airbender/Review/Helpers/Context/Model.lean) and
[the selected row's pre-state](Airbender/Review/Helpers/Context/RowContext.lean).
The accepted initialized history is still part of these claims; reads and ranges
remain conclusions. Circuit setup definitions live in each family's `Tables/`;
shared range/byte/subword constructions live in `Helpers/Tables/`.

For whole execution, start with [Trace/Soundness.lean](Airbender/Review/Trace/Soundness.lean), then
[pooled public inputs](Airbender/Review/Helpers/Context/PooledBoundary.lean),
[native matching](Airbender/Review/Helpers/Context/Model.lean), the
[family registry](Airbender/Review/Helpers/Context/Registries/Pooled.lean), and
[actual public decoding](Airbender/Review/Helpers/Decoder/PooledProgram.lean).
[Execution.lean](Airbender/Review/Trace/Execution.lean) states the shared `Realizes`
conclusion; [SailHistory.lean](Airbender/Review/Helpers/Memory/SailHistory.lean) defines native
row events and the meaning of intermediate and retired states.

`Circuits/` owns row references, artifacts, named mappings and local assumptions.
`Helpers/` owns the shared context; `Trace/` owns instruction execution, terminal
realization and composition. The helper import graph is independent of `Trace/`.
Three circuit theorem modules (jump/branch/SLT, MUL/DIV and shift/binop) still reuse
`Proofs/Trace/PooledExecution.lean`, whose implementation imports jump composition.
Their statements/models remain local; this retained proof dependency is checked
and does not add assumptions. `Proofs/` contains supporting
calculations, interfaces, proof assembly and artifact guards. Review `Import/`
separately for fidelity. Per-circuit `circuitModel` and `InterfaceAssumptions`
remain visible; accepted row membership supplies that row's imported constraints.
Shared initialized history derives bounds, actual reads and preprocessing.
[RowPosition](Airbender/Review/Helpers/Context/RowContext.lean) applies earlier native writes
without assuming successful reads or ISA execution.

Unified models and workers retain their own explicit public contracts. For their
claims and remaining scope, use the status table rather than inferring whole-machine
coverage from a local operation theorem.

The [modular pooled extension](Airbender/Review/Trace/Modular/README.md) connects
ADDMOD/SUBMOD/MULMOD/FMAMOD to the same initialized six-family history, native
boot/ROM view and external padding boundary. Actual Sail MOP decoding derives
native selectors; history derives operands and FMAMOD's old destination.
Arithmetic remains the existing pinned BabyBear project specification. The
combined pooled entry includes exact external-stream consumption; the
[unified modular entry](Airbender/Review/Trace/UnifiedReduced/ModularExecution.lean)
uses actual unified equations alongside standard/TRIADD/XORROT retirement.
Neither extension supplies desired operands or results as assumptions.

[Initialization/teardown](Airbender/Review/Circuits/Initialization/README.md) now
interprets the actual standalone and unified inline GKR slices. Gate satisfaction
proves exact products of computed RAM initialization/teardown tokens, including
actual raw teardown columns and native output wiring. The
[execution adapters](Airbender/Review/Trace/Initialization.lean) derive seed
correspondence, aligned/distinct cells and register coverage from imported
geometry and public distinct windows. Public Sail/program/configuration and
starting PC/clock conditions remain; native ROM shadows are zero independently
of program bytes. Register teardown is outside these RAM-only slices. Exact
logical matching is still assumed separately from product computation;
Rust/parser fidelity and cryptographic enforcement are not inferred.

## Checked scope boundaries

Current native BabyBear acceptance includes #490's active-invocation timestamp
query. [Native exclusion](Airbender/Proofs/Delegation/NativeInvocation.lean) and
[caller accounting](Airbender/Proofs/ExternalBoundary/NativeRequests.lean) derive
complete worker participation. Lower-level generic zero-clock classifications
below retain their mathematical scope; accepted prefix examples from the
[pre-rebase snapshot](https://github.com/matter-labs/zksync-airbender/blob/010c3cbb3c237b6e125277162dd1011c2f212333/formal_verification/lean/Tests/DelegationZeroInvocation.lean)
are historical. The current fixture proves native rejection while preserving
its raw arithmetic, matching and padding behavior.

Keep proof coverage and finding status separate. The
[reviewed-case register](FINDINGS.md#linear-and-open-pr-review--15-october-2026)
distinguishes temporary assumptions for open defects from intended external
interfaces and public profiles. A conditional theorem can be complete while an
implementation finding remains open; an unmerged PR is not evidence of enforcement.

These fixtures explain restrictions on the current claims. They concern the
imported richer relations and logical matching; they do not establish a
whole-system or cryptographic exploit. Keep their public inputs and scope visible
when reviewing or strengthening a theorem.

| Boundary | Checked fixture and consequence |
| --- | --- |
| Inactive padding | [Inactive ADD/SUB row](Tests/InactiveRow.lean): execute zero admits PC 0→4 and result 123. The [external contribution-mask boundary](Airbender/Review/Helpers/Context/PaddingBoundary/README.md) now derives active acceptance/execution by erasing identity factors from exact whole-layout masked state/memory/request matching. Raw padding values need not stutter. Rust/GKR/cryptographic enforcement and artifact correspondence remain external; this is no demonstrated padding bug. |
| Jump termination | [Noncanonical JAL endpoint](Tests/JumpSailHistory.lean): imported constraints, decoding and native matching admit a field-aliased terminal PC that disagrees with Sail. The [canonical verifier-boundary contract](Airbender/Review/Helpers/Context/VerifierBoundary/README.md) now replaces the direct range premise at public jump/pooled entries. Accepted state matching and typed u32 contribution closure derive full raw terminal equality and bounds. F01 is resolved under that external logical binding; the malformed witness remains valid locally and is excluded by the new contract. Cryptographic enforcement, PC-space projection and Rust/artifact correspondence remain external. |
| Discarded LW | [Sparse-memory load](Tests/DiscardedLoad.lean): an accepted native NOP can fail original Sail's LW-to-x0 access. The unchanged-Sail claim retains `NoDiscardedLoads`; the named Airbender profile uses the pinned PC-only NOP rule. |
| Unissued workers | [Historical zero-clock G worker](Tests/DelegationZeroInvocation.lean): its raw arithmetic, token cancellation and padding retention remain checked; current native BabyBear timestamp constraints reject it. [Native accounting](Airbender/Proofs/ExternalBoundary/NativeRequests.lean) derives the occurrence ledger from accepted constraints and initialized caller binding, without a positive-invocation premise. |
| Bigint controls | [Issued unified calls](Tests/UnifiedDelegation.lean): x12 = 0 admits no opcode; x12 = 65537 admits ADD with a nonzero high limb. Current caller-cycle observations hold, while the pinned reference rejects these control words. The temporary valid-command contract now supports [complete bigint reference retirement](Airbender/Review/Trace/UnifiedReduced/BigintCalls.lean); F02 implementation enforcement remains open, and both controls fail that full reference. |
| Worker ROM | [COPY with ROM pointers](Tests/DelegationROMBoundary.lean): zero native shadows and exactly matched worker values can differ from public ROM bytes. Replacing shadow tokens with public bytes breaks matching. A temporary RAM-port contract restricts conditional transport and leaves F04 open. |

The [temporary contracts](Airbender/Review/Helpers/Context/ExternalBoundary/README.md)
also model distinct initialization windows and unqueryable decoder filler.
AIH-334 now has a tested EVM source check for complete, bounded, distinct windows;
its formal correspondence to the selection contract remains external. AIH-336 now
has a source correction for the untagged decoder tail and full-domain CPU/GPU
cache preprocessing, with checked CPU forward regressions. Accelerated runtime
validation, regenerated proof replay and the formal setup binding remain open;
see the [validation scope](FINDINGS.md#aih-336-source-correction-and-validation). No temporary contract
is silently added to the existing general-acceptance theorems or their fixtures.

## Sources and pins

| Component | Source and review obligation |
| --- | --- |
| Lean kernel and standard axioms | Accepted proof-checking foundation. The [axiom audit](Airbender/Checks/Axioms.lean) records actual dependencies. |
| Lean / Mathlib | `v4.31.0`, pinned in `lean-toolchain` and [lakefile.toml](lakefile.toml). |
| Clean | `1e563b9c27991b3795eb440c1ee0757edb4ce8b1`; upstream definitions in `.lake/packages/Clean`. Review their applicability; Lean checks proof terms. |
| Clean compatibility preparation | [prepare_clean.py](scripts/prepare_clean.py) guards original hashes and lists tactic-import, factory-registration and proof-reduction patches. Constraint semantics, algorithms and theorem statements are unchanged; repaired proofs are checked and audited. |
| Sail model/compiler | Pinned source in `vendor/sail-riscv`; exact pins, source hashes and generation details in [provenance](generated/sail-rv32/provenance.json) and [regeneration notes](generated/sail-rv32/README.md). |
| Sail runtime | `lean-sail` revision `c816ea7ad03cce98d51acee252540fd4215fede8`, pinned in `lakefile.toml`. |
| Platform support | [SailPlatform.lean](scripts/SailPlatform.lean), copied by the original backend. Experimental extensions are disabled to match the pinned emulator configuration. Runtime compatibility is proved in [Runtime.lean](Airbender/Proofs/Sail/Runtime.lean); terminal/reservation calls remain abstract parameters. |
| Project profile/custom reference | Unmodified [00-master.md](vendor/airbender/00-master.md) at `2331d1c511f26c17be85879fbab02ab109aefd05`, with [hash/provenance](vendor/airbender/provenance.json). Applicability to the circuit revision remains a review obligation. |
| Base ADD/SUB artifact | `av_gkr_compiler` revision `28ffe3ff0353edd9051485c2974b28b52b495dc4`; [retained no-cache JSON](../../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json), SHA-256 `084a58f08dd122160b548689383f74d4a790c782046f8a5bf43f9f287c22a620`. Other family JSON paths remain in their reviewed artifact declarations. |

## Import and generation fidelity

Clean supplies `Expression`, `FlatOperation`, `Environment`, static tables and
`ConstraintsHoldFlat` directly. The JSON schema is parser data, not a second
arithmetic semantics. Lean's `Json.parse` and typed `FromJson` instances decode
the Rust artifact directly. Audit [Parse](Airbender/Import/Parse.lean),
[Schema](Airbender/Import/Schema.lean),
[Coefficients](Airbender/Import/Coefficients.lean) and
[Embed](Airbender/Import/Embed.lean). Coefficient cast equivalence is proved, but
faithful parsing/emission is not. Placement guards reject missing or ambiguous
logical variables and check memory/witness banks. Named imported descriptors do
not prove Rust preprocessing fidelity. Imported setup-row meanings are checked
separately below; Rust execution and query/authentication binding remain external.

The target remains the richer no-cache representation. Compiled-gate implication,
witness extension and cached-layout equivalence are unproved. Generic prime-field
claims retain their stated minimum moduli and inverse compatibility; they do not
establish import of the native Proth120 artifact with its own coefficients.

Sail standard instructions call original generated clauses, with no replacement
arithmetic specification. Review [generate_sail.py](scripts/generate_sail.py),
[sail_slice.ml](scripts/sail_slice.ml) and the recorded provenance. The generator
extracts the unique normal `F_Base` nextPC assignment verbatim from pinned
`run_hart_active` into `extracted_base_pc.sail`, then compiles it with Sail.
Hashes identify inputs and outputs; extraction, compilation and pruning fidelity
are not proved. The selected successful four-byte path does not include the full
fetch driver, interrupts or exceptional branches. `MemoryPlatform` externals are
abstract conditions, without supplied implementations or project axioms.

Public decoder constructors use actual Sail byte reads and original decoding.
The restricted pure and M-extension interpreter constructors preserve their
configuration requirements, including `misa`; checked frame proofs transport
source evidence through history. The native metadata projection still needs
review against Rust. Custom CSR/Zimop behavior comes from the pinned project
reference and explicit reviewed clauses rather than standard CSR execution.

## Modeled tables and logical arguments

[Shared range definitions](Airbender/Review/Helpers/Tables/Range.lean) now import
actual native setup JSON: the complete virtual 16-/19-bit columns, including zero
padding, and bigint's table-ID-26 region for the 13-bit range. Their exact bounds
are proved from the imported data in [ImportedRanges](Airbender/Proofs/Tables/ImportedRanges.lean),
with the existing generic field scope and public helpers preserved. The
[export/import workflow](artifacts/setup/README.md) includes the selected program,
native IDs/offsets and actual circuit object. [Bigint fixed rows](Airbender/Review/Circuits/Bigint/Tables/Setup.lean)
now also import the six native regions; [structural proofs](Airbender/Proofs/Bigint/ImportedSetup.lean)
recover their exact carry/low-byte meanings and native field membership, and the
existing circuit consumers use those rows. [G controller outputs](Airbender/Review/Circuits/Blake2G/Tables/Controller.lean)
now project the imported native region: [kernel proofs](Airbender/Proofs/Blake2G/ImportedController.lean)
check all 512 rows against the reference and concrete setup, including keys and
discriminator. Generalized controller parameters and inactive/invalid controls
retain their previous scope. [Keccak controller outputs](Airbender/Review/Circuits/Keccak/Tables/Controller.lean)
also import the native region; [kernel proofs](Airbender/Proofs/Keccak/ImportedController.lean)
check all 4,096 keys, six outputs and discriminator against the unchanged
reference and concrete setup. Its generalized controllers and invalid/inactive
rows retain their scope. [G XOR rows](Airbender/Review/Circuits/Blake2G/Tables/XorData.lean)
and [round XOR rows](Airbender/Review/Circuits/Blake2Round/Tables/XorData.lean) also
come from their own native artifacts. [G proofs](Airbender/Proofs/Blake2G/ImportedXor.lean)
and [round proofs](Airbender/Proofs/Blake2Round/ImportedXor.lean) check the
current artifacts' 344,384 G rows and 606,208 extended-round rows, including
carry/packed native regions, padding/tags and field casts. Existing lookup
consumers use those data with their original generic field scopes.
[Keccak fixed rows](Airbender/Review/Circuits/Keccak/Tables/FixedData.lean) also import
all five native regions. [Kernel proofs](Airbender/Proofs/Keccak/ImportedFixed.lean)
recover XOR/Iota/Chi and both rotation pieces, including every key, padding and tag,
and connect the actual lookup consumers without changing controller or field scopes.
Standard fixed tables and selected-program ROM/decoder contents now import actual data.
Their relation bridges and native execution adapters pass the complete library,
test, importer and axiom/review checks. Arbitrary
program/controller interfaces retain their scope. Source parsing/emission, general
Rust refinement and cryptographic query/table authentication remain separate boundaries.

`Accepted` checks imported equations/lookups and logical native state/memory
permutations. Decoder membership and caller/request matching are likewise logical
conditions. [Caller request windows](Airbender/Review/Trace/Delegation/RequestHashWindows.lean)
reuse these checks at aligned instruction cuts after clock two. Exact worker/caller
multiplicity, slots and full CSR families are derived. Generic window
decompositions retain all prefix effects; current native BabyBear acceptance
separately excludes active zero-clock workers. Standalone hash-window claims retain explicit worker-only
matching and protocol ABI. [Joint instruction windows](Airbender/Review/Helpers/UnifiedReduced/Windows.lean)
now derive actual shared cut states and canonical boundary tokens from architectural
matching. Machine ports include native offset zero; Clean event clocks add one.
[Joint caller-only hash windows](Airbender/Review/Trace/UnifiedReduced/JointHashWindows.lean)
now bind the complete references at those same states. Worker boundaries are
projected from shared matching and x0 refreshes are removed as Sail no-ops. Public
mode/count, prefix scope and modeled tables remain explicit; no worker-only
permutation or intermediate state is an input.
[Mixed-history worker projections](Airbender/Review/Helpers/UnifiedReduced/WindowSchedule.lean)
derive selected caller regions from accepted clock/request matching. Public cuts
must lie inside the native path, with duration four times the selected worker
count; no caller selector or instruction schedule is supplied. Earlier ordinary
effects remain in the joint prefix, rather than a worker-only prefix projection.
Prepared G and Keccak spans now reach their complete references through
[prepared hash windows](Airbender/Review/Trace/UnifiedReduced/PreparedHashWindows.lean).
The public instruction registry, worker-free final preparation cycle, selected-span
family, call count and four-tick duration remain explicit. Bigint, G and Keccak
workers outside that span stay in joint matching; extended-round workers require
separate mask transport. No bigint opcode-validity condition is added. Earlier worker effects,
stay in the actual prefix. The old zero-clock prefix example is historical. Worker boundaries, controls
and caller regions are derived from shared matching, with no supplied worker masks.
[Prepared hash chains](Airbender/Review/Trace/UnifiedReduced/PreparedHashWindows.lean)
now bind two complete G/Keccak references to one continuous architectural-memory
execution. The first span's actual finish initializes the gap and then the second
span. Native tokens and clocks survive every cut; both preparation controls and
reference results are derived. Public span counts/durations, cut order/alignment,
literal registry and nonround worker scope remain explicit. This does not establish
whole instruction retirement or that arbitrary acceptance has complete-span shape.
[Prepared hash sequences](Airbender/Review/Trace/UnifiedReduced/PreparedHashWindows.lean)
extend this to an arbitrary nonempty ordered list in the same nonround scope.
Each window and its gap starts from the preceding actual state; the mapping binds
all complete references, request permutations and counts to those exact states.
Public ordering/alignment and each span's preparation/mode/count/duration remain
inputs. This does not derive unrestricted protocol shape from general acceptance.
[Prepared extended-BLAKE windows](Airbender/Review/Trace/UnifiedReduced/PreparedRoundWindows.lean)
also bind complete compression at those actual cut states. Raw matching and the
ordinary LUI token derive exclusive round masks before Sail value transport.
Public suffix duration derives its caller selectors; the empty worker prefix and
ten-position controller stay explicit. Later rounds may remain outside a selected
seven-/ten-round window. The broader
[prepared protocol sequence](Airbender/Review/Trace/UnifiedReduced/PreparedRoundWindows.lean)
derives exclusive masks from raw prefix/window matching within each public
LUI-prepared controller region. Earlier workers remain in history; the ten-position
bound applies to each region. Explicit coverage places every extended-round worker
in such a region before mask-dependent Sail transport. All three complete references
then compose at the same continuous sequence states. Global prefix emptiness,
pool homogeneity and a global ten-row cap are absent from this entry; local family,
count/duration, literal preparation, cut order and region coverage remain witness-
shape boundaries. They are not a theorem that general acceptance runs valid
protocols. Broader preparation/protocol binding and whole mixed retirement remain open.
The [public-program sequence entry](Airbender/Review/Trace/UnifiedReduced/Theorems.lean)
now derives selected worker families and complete call counts instead of assuming
them. `ProgramCallerRegion` excludes ordinary entries from a public PC/clock
interval and fixes its full CSR family. With a sequential ordinary registry,
accepted state matching locates every instruction and request matching derives
its worker, family, native slot and count. The public reference duration determines
the count independently of the worker list. `ProgramProtocolWindowInputs` keeps
preparation and cuts explicit. `ProgramPreparedProtocolInputs` also replaces the
local extended-round worker shape with `ProgramRoundRegionInputs`: public CSR
regions, ordered aligned cuts and at most forty ticks derive family, row count,
the ten-position bound and exact duration. The existing raw matching/LUI proof
then derives masks before transport. `ProtocolContextInputs` shares the unchanged
public memory/program/table context with the legacy regional interface.
`ProgramRoundCallerCoverage` constrains public decoded round CSR addresses rather
than selected rows. The public coverage theorem derives prepared-region membership
for every live extended-round worker and proves its converse. Public LUI preparation
and raw regional matching then derive all issued round masks without full worker
coverage. The local raw-mask helper uses only `ProtocolContextInputs` and its
selected region; global coverage is supplied separately for whole-pool transport.
In this public sequential/controller profile, full worker coverage is equivalent to the absence
of zero-clock extended-round workers. This is an exposed conclusion, without a
new nonzero-invocation premise. Full coverage remains explicit before global mask
transport at these generic entries; native BabyBear exclusion supplies the
zero-clock boundary in the full mixed entry.
Empty prepared cuts retain the actual clock-six LUI token; wrong flags/family,
oversized/reversed/unaligned cuts and two
round bits are rejected. General protocol validity and invalid-call ABI remain
separate; full caller retirement is checked under the profiles below. Both invalid bigint controls still satisfy
the program-derived request/schedule claim.

The modular variant uses `WrappedProgramCallerRegion`: public ordinary exclusion
and full CSR-family selection at every clock in the interval. The aligned
sequential/comparison registry and modeled setup derive actual modular addresses;
state/request matching derives caller participation, counts, family and unique
slots. No PC injectivity or no-wrap premise is supplied. The modular controller
and prepared sequence entries derive local shape before reusing the existing
raw-mask and complete-reference proofs on one continuous history. Public
cuts/preparation/reference duration and global extended-round worker coverage
remain explicit. `WrappedProgramRoundCallerCoverage` now covers every aligned
occurrence of each decoded round CSR between the supplied initial and terminal
native clocks. Strict native four-tick increments and state matching derive the
actual clock interval without assuming native row order. Modular address matching
then locates the actual caller occurrence, including repeated addresses, and
full-width request matching derives round-worker membership exactly for live
invocations. The modular issued-mask theorem reuses public LUI preparation and raw
regional matching, without full worker coverage. Full coverage is equivalent to
absence of zero-clock extended-round workers. This generic implication uses
current native BabyBear exclusion at the full mixed entry. Public CSR bytes, native endpoints, modeled setup and
logical matching remain explicit. A public code-policy fixture with a 2^32-tick
recurrence rejects covering only either occurrence; it makes no accepted-trace
claim. COPY and the real comparison-wrap fixture retain their native behavior,
both bigint controls remain admitted. The historical unissued G-prefix is
rejected by the current native timestamp constraint.
[Unissued worker binding](Airbender/Review/Trace/UnifiedReduced/UnissuedWorkers.lean)
now derives the original public seed token for every read of a zero-clock worker,
including its actual value, canonical word and raw zero timestamp. Every worker
write is at least clock two. The mandatory first machine port, strict memory
order and native clock alignment derive machine clocks at least four, so no
machine write can feed an unissued read before clock two. Logical memory matching
therefore roots those reads directly in initialization. No operation mask, desired
read or additional initial-clock floor is supplied. The actual public x12 high
limb then characterizes every exclusive extended-round mask exactly as
`flags + 8 * 2^round`, with flags below eight. The control assertions prove both
directions for the existing field bound, independently of XOR-table contents.
A zero public x12 seed implies no exclusive mask for such a worker; this is a
conditional classification, without an accepted unissued-round witness or an
exclusion/inertness claim for generic fields. Current native BabyBear
acceptance excludes the historical G prefix.

`WorkerInvocationUniqueness` now extends the earlier live-only scheduling fact
to every native worker occurrence. All four imported layouts transfer fixed GPR
x10 at invocation plus two. Projecting those actual ports from the existing
initialized-memory key-uniqueness theorem distinguishes both numeric and raw
invocation clocks across the whole worker pool. The public tracked domain must
have distinct physical cells; no round mask, opcode validity, operation effect,
nonzero invocation or global hash coverage is supplied. Consequently the actual
zero-clock sublist has length at most one. This counts list occurrences and also
rejects two identical rows. Current native BabyBear constraints separately exclude active zero clocks,
so no single or duplicate active-zero pool is accepted. The historical raw
worker and its request cancellation remain checked alongside current rejection.
Both invalid bigint controls retain full invocation uniqueness.

The [all-worker execution entry](Airbender/Review/Trace/UnifiedReduced/Theorems.lean)
uses that full uniqueness to derive actual pre/post-states for every worker in
one architectural history, including the unissued case. Native machine clocks
are at least four; the unissued worker's exact transfer group is clock three.
The native write floor excludes any earlier transfer, so its actual pre-state is
the public initial state. Its post-state then initializes every later transfer
and the same execution reaches shared terminal cells. Raw grouping and per-port
observations assume only public initialization, distinct aligned cells and native
matching, without operation masks, valid bigint controls or positive invocations.
The closed BabyBear result reuses existing history realization and retains its
explicit modeled setup/tables and extended-round masks. This does not execute
unsupported round controls or establish a full CSR ABI. Live COPY and both invalid bigint controls instantiate this result. The
historical G-prefix execution belongs to the pre-#490 snapshot; current native
BabyBear acceptance rejects that witness. Every native machine row also has
actual cycle states in the same history: strict memory order and alignment
derive its positive clock. The caller-cycle entry reuses this bound for fetch,
observations and PC retirement, without a separately supplied positive initial
clock. Both invalid bigint controls and LW/SW fixtures inhabit that entry.
Full mixed execution adds complete reference calls under the command and public
protocol/RAM profiles described below.

The [PC-relative preparation entry](Airbender/Review/Trace/UnifiedReduced/PCRelativePreparation.lean)
computes a control with original public AUIPC decoding. Modular public
sequential/comparison code and native PC/clock matching derive its actual address;
accepted arithmetic equations derive the RV32 sum of that PC and the U-immediate.
The canonical native token survives prefix matching at cut minus two, and the
same initialized history supplies its actual Sail cut read. There is no expected
output, desired operand or selected native row premise. The final preparation
cycle stays worker-free; earlier issued and unissued effects remain. Modeled
setup/tables, public initialization and existing extended-round ABI remain
explicit. Fixtures check nonzero PCs and an overflowing sum, retain clock-six
tokens, and reject a wrong immediate or fabricated read. This proves preparation
and memory transport. Complete selected G/Keccak reference integration now uses
the source interface below. General operand-dependent preparation, jumps/branches
and whole caller retirement remain separate.

The [computed hash-window inputs](Airbender/Review/Trace/UnifiedReduced/ComputedHashWindows.lean)
admit literal or publicly placed AUIPC preparation for complete selected G/Keccak
references and nonempty ordered lists. AUIPC's address-plus-U-immediate equation
is a condition on decoded public code placement. It supplies no current-state
control value: native constraints/matching identify the actual instruction, derive
its canonical token at cut minus two and transport the actual cut read. The same
existing reference and sequence algorithms retain every gap and intermediate
state in one initialized history. Legacy literal entry points keep their contracts
and use that shared proof. Selected family, mode/count/duration, nonround worker
scope, public initialization/domain/setup/tables and logical matching remain
explicit. The preparation fixtures check G's 128 and Keccak's wrapped zero reset,
actual reads and clock-six tokens; wrong placement and incomplete windows are
rejected. These are preparation/guard fixtures, with complete-reference claims
remaining arbitrary-witness theorems under the stated ABI. The bigint and
ROM-shadow ABI gaps stay exposed. The new public modular-region entry derives caller rows, exact native
request slots, worker family and count before applying that same composition.
It supports either source and arbitrary nonempty ordered lists, retaining public
mode/code/duration and the global nonround boundary. Native AUIPC preparation
witnesses derive empty-region counts; incomplete durations, cuts past the native
terminal and regions containing ordinary preparation code are rejected. The public-region entry retains every accepted earlier worker effect.
The [source-aware round regions](Airbender/Review/Trace/UnifiedReduced/ComputedRoundRegions.lean)
now derive actual round-zero tokens from either preparation source and exclusive
regional masks from raw initialized matching. Public modular controller code,
aligned cuts and at most forty ticks derive local family/count/duration and the
ten-position bound. No control read, mask, empty prefix or global ten-row cap is
supplied. Global memory transport keeps full round-worker coverage explicit;
local regions do not exclude unissued workers elsewhere. Legacy LUI regional-mask
and global-memory entries keep their signatures and share this proof. A native
AUIPC fixture at PC 524288 derives x12 = 65537→524288 and the clock-six token;
it inhabits an empty controller region and its global context. Wrong public flags,
invalid cuts and two simultaneous round bits are rejected under the stated ABI.
These are preparation/empty-region fixtures; nonempty region masks are general
accepted-witness theorems. Source-aware public modular round-CSR occurrence coverage now
derives precisely live regional membership and all issued masks. Every aligned
occurrence is covered, retaining repeated RV32 addresses. Full round coverage is
equivalent to absence of zero-clock round workers. CSR coverage alone does
not supply that absence; current native BabyBear timestamp constraints do. The new complete entry admits G, extended-BLAKE and Keccak
reference lists with literal/AUIPC preparation in one continuously initialized
history. Public modular caller/controller regions derive shape, and the existing
composition retains every gap and actual cut state. Full round-worker coverage
stays explicit. Legacy coverage/reference/list signatures remain and share these
proofs. The native preparation/empty-region fixtures inhabit the new public
context and reject incomplete reference counts/durations and cuts past the native
terminal. Complete references/lists remain general accepted-witness theorems;
these fixtures do not construct complete native reference windows. Broader
operand-dependent preparation and jumps/branches remain outside the frozen
preparation scope; whole CSR retirement is checked under the profiles below.

The separate [register-dependent ADDI entry](Airbender/Review/Trace/UnifiedReduced/RegisterPreparation.lean)
derives the actual final row from public modular code and native clocks. One
initialized prefix supplies its actual source state; memory induction supplies
operand bounds, and imported arithmetic derives the RV32 sum with Sail's original
signed immediate extension. The same native cycle supplies the actual cut read
and canonical output token at cut minus two, including source/destination aliases.
No operand read, bound, selector, intermediate state or prepared value is supplied.
Only the final cycle is worker-free; earlier issued/unissued effects remain.
Public domain/setup/tables and the existing round-mask boundary stay explicit.
Native fixtures check 65537→65665 and 65537→65536, retain clock six and reject a
wrong immediate/fabricated source. The old unissued-prefix fixture is historical. Legacy literal/AUIPC signatures
remain and share arithmetic/output-token helpers. The
[consecutive literal→ADDI source](Airbender/Review/Helpers/UnifiedReduced/RegisterPreparation.lean)
now binds a protocol entry constant through public instructions. Strict native
clocks and initialized prefix/suffix matching identify the actual first operand
with the preceding literal's canonical token; the existing distinct public domain
supplies uniqueness. This raw proof precedes Sail transport and round-mask
derivation, preserving the dependency order. No actual read or bound is an input.
Both final preparation cycles are worker-free; earlier effects remain. The third
source feeds the existing complete G/extended-BLAKE/Keccak windows and lists,
including public modular shape and raw regional masks, with the same coverage,
domain/setup/table and logical-matching boundaries. Native fixtures derive
65537→127→128 and 65537→129→128 with aliases, signed −1 and clock ten. Wrong
immediates/public constants, fabricated operands and incomplete references are
rejected. Complete reference claims remain general accepted-
witness theorems; the fixtures cover preparation/empty-region guards. Nonconsecutive
dataflow and the admitted broader operations are described below; additional
variants remain outside the frozen scope.


The [finite public register-chain entry](Airbender/Review/Helpers/UnifiedReduced/RegisterChains.lean)
extends literal/AUIPC roots with any finite sequence of consecutive ADDIs,
including changes of nonzero register and aliases. Values are indexed by the public
instruction expression. Induction derives each canonical operand token through
raw initialized matching and strict clocks, then native arithmetic derives the
next result. The same token helper serves the legacy two-instruction source;
its signatures remain unchanged. This dependency precedes Sail transport and
regional round-mask derivation. The new source feeds all existing complete
selected-reference window/list interfaces with their existing domain/setup/table,
coverage and logical-matching boundaries. Each selected preparation cycle is
worker-free; all earlier effects remain. Native reversed-row three-instruction
fixtures compute x12 = 127/129, then x10 = 128, then x12 = 128, retaining canonical
clock fourteen. Actual prefix/cycle reads and matching retain the intermediate
register values; wrong immediates/constants, fabricated middle reads and
incomplete references are rejected. AUIPC fixtures inhabit the root case.
These are preparation/guard fixtures; complete references remain general
accepted-witness theorems. Admitted gap instructions and full mixed
retirement are described below; further variants are outside the frozen scope.


The [public register-dataflow entry](Airbender/Review/Helpers/UnifiedReduced/RegisterDataflow.lean)
now allows intervening arithmetic, bitwise/shift/REV8, comparison and admitted
TRIADD/XORROT writes to other nonzero GPRs, plus selected LW/SW gaps.
Original public instruction constructors bind the destination;
successful public decoding retains supported RV32 shift-payload checks. Native
decoder equations derive its GPR bank and index without an operand bound or
instruction result. A gap may read the tracked register and refresh its timestamp. Public decoding derives the real destination;
raw initialized matching and readonly-port preservation derive the tracked value,
retaining the gap's actual write. Induction alternates these gaps with computed
ADDIs before Sail transport or regional round-mask derivation. No desired read,
operand bound, selector, inert-gap or intermediate-state premise is supplied.
Exact prefix matching binds the boundary tokens to their native transfers.
A tracked token after a gap keeps its actual native clock; it need not be the
last destination token at cut minus two. A final public ADDI derives the fresh
canonical output required by the existing complete selected-reference interfaces,
with their domain/setup/table, coverage and logical-matching boundaries unchanged.
Each selected ordinary cycle is worker-free; caller gaps retain their workers.
Native reversed-row
fixtures prepare x12 = 127/129, copy it to x10 in the gap, then derive x12 = 128
with signed +1/−1. The gap changes x10 from 65537 and refreshes x12 at clock
eight; final output retains clock fourteen. A forged source clock ten passes
local native constraints/timestamp lookups but fails joint architectural matching.
Wrong constants and incomplete references are rejected. The actual unissued
G-prefix effect remains admitted. These are preparation/guard fixtures; complete
references remain general accepted-witness theorems. New reversed-row ADD/SUB
fixtures read x12 twice, preserve its value 127/129, write x10 = 254/0 and retain
the second readonly refresh at clock nine. The final signed ADDI derives x12 = 128
at clock fourteen. Wrong public destinations and instruction forms are rejected.
A final source that reuses clock eight still passes all local native constraints
and timestamp queries, but global token counts reject its second consumption.
Native XOR/AND gaps now also read x12 twice, preserve 127/129, write x10 = 0/129
and retain the second readonly refresh at clock nine. The final signed ADDI
derives x12 = 128 at clock fourteen. Stale clock-eight sources remain locally
valid and globally rejected; wrong public destinations/forms, illegal shifts
and discarded binary destinations are rejected at their stated boundaries.
All four original comparisons, TRIADD and the four pinned XORROT forms now
derive the same GPR destination footprint without operand values, predicate bits
or instruction results. Native SLTU/TRIADD gaps retain two aliased x12 reads,
preserve 127/129, write x10 = 0/65795 and retain the clock-nine refresh before
final x12 = 128 at clock fourteen. TRIADD consumes the actual old x10 = 65537.
Stale sources remain locally valid and globally rejected; wrong destinations/
forms, unsupported MOPs and discarded selected destinations are rejected at
the public-registry boundary. Pinned custom clauses are unchanged; this memory
preparation claim does not assert full custom retirement or a Zimop fallback.
LW/SW gaps now have separate public scopes. Original decoding derives the LW
GPR destination, including the native NOP projection for LW-to-x0, or SW's RAM
write bank. Native bank separation and initialized matching preserve the tracked
GPR without a supplied effective address, loaded value, store result or inert-gap
premise. Every other transfer remains in the exact prefix/window matching. Native
RAM fixtures initialize x10 = 4194304 and RAM[4194304] = 42. LW changes x10 to 42
and refreshes the RAM token at clock nine; SW consumes actual x12 = 129, writes
RAM = 129 at clock ten and refreshes x12 at clock nine. The tracked literal token
stays at clock six after LW. A discarded, misaligned LW-to-x0 is also admitted:
its native gap touches only x0, RAM and the tracked literal retain clock zero/six,
and the program fails NoDiscardedLoads. Final signed ADDIs still derive x12 = 128
at clock fourteen. Fabricated fresh source clocks and a fabricated RAM read of 43
pass local native constraints/timestamps but fail initialized matching. Wrong
public load destinations and store sources are rejected. These are native memory
preparation claims; the original Sail discarded-load mismatch and native ROM-shadow
boundary remain explicit. No original memory-clause retirement is added.

Caller gaps now preserve tracked GPRs outside x10/x12. Public modular code
excludes ordinary entries at the selected address; accepted decoding and PC/clock
matching derive the caller. The original imported port descriptors derive the
write footprint of all four worker layouts: bigint/BLAKE can write x12, Keccak
can write x10, and other fixed-register accesses only refresh values. RAM writes
remain in the same initialized history. No worker-free gap, selected worker,
valid control, nonzero invocation, desired read or inert effect is an input.
The raw token induction feeds the existing final ADDI and complete selected-reference
interfaces, retaining their domain/setup/table, coverage and matching boundaries.
A [reversed-row literal→COPY→ADDI fixture](Tests/UnifiedDelegation.lean) derives x13 = 0→127→127 while COPY
changes actual x12 = 128→0; final ADDI restores x12 = 128 at clock fourteen.
The tracked x13 token retains clock six, and the actual x11 pointer refresh retains
clock eleven. A fabricated clock-eleven x13 source satisfies local constraints and
timestamps but fails initialized matching. Both issued invalid bigint controls
also retain the x11 refresh law; ordinary-code gaps and incomplete reference
windows are rejected. Zero-clock prefix effects, ROM-shadow transport and discarded
loads keep their existing scope. This proves memory preparation, not full custom
CSR retirement. General operand-dependent worker writes to tracked x10/x12
and broader operands remain open; no preservation is assumed.
The bigint caller return now has its own checked boundary. `CallerControlPreparation`
uses public modular CSR-region code and the aligned ordinary registry; initialized
native clock order derives a positive selected cycle, and state/request matching
derives its unique bigint worker. Native constraints under the existing modeled
tables derive x12's returned word as zero or one, including a zero high limb.
Raw token classification uses native matching, initialization and modeled tables
before round masks. Raw prefix matching retains the actual worker token at cut
minus one; strict order
rejects consuming that token again before the cut. `BigintControlBoundaryExecution`
then realizes the actual x12 read in the same initialized history, without an
incoming opcode/control restriction, supplied output or intermediate state.
The public `Caller.bigint_control_boundary_soundness` entry keeps the existing
field/inverse, program/domain, table, round-mask and logical-matching boundaries.
A [native COPY-with-carry fixture](Tests/UnifiedDelegation.lean) reads a 256-bit all-ones source from public RAM,
returns x12 = 192→1 at clock seven and retains the source RAM word 0xffffffff.
COPY without carry returns zero; both invalid incoming controls 0 and 65537 also
retain actual zero returns at that clock. A fabricated return of two, wrong public
family, ordinary-code selection and a cut past the terminal are rejected.
This classifies the native returned bit; it does not validate the incoming bigint
ABI or prove full CSR retirement. The unissued-worker, ROM-shadow, terminal-PC and
discarded-load cases remain exposed.

`BigintReturnPreparation` binds the following original ORI of x12 with one to
that actual native return. Raw initialized matching derives the ORI source
from the retained worker token, and the existing clock inverse derives the byte
inverse. Modeled byte lookups and public decoding derive ORI's selectors, operands
and result one for either return bit. The `PublicRegisterDataflow.bigintReturn`
root then joins the existing ADDI and selected-reference preparation interfaces;
no expected source, zero-return condition or new field premise is supplied.
[Concrete reversed-row traces](Tests/UnifiedDelegation.lean) check COPY→ORI→ADDI
and carry-COPY→ORI→ADDI, plus both invalid incoming controls 0/65537. The actual
worker write retains clock seven, normalized one clock ten, and final control 128
clock fourteen. One initialized history retains the worker return and final control.
A fabricated clock-six source passes native constraints/timestamps and fails shared
matching. XORI is rejected by the public scope, and XORI of return one with one
cannot supply normalized one. An incomplete 56-call G window remains rejected.
The existing public domain, modeled tables, logical matching and complete selected
protocol scopes remain explicit. General operand-dependent x10/x12 results,
broader operations and whole caller retirement remain open.

[Control preparation](Airbender/Review/Helpers/UnifiedReduced/ControlPreparation.lean)
uses a public ordinary ADDI-from-x0/LUI registry and a worker-free final preparation
cycle. The registry may be uniform, contain different literals/registers, or admit
arithmetic, LW/SW, bitwise/shifts, REV8 and supported TRIADD/XORROT along a straight
path with callers. The sequential profile is stated on original public instruction
forms, not assumed native selector bits. The separate aligned
[`WrappedSequentialProgram`](Airbender/Review/Helpers/UnifiedReduced/ControlPreparation.lean)
adds original SLT/SLTU/SLTI/SLTIU. Modeled setup and `4194304 ≤ p` remain explicit;
accepted constraints derive comparison cleanup/carry values and modular RV32
PC/clock addresses. No native successor or wrap flag is supplied. The
[wrapped comparison regression](Tests/UnifiedComparison.lean) checks SLTIU at
`0xfffffffc` and ADDI at zero, actual x12 = 65537→1→0, retained write clocks
six/ten, and rejection of a wrong literal, fabricated read or misaligned public
code. Jumps/branches remain outside these preparation registries. Public
selected caller/controller regions now also use modular addresses. Global public
round-CSR occurrence coverage and issued masks also support this modular registry.
Preparation transports actual memory;
it does not assert successful retirement of every prefix instruction or remove
the discarded-LW profile boundary. Actual decoding and accepted constraints derive
PC increments. Only the final preparation must be the specified literal; its
address follows from native PC/clock increments and state matching. Earlier
workers remain connected. The original extended-round first-span scope retains
its empty prefix while regional composition uses controller coverage. Accepted
decoding, clock matching and writes derive the actual control and retained timestamp.
The selected registry and cut bounds remain public; no desired control value at an intermediate state is assumed.
The [prepared control window](Airbender/Review/Trace/UnifiedReduced/ControlPreparation.lean)
connects two prepared controls through the same actual intervening machine/worker
history. Prefix/window matching composes the second boundary; neither state nor
control is an input. This is preparation/transport, with whole instruction retirement separate.
[Caller cycles](Airbender/Review/Trace/UnifiedReduced/CallerCycles.lean) bind original
public fetch, full-CSR worker identity, selected local references, actual port
observations and Sail PC ticking. [Shared cycle composition](Airbender/Review/Trace/UnifiedReduced/MixedCycles.lean)
now combines these observations with original ordinary/custom retirement, every
worker's call states and the complete raw native PC/clock path in one initialized
history. The same actual final memory agrees with terminal cells in the retired
terminal-PC view. [RetirementProfile](Airbender/Review/Helpers/UnifiedReduced/RetirementProfile.lean)
retains public configuration/register initialization, readonly code, tracked-RAM
data and the unchanged-Sail discarded-load restriction. Reads, bounds, decoding
and schedules remain derived. The statement explicitly does not conclude a
successful full custom-CSR reference sequence. Both invalid bigint controls
instantiate the shared certificate. The historical zero-clock G is now
rejected by current native BabyBear timestamp constraints.
No positive initial-clock premise or valid-control assumption is added to that
older certificate. The stronger
[full mixed execution theorem](Airbender/Review/Trace/UnifiedReduced/FullExecution.lean)
now proves a genuine complete reference chain under the explicitly temporary
F02 bigint-command contract. Native BabyBear timestamp constraints and
initialized caller accounting derive the occurrence ledger internally. The existing public
prepared-protocol profile derives full hash ABI and schedules; initialized history
derives every operand, pointer and exact full-state write/frame. Original Sail
PC retirement links ordinary and caller steps from the actual public initial
state to terminal PC/cells. Public initial PC, configuration, modeled tables,
logical matching, readonly code and tracked-RAM domain stay explicit; nextPC is
not assumed prepared. This closes conditional integration, while F02/F04
enforcement remains open. Padding has its separate authorized contribution boundary.
Native columns retain full address/time/value limbs, including readonly
clock refreshes. Bounds, latest-write reads and Clean online-consistent histories
are derived from those relations and public initialization. Retiming introduces
initialization writes and preserves addresses/values; it does not prove cryptographic
permutation or lookup enforcement. Prover/verifier refinement and protocol soundness
are separate obligations.

[Issued hash segmentation](Airbender/Review/Trace/UnifiedReduced/Segmentation.lean)
closes coverage for the existing unified public prepared-protocol profile.
`ProgramHashCallerCoverage` quantifies every occurrence of public hash CSR code,
including repeated RV32 addresses; bigint callers may remain in gaps.
`IssuedHashSegmentation` derives unique window assignment, exact worker/request
multiset partitions and the sum of complete-reference call counts through
`Caller.hash_segmentation_soundness`. No selected worker coverage or desired state
is supplied. `Caller.segmented_hash_sequence_soundness`
combines this partition with the existing complete G, extended-BLAKE and Keccak
references at the same continuous-history states. Mode, public cuts/duration,
code coverage, modeled tables, logical matching and the existing global round-mask
scope remain explicit. This does not infer protocol shape from general acceptance.
The generic partition classifies uncovered hash workers as zero-clock
residuals. Current native BabyBear constraints exclude active residuals. An issued G worker is covered at its
actual clock-five invocation, while its one-call interval cannot satisfy the
56-call reference scope. Missing windows, wrong families, repeated-address omissions
and overlap are rejected. All four COPY/carry/invalid-bigint preparation fixtures
remain admitted outside the hash partition. Whole custom-CSR retirement is now
checked under the named temporary contracts above; unrestricted invalid-call/ROM
behavior remains separate.

## Public state, profiles and external inputs

[InitialImage.lean](Airbender/Review/Helpers/Memory/InitialImage.lean) reads actual Sail GPRs
and bytes over a distinct public cell domain; missing cells fail. Public inputs
bind initial PC/clock, configuration, program bytes and modeled ROM. Relevant
memory claims retain alignment, ordinary-address/domain and platform conditions.
Per-row expected reads, operand bounds and execution results are conclusions.

The [initialization profile](Airbender/Review/Helpers/Memory/Initialization.lean) fixes zero
GPR/non-ROM RAM and PC zero. [Native ROM view](Airbender/Review/Helpers/Memory/Native.lean)
keeps zero native ROM shadow slots separate from public code bytes. Slot masking
comes from `mask_read_for_witness` in `riscv_transpiler/src/replayer/mod.rs`;
zero seeds come from `inits_or_teardowns_as_flattened_relation` in
`prover/src/gkr/prover/forward_loop/utils.rs`. Checked public-byte view conversions
preserve the relevant constraints, queries, ports, clocks, outputs and matching.
[Unified NativeROM.lean](Airbender/Review/Helpers/UnifiedReduced/NativeROM.lean) exposes its
projection explicitly. Rust fidelity and cryptographic enforcement remain external;
the [native mixed-ROM result](Airbender/Review/Trace/UnifiedReduced/NativeMixedROM.lean)
now composes public boot initialization, native ordinary ROM interpretation and
RAM-worker transfers in one physical history with terminal agreement. F04's
RAM-port contract stays explicit; its implementation enforcement and full
custom-CSR retirement remain separate. The accepted ROM-shadow case is retained.

The unchanged-Sail theorem retains `NoDiscardedLoads`: an accepted native NOP
can fail an actual Sail load under sparse memory, as
[DiscardedLoad.lean](Tests/DiscardedLoad.lean) checks. The named Airbender
`profileClause` implements the pinned LW-to-x0 PC-only-NOP rule through Sail's
ADDI x0,x0,0 clause. Keep that profile connection distinct from original LOAD
semantics. Arithmetic writes to x0 use their original clauses.

[NonDeterminism.lean](Airbender/Review/Helpers/Decoder/ExternalInput.lean) receives an external
stream independently of the witness. `StreamPorts` explicitly connects native
response ports; the circuit does not authenticate a fixed stream and permits
different responses. Native clocks derive positions, and the execution claim
concludes the exact consumed count. Hints consume no word and make no application
I/O claim. Native ROM views must preserve this input connection.

The [verifier boundary](Airbender/Review/Helpers/Context/VerifierBoundary/README.md)
records the inspected unrolled and unified total-statement paths at revision
`0dc0a631349462700825f326516d36200be30edc`, with exact source blobs. Both read the
final PC as u32, split it into low/high limbs and incorporate its PC-space
contribution into global permutation products. `Binding` is the explicit logical
tuple-closure contract; sampled product equality alone is not multiset equality.
The encoding proof preserves the full PC, and cancellation against accepted native
state matching proves equality of both raw terminal PC columns and timestamps.
Boot claims specialize the inspected initial PC/clock 0/4. Other typed initial
endpoints describe conditional canonical trace/segment scopes. Public jump/branch/
comparison, standalone jump and pooled claims now derive their terminal bound from
this contract; local calculations remain conditional. The unified artifact keeps
its separate local-range proof. No Rust refinement or cryptographic enforcement
is proved, and the uninspected historical source revision is not attributed.

The selected claims retain normal-path/configuration, field and external boundaries.
Checked surplus-worker, bigint-control and ROM-shadow counterexamples must stay
visible at their actual logical scope; no whole-system exploit, circuit fix or
assumed ABI validity follows. Use [Verification status](VERIFICATION_STATUS.md)
for those fixtures and all unresolved coverage, and
[the plan](FORMAL_VERIFICATION_PLAN.md#deferred-milestones) for downstream proofs.
