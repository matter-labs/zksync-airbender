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

## Checked scope boundaries

These fixtures explain restrictions on the current claims. They concern the
imported richer relations and logical matching; they do not establish a
whole-system or cryptographic exploit. Keep their public inputs and scope visible
when reviewing or strengthening a theorem.

| Boundary | Checked fixture and consequence |
| --- | --- |
| Inactive padding | [Inactive ADD/SUB row](Tests/InactiveRow.lean): execute zero admits PC 0→4 and result 123 under the retained local constraints. Padding neutrality needs global state/write obligations; the selected trace model includes active rows. |
| Jump termination | [Noncanonical JAL endpoint](Tests/JumpSailHistory.lean): imported constraints, decoding and native matching admit a field-aliased terminal PC that disagrees with Sail. The public terminal-PC bound remains required; teardown binding is open. |
| Discarded LW | [Sparse-memory load](Tests/DiscardedLoad.lean): an accepted native NOP can fail original Sail's LW-to-x0 access. The unchanged-Sail claim retains `NoDiscardedLoads`; the named Airbender profile uses the pinned PC-only NOP rule. |
| Unissued workers | [Zero-clock G worker](Tests/DelegationZeroInvocation.lean): an active worker matches no caller and changes actual x12 from 0 to 1. Issued-worker uniqueness does not exclude this prefix effect. |
| Bigint controls | [Issued unified calls](Tests/UnifiedDelegation.lean): x12 = 0 admits no opcode; x12 = 65537 admits ADD with a nonzero high limb. Current caller-cycle observations hold, while the pinned reference rejects these control words. Full custom-CSR ABI remains open. |
| Worker ROM | [COPY with ROM pointers](Tests/DelegationROMBoundary.lean): zero native shadows and exactly matched worker values can differ from public ROM bytes. Replacing shadow tokens with public bytes breaks matching; RAM-profile claims retain their stated domain. |

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
not prove that Rust preprocessing or decoder-table contents match the model.

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

[RangeChecks.lean](Airbender/Review/Helpers/Tables/Range.lean) enumerates 16-bit limbs using
Clean's `StaticTable`; membership characterization is kernel checked. Its rows
reconstruct [Rust range setup](../../prover/src/gkr/virtual_polys/range_check.rs),
selected with 16 bits in [the prover](../../prover/src/gkr/prover/mod.rs).
The 19-bit timestamp table and worker controller/XOR/operation tables have the
same unproved setup-generator correspondence. Exact extracted rows, table identity,
query binding and padding remain deferred provenance work.

`Accepted` checks imported equations/lookups and logical native state/memory
permutations. Decoder membership and caller/request matching are likewise logical
conditions. [Caller request windows](Airbender/Review/Trace/Delegation/RequestHashWindows.lean)
reuse these checks at aligned instruction cuts after clock two. Exact worker/caller
multiplicity, slots and full CSR families are derived; zero-clock worker effects
stay in the actual prefix. Standalone hash-window claims retain explicit worker-only
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
including zero-clock effects, stay in the actual prefix. Worker boundaries, controls
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
preparation and cuts explicit; shared extended-round regions still require their
existing shape and global coverage. General protocol validity, invalid-call ABI
and whole caller retirement remain open. Both invalid bigint controls still satisfy
the program-derived request/schedule claim.
[Control preparation](Airbender/Review/Helpers/UnifiedReduced/ControlPreparation.lean)
uses a public ordinary ADDI-from-x0/LUI registry and a worker-free final preparation
cycle. The registry may be uniform, contain different literals/registers, or admit
arithmetic, LW/SW, bitwise/shifts, REV8 and supported TRIADD/XORROT along a straight
path with callers. The sequential profile is stated on original public instruction
forms, not assumed native selector bits. Jumps, branches and wraparound comparisons
remain outside that linear PC/clock profile. Preparation transports actual memory;
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
[Caller cycles](Airbender/Review/Trace/UnifiedReduced/CallerCycles.lean) now bind original
public fetch, the full-CSR matched worker family, existing local operation references,
all actual worker observations and Sail PC retirement at the same boundaries.
The public physical/code domain, positive machine start and existing worker ABI
remain explicit; prepared extended-round cycles derive their masks. This establishes
cycle observations and PC retirement, with full custom-CSR ABI and whole mixed
execution still separate. Both issued bigint control gaps remain admitted, and
surplus zero-clock effects remain in the shared prefix.
Native columns retain full address/time/value limbs, including readonly
clock refreshes. Bounds, latest-write reads and Clean online-consistent histories
are derived from those relations and public initialization. Retiming introduces
initialization writes and preserves addresses/values; it does not prove cryptographic
permutation or lookup enforcement. Prover/verifier refinement and protocol soundness
are separate obligations.

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
worker ROM transport retains the gap recorded in the status table.

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

The selected claims retain normal-path/configuration, field and terminal boundaries.
Checked surplus-worker, bigint-control and ROM-shadow counterexamples must stay
visible at their actual logical scope; no whole-system exploit, circuit fix or
assumed ABI validity follows. Use [Verification status](VERIFICATION_STATUS.md)
for those fixtures and all unresolved coverage, and
[the plan](FORMAL_VERIFICATION_PLAN.md#deferred-milestones) for downstream proofs.
