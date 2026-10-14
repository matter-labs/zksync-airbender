# Findings: assumptions and circuit bindings

Review date: 13 October 2026. Snapshot: `59a493173a85441da542155cb825488f43904b1e`.

This document records places where a checked theorem can remain true while a
broader circuit or execution claim fails. The pass examined the input/interface
declarations across `Review/Circuits`, `Review/Helpers` and `Review/Trace`, then
followed the significant conditions into their stronger claims and regressions.
It screened 224 Review modules and inspected 105 named input/interface declarations
in 83 files, plus acceptance, profile and conclusion definitions.

The audit-only pass at the snapshot above changed no Lean, Rust, artifact or
dependency files. The counterexamples below
already exist in the development; this pass did not discover a new counterexample.
An **accepted counterexample** establishes a gap at the exact relation tested.
An **unresolved binding** identifies a condition not yet connected to general
acceptance. A **profile difference** is intentional semantic scope. These labels
are not interchangeable with a full verifier or cryptographic exploit.

## Implementation update: issued round coverage and wrapped preparation

Update verified: 14 October 2026. Round coverage checkpoint: `9d9cf76b7`.
The current sources also include the comparison-preparation and modular
coverage updates below.

`ProgramCallerRegion` states public code addresses in native PC/clock coordinates:
ordinary entries lie outside a selected interval and its CSR entries identify the
full worker family. Sequential public decoding and accepted state/request matching
derive caller participation, equal machine/worker counts, unique slots and family.
`ProgramProtocolWindowInputs` uses public reference duration to derive selected
span counts, reusing all three complete references at continuous actual states.

`ProgramRoundRegionInputs` now also replaces the local extended-round worker shape
with public CSR regions, LUI preparation, ordered aligned cuts and at most forty
ticks. `Caller.program_round_region_soundness` derives selected family, the
ten-position bound and exact duration from the native count. The stronger sequence
entry consumes `ProgramPreparedProtocolInputs`; conversion derives every old local
scope before raw matching/LUI preparation proves masks and Sail transport begins.
`ProtocolContextInputs` shares the unchanged public memory/program/table context
with the legacy interface. No selected controller-worker family, length bound or
duration proportional to that list is supplied by the stronger entry.

`ProgramRoundCallerCoverage` now places public decoded round CSR addresses in
these prepared regions. Native PC/clock matching locates actual callers, and the
full CSR/request token identifies each actual live round worker in its region.
`RoundWorkerCoverage` proves the converse too: actual region membership is
equivalent to live invocation. No actual worker coverage or nonzero-invocation
premise is supplied by this coverage result.

`Caller.program_round_live_masks_soundness` combines that derived membership with
public LUI preparation and raw regional matching to derive exclusive masks for
every issued round worker. The local raw-mask helper now uses only
`ProtocolContextInputs` and its region, without global worker coverage.

`Caller.program_round_global_coverage_boundary_soundness` proves that full round
worker coverage is equivalent to absence of zero-clock extended-round workers
within this public sequential/controller profile. Global mask-dependent transport
still retains full coverage; actual exclusion or supported masks for unissued
round workers remain unproved. This is a boundary theorem, not a new accepted
unissued extended-round counterexample. Other zero-clock workers remain in actual
history. Unrestricted protocols and whole caller retirement remain open; earlier
literal/arithmetic/sequential and regional entry points stay available.

Empty public LUI regions derive the old local scope and retain the actual clock-six
preparation token. A public round CSR requires a nonempty covering interval, and
the public coverage result admits the actual unissued G worker. Wrong flags/family,
oversized/reversed/unaligned cuts and two round bits are rejected; the new two-bit
test uses public code/preparation and a live target without whole-pool coverage
or a supplied mask. The stronger context still admits the unissued G worker;
the existing continuous-prefix test now uses its derived context and retains the
actual x12 = 0→1 effect. COPY→ADDI and both accepted bigint controls remain checked.
Surplus workers, bigint invalid controls, worker ROM and discarded-load findings
remain open. F01 is resolved conditionally under the canonical verifier-boundary
binding described below; all original accepted counterexamples are preserved. This audit is tracked with
the verification sources and updated as the reviewed boundaries change.

The separate aligned `WrappedSequentialProgram` now admits the four original
comparisons before the final public ADDI-from-x0/LUI literal. Accepted constraints
derive native comparison cleanup/carry values; native state/clock matching derives
modular RV32 program addresses, including comparison wraparound. Modeled setup
and `4194304 ≤ p` remain explicit. The
[SLTIU→ADDI regression](Tests/UnifiedComparison.lean) starts at `0xfffffffc`,
resets at address zero and derives actual x12 = 65537→1→0 in one continuous
initialized history with reversed native rows. The reset consumes the comparison's
clock-six token and writes at clock ten. Wrong literals, fabricated reads and
misaligned public code are rejected. These are preparation/transport claims;
prefix and whole caller retirement remain separate. Selected caller/controller
regions and global public round-CSR occurrence coverage now also use modular
addresses. Jumps/branches and nonliteral preparation remain open.

`WrappedProgramCallerRegion` now states ordinary-code exclusion and the full CSR
family at modular addresses for every clock in a selected interval. These
policies use the supplied native initial PC/clock, as in the linear entry. Public
decoding and native state/clock matching derive caller participation, worker
family/count and unique native request slots without a no-wrap or PC-injectivity
premise. Modular local controller regions use public LUI preparation and at most
forty ticks to derive family/count/duration and the ten-position bound. The new
prepared sequence entry reuses all three complete references at the same actual
states, with public cuts/preparation/reference duration and global round-worker
coverage still explicit. No unissued-round mask/exclusion result is added.
The [wrap regression](Tests/UnifiedComparison.lean) admits the empty cut at PC zero
and rejects selecting the ordinary ADDI there. The
[COPY regression](Tests/UnifiedDelegation.lean) checks nonempty caller/worker binding,
wrong-family and ordinary-code rejection, while both bigint-control gaps remain
accepted. The [unissued G-prefix regression](Tests/DelegationZeroInvocation.lean)
now uses the modular-context conversion and retains its actual x12 = 0→1 effect.

`WrappedProgramRoundCallerCoverage` now quantifies every aligned native clock
between the supplied endpoints at which a public decoded round CSR equals the
modular program address. Strict clock increments and accepted state matching
derive each actual caller's clock interval without a row-order assumption.
Modular address matching and full-width request matching then prove membership in
a prepared region exactly for live round workers. Public LUI preparation and raw
regional matching derive all issued round masks without assuming full worker
coverage. Full coverage remains equivalent to absence of zero-clock round workers;
this exposes the remaining binding rather than assuming nonzero invocations.
Public code/configuration, native endpoints, modeled setup and logical matching
remain explicit. A public code-policy fixture repeats a round CSR address after
2^32 ticks and rejects covering only either occurrence; it makes no accepted-trace
claim. The actual comparison wrap derives native clock bounds. Empty prepared
cuts, rejection of simultaneous issued round bits, both bigint gaps and the actual
unissued G-prefix effect remain covered by the regression suite.

All 116 concrete test modules and 143 importer guards pass. The full
2,074-root axiom audit has 64 axiom-free roots and only the three standard
Lean axioms. Review checks pass for all 100 public theorem roots, 156 declaration
names and 657 guide links/anchors, with no handwritten project diagnostics.

## Review priorities

| ID | Finding | Evidence/status | Condition or weaker claim that limits coverage |
| --- | --- | --- | --- |
| F01 | Jump terminal PC can be noncanonical locally | Resolved in the logical model under explicit total-verifier boundary binding; original counterexample retained | Canonical u32 contribution closure, cryptographic enforcement and Rust/artifact correspondence remain external |
| F02 | Issued bigint controls violate the reference ABI | Accepted counterexamples for x12 = 0 and 65537 | Selected-operation effects and caller-cycle observations do not validate the full CSR |
| F03 | An active worker can run without a caller | Accepted zero-clock worker with an actual state change | Matching covers live requests; some prepared spans require an empty worker prefix |
| F04 | Worker ROM shadows can disagree with public bytes | Accepted COPY/request counterexample | Physical seed images and tracked-RAM profiles exclude the problematic general native case |
| F05 | Execute-zero does not imply inert padding | Accepted local row counterexample | `Accepted.active` and `RequestChecks.workerActive` select participating rows |
| F06 | Discarded LW differs from original Sail | Accepted native NOP with no original Sail execution | `NoDiscardedLoads`, or the named Airbender NOP profile |
| F07 | Standalone worker claims retain control/participation conditions | Unresolved general binding; discharged in specified stronger scopes | `rounds`, `RoundMask`, `keccakActive` |
| F08 | Complete hash claims retain protocol shape and first-span restrictions | Public-program binding derives selected span/controller shape and all issued round coverage/masks; full coverage exposes the zero-clock extended-round boundary | Mode/duration/preparation, public code profile, controller extents/full coverage and legacy prefix conditions |
| F09 | Decoder/setup models need an implementation binding | Unresolved provenance/structural correspondence | Modeled table equality and logical decoder membership |
| F10 | Caller-cycle effects are weaker than full custom instruction execution | Missing composition/semantic connection | Current fetch, selected worker effects and PC retirement do not execute the full CSR reference |

Review F01's external correspondence and F02–F04 first. F05 and F06 establish why current
participation/profile restrictions matter. F07–F10 identify assumptions or narrower
conclusions that must not silently become claims of unrestricted acceptance.

## F01 — Terminal PC resolved under the explicit total-verifier boundary

**Status.** Resolved in the logical model under the explicit total-verifier boundary
binding. The local circuit counterexample remains valid, but is excluded by the
verifier's canonical u32-to-two-limb terminal contribution. Cryptographic
enforcement and Rust/artifact correspondence remain external.

**Evidence.** [JumpSailHistory](Tests/JumpSailHistory.lean)
proves `noncanonical_native_accepted` and `noncanonical_terminal_mismatch`.
The row satisfies imported equations and timestamp queries, original public JAL
decoding, state/memory matching, clock boundaries and actual public initialization.
Its terminal high PC limb is the field encoding of `-1`, outside the 16-bit range;
the interpreted terminal word disagrees with Sail's sign-extended JAL target.
Register-word bounds still hold: this is specifically an endpoint failure.

**Where the bad case is excluded.**
[JumpBranchSlt.TraceInputs](Airbender/Review/Circuits/JumpBranchSlt/Model.lean),
[Standalone jump inputs](Airbender/Review/Helpers/Context/Registries/JumpBranchSltInputs.lean)
and both
[pooled physical/native-boot inputs](Airbender/Review/Helpers/Context/PooledBoundary.lean)
now consume `verifierBoundary` closure in place of their former direct
`terminalPC` / `terminalCanonical` range fields. The
[public contract](Airbender/Review/Helpers/Context/VerifierBoundary/Model.lean)
keeps typed statement PCs/timestamps and the logical permutation over the actual
imported row starts/ends explicit. Boot inputs fix initial PC/clock to 0/4;
general canonical initial endpoints describe conditional trace/segment scopes.

**Checked connection.** The encoding reuses `PCState.boundary` and preserves the
full 32-bit PC in bounded low/high field limbs. Comparing accepted state matching
against the canonical closure and canceling their identical start-list proves
equality of the entire original terminal tuple with the typed contribution.
[`terminal_state_soundness` and `terminal_bound_soundness`](Airbender/Review/Helpers/Context/VerifierBoundary/Theorems.lean)
derive the raw endpoint and its bounds, without truncating/repacking a malformed
pair or supplying its range. Existing intermediate-PC range proofs consume this
derived bound. Purely local calculation lemmas remain conditional.

The [original witness](Tests/JumpSailHistory.lean) still satisfies its original
acceptance relation; `noncanonical_verifier_boundary_rejected` proves that no new
canonical closure can admit it. The [valid JALR fixture](Tests/JalrTrace.lean)
proves `canonical_verifier_boundary` and instantiates the public standalone and
per-circuit soundness claims. Existing branch/comparison and pooled fixtures also
inhabit their replacement contracts.

**Inspected implementation and remaining trust.** The source revision actually
inspected is `0dc0a631349462700825f326516d36200be30edc`. The
[source inventory](Airbender/Review/Helpers/Context/VerifierBoundary/README.md#inspected-source-and-external-obligations)
records the unrolled and unified total-statement paths, u32 mask/shift encoder,
separate PC-space coefficients/tuples and initial 0/4 constants, with exact blobs.
The supplied historical revision was not retrievable and is not claimed as
inspected. Logical PC-space matching and its Rust/artifact correspondence remain
external; sampled product equality is not deterministic multiset equality.

**Scope distinction.** The separate unified artifact's
[execution_soundness](Airbender/Review/Trace/UnifiedReduced/Theorems.lean)
does not assume terminal-PC normalization. Do not generalize the standalone/pooled
jump counterexample to that theorem. The earlier user-reported circuit bug is
historical context; this investigation establishes conditional logical exclusion,
not a circuit fix, a proved Rust correspondence or an unconditional verifier proof.

## F02 — Valid bigint operation observations do not establish valid calls

**Evidence.** [UnifiedDelegation](Tests/UnifiedDelegation.lean)
proves `issued_bigint_without_opcode`, `issued_bigint_high_control` and their
execution/current-fetch consequences. Both cases are live, original-decoded calls
in initialized, exactly matched joint histories. x12 = 0 selects no opcode;
x12 = 65537 selects ADD while retaining a nonzero high control limb.
`issued_bigint_abi_gap_caller_cycles` shows that even current caller-cycle
observations admit both cases. `issued_bigint_pointer_abi` establishes canonical,
aligned, distinct RAM pointers for these same witnesses: fixing the pointer ABI
does not fix control validity. [BigintAbi](Tests/BigintAbi.lean)
also checks the smaller local witnesses.

**Reference discrepancy.** The checkout's
[bigint_impl](../../riscv_transpiler/src/vm/delegations/bigint.rs) asserts an eight-bit
control word and exactly one opcode after removing the carry bit. It rejects
both controls. These Rust assertions are source evidence, not a proved equivalence
between the VM and Lean.

**Why current theorems still pass.**
[Native.operation_execution](Airbender/Review/Trace/Workers/Bigint/Theorems.lean)
proves the existing selected arithmetic effects. It deliberately does not assume a
valid opcode to erase the gap. An implication for each selected operation can hold
when none is selected; current caller cycles likewise do not run the full custom CSR.

**Closure needed.** Bind all control bits, opcode cardinality and invalid-call
behavior to general native acceptance and the full call reference. An assumed
`validControl` premise would only narrow the theorem and leave these witnesses open.

## F03 — Zero-clock fulfillment matching permits an unissued state change

**Evidence.** [DelegationZeroInvocation](Tests/DelegationZeroInvocation.lean)
proves `active_zero_invocation`, `no_caller_virtual_matching`,
`mixed_unissued_worker_accepted` and `mixed_unissued_control_update`. An active G
worker satisfies imported constraints, modeled tables and initialized architectural
matching, yet matches no caller and changes actual Sail x12 from 0 to 1.

**Mechanism.** In [Requests.Matching](Airbender/Review/Helpers/Delegation/Requests.lean),
a zero-clock worker's issued and empty virtual tokens coincide and cancel. Request
binding/unique scheduling is established for live requests, not an exclusion of
all additional workers. The [unified RequestBinding](Airbender/Review/Helpers/UnifiedReduced/RequestTrace.lean)
explicitly classifies zero-clock workers as unissued rather than rejecting them.
Moving an effect before a selected window retains the effect;
`zero_worker_retained_before_request_window` checks this directly.

**Current preparation scope.**
[ControlPreparation.prefixScope](Airbender/Review/Helpers/UnifiedReduced/ControlPreparation.lean)
now excludes worker writes only from the final preparation cycle. Earlier workers,
including zero-clock workers, remain in the actual history.
`control_preparation_after_unissued_worker` checks a retained unissued update followed
by actual ADDI preparation. The original extended-round first-span scope still requires its separate
empty prefix; the regional entry uses explicit controller coverage and retains
unissued G-prefix effects. Neither condition is a general fulfillment-exclusion proof. The new program-derived
request window retains its `unissued` classification and prefix placement too;
no nonzero-invocation premise is introduced.

**Closure needed.** Show that the actual full acceptance argument rejects unissued
active workers, or gives them a justified inert meaning. Issued-worker uniqueness
alone is insufficient. Do not close the finding by assuming nonzero invocation.

## F04 — A valid COPY mode does not bind native worker ROM to public bytes

**Evidence.** [DelegationROMBoundary](Tests/DelegationROMBoundary.lean)
proves `native_caller_worker_matching`, `public_request_binding`,
`supported_copy_mode`, `worker_accesses_rom` and `public_rom_word_nonzero`.
The decoded caller and COPY worker match with native zero-ROM shadows while the
actual public ROM word is nonzero. `machine_only_rom_lift_breaks_matching` proves
that lifting seed/terminal tokens to public bytes while retaining worker values
breaks the architecture's exact matching.

**Where current claims stop.**
[MixedMemoryInputs.initialization](Airbender/Review/Helpers/UnifiedReduced/MixedMemory.lean)
uses a physical Sail seed image; it does not automatically transport a native
zero-shadow worker pool. The actual VM
[bigint_call](../../riscv_transpiler/src/vm/delegations/bigint.rs) rejects ROM pointers.
The [pointer ABI](Airbender/Review/Circuits/Bigint/PointerABI.lean)
is derived in shared-history claims under a tracked-RAM domain. Its RAM condition
is not established for arbitrary native acceptance, and valid controls alone do
not exclude the COPY fixture.

**Closure needed.** Bind the native worker ports to the RAM-only call ABI or model
the actual invalid-call behavior, then prove public-byte transport for the admitted
scope. Ordinary machine ROM transport cannot simply be reused with worker values
left untouched. The physical-image/RAM-profile claims remain valid.

## F05 — Participating-row models leave global padding obligations open

**Evidence.** [InactiveRow](Tests/InactiveRow.lean)
checks all retained local ADD/SUB constraints for execute = 0, initial PC = 0,
final PC = 4 and destination low limb = 123. Execute-zero alone proves neither
PC stuttering nor an inert observable result.

**Where the case is excluded.**
[Accepted.active](Airbender/Review/Helpers/Context/Model.lean)
requires every included machine row to execute. Pooled and unified request checks
also require included workers to be active. These are participation predicates
for the modeled lists; the audit found no whole-layout theorem that derives the
irrelevance of every excluded row's state, write or lookup contribution.

**Closure needed.** Bind list participation to the actual global argument and
prove all omitted padding contributions neutral. The fixture is local: it does
not establish that an inactive row can alter a fully accepted machine trace.

## F06 — The discarded-LW restriction protects a real semantic difference

**Evidence.** [DiscardedLoad](Tests/DiscardedLoad.lean)
proves `native_accepts_discarded_load`, `original_discarded_load_error`,
`no_native_terminal_execution` and `profile_terminal_execution`. An accepted native
NOP has no original Sail execution because the discarded load still performs a
failing memory access. The explicit Airbender profile admits the PC-only NOP.

**Where it is excluded or reinterpreted.**
[NoDiscardedLoads and profileClause](Airbender/Review/Helpers/Decoder/Instruction.lean)
state this distinction. The unchanged-Sail
[ADD/SUB trace theorem](Airbender/Review/Trace/Families/AddSub/Theorems.lean)
requires the restriction; pooled and unified standard execution inputs retain it.

**Closure needed.** Decide which ISA profile is the intended claim and preserve
that choice through fetch and retirement. This is a documented project-profile
difference, not evidence that the declared Airbender-profile theorem is wrong.
Removing the restriction from an original-Sail claim would require new semantics
or proof inputs.

## F07 — Round selection and worker participation remain inputs in weaker scopes

**Condition.** [OperationInputs](Airbender/Review/Helpers/Delegation/Operations.lean)
requires an exclusive `RoundMask` for every extended-BLAKE row and execute = 1
for every Keccak row. The extended-round
[local interfaces](Airbender/Review/Circuits/Blake2Round/Row.lean)
and [Memory interface](Airbender/Review/Circuits/Blake2Round/Memory.lean)
retain the round-mask premise too. Individual boolean bit checks are not the
exclusive-mask ABI specified in [Control.RoundMask](Airbender/Review/Circuits/Blake2Round/Control.lean).

**What is already discharged.** The initialized full
[compression/boundary/window claims](Airbender/Review/Trace/Workers/Blake2Round/Theorems.lean)
derive masks from their public control/protocol inputs. Prepared unified round
claims derive them from the actual LUI preparation token and matching. The regional
entry derives masks separately inside each caller window before Sail transport;
earlier workers remain in the prefix and every extended-round worker must be
covered by a prepared controller region. Public decoded round CSR coverage now
derives region membership and masks for every issued round worker without
whole-pool coverage. Raw regional mask derivation uses the public memory context
and the derived local scope. Unissued extended-round mask behavior remains outside
this issued result.
[Blake2RoundCall](Tests/Blake2RoundCall.lean)
checks rejection of a wrong round bit and changed flags under the corresponding
control word. Request checks separately provide participating worker activity.

**Closure needed.** Trace every use of the weaker interfaces to one of those
derived facts or to an explicit supported protocol. General arbitrary-control
and inactive-worker behavior remain outside these stronger scopes. No new
malformed-round counterexample is claimed here.

## F08 — Hash interfaces include restrictions on the witness and its schedule

**Condition.** [HashSpan.Protocol](Airbender/Review/Helpers/Delegation/SpanABI.lean)
assumes a homogeneous worker family, initial control/mode and exact call count.
Worker windows add [G prefix completeness](Airbender/Review/Trace/Workers/Blake2G/Windows.lean),
[extended-BLAKE empty prefix and ten-row cap](Airbender/Review/Trace/Workers/Blake2Round/Windows.lean),
or [Keccak empty prefix](Airbender/Review/Trace/Workers/Keccak/Windows.lean).
Prepared mixed scopes add a uniform/straight literal or sequential ordinary/custom program profile,
a worker-free final preparation cycle, selected-span family/count restrictions and
duration equalities. Regional extended-BLAKE composition also requires explicit
controller coverage and a ten-position bound inside each region.
G/Keccak now constrain the family only inside their selected window; other
bigint/G/Keccak workers stay in joint history outside it. Extended-round workers
remain outside that mask-free scope. This adds no bigint opcode-validity condition.
Different literals/registers may appear along the straight path: native PC/clock
matching derives the instruction at each cut. This removes the one-literal registry
restriction without admitting branches or arbitrary final preparations. The
arithmetic extension admits ADD/SUB/ADDI/LUI/AUIPC with arbitrary operands before
the final specified literal. The sequential extension also admits LW/SW, bitwise/
shifts, REV8 and supported TRIADD/XORROT. Its accepted aliased TRIADD→ADDI reset
derives 65537→196611→0 with the same retained clocks and rejects a fabricated read.
Jumps, branches and wraparound comparisons remain outside the linear PC/clock
profile. A separate aligned comparison profile now derives modular RV32 addresses
from the same accepted constraints/matching, with modeled setup and minimum
modulus 4194304 explicit. It derives actual SLTIU→ADDI states 65537→1→0 through
PC `0xfffffffc`→zero, retains clocks six/ten and rejects fabricated reads and
wrong literals. Selected caller/controller regions now support the modular
registry too; global public round-CSR coverage remains linear. Jumps, branches
and nonliteral final preparation remain open. These are preparation/memory effects,
not full-prefix retirement. Public
decoded forms and accepted PC constraints derive the preparation address; native selector bits or output values are not
supplied. The accepted aliased ADD→ADDI reset derives actual 65537→131074→0
through one continuous history with clocks six/ten and rejects a fabricated read. Two preparation
cuts also share one intervening native history with both controls derived. Two
complete prepared G/Keccak references now use one continuous chain, with the actual
first finish initializing the gap and second span; their intermediate states,
native tokens, clocks and reference results are derived. This still uses the public
literal registry, ordered aligned cuts and explicit span mode/count/duration.
Arbitrary nonempty ordered lists now share the same continuous execution within
this public prepared G/Keccak scope. The broader prepared protocol entry now
adds extended-BLAKE restarts: raw matching derives masks within each LUI-prepared
caller region with a local ten-position cap. Explicit coverage of all extended-round
workers permits complete lists of all three references in the same continuous
execution. It no longer requires a global empty prefix, homogeneous pool or ten-row
pool bound. Coverage, local family/count/duration and public preparations still
constrain witness shape. Broader preparation/protocol binding and whole ISA
retirement remain open. G/Keccak
allow earlier workers; the original first-span extended-BLAKE entry retains an empty
worker prefix while the newer regional entry uses explicit controller coverage; see
[ControlPreparation](Airbender/Review/Helpers/UnifiedReduced/ControlPreparation.lean),
[PreparedHashWindowInputs](Airbender/Review/Trace/UnifiedReduced/PreparedHashWindows.lean)
and [PreparedRoundInputs](Airbender/Review/Trace/UnifiedReduced/PreparedRoundWindows.lean).

These conditions are not all just public initial data: lengths, family membership,
prefix emptiness and duration constrain the accepted worker/machine collections.
Intermediate values, actual cut states and schedules *within that scope* are proved.
The theorem does not derive that every generally accepted execution has that shape.

**Evidence for the limit.** Both
[extended-BLAKE completion](Tests/Blake2RoundCall.lean)
and [Keccak completion](Tests/KeccakSchedule.lean)
have checked `completion_does_not_restart` results. Treating first-span theorems
as automatically repeating would be incorrect.

**New public-program connection.**
[ProgramCallerRegion](Airbender/Review/Helpers/UnifiedReduced/WindowSchedule.lean)
constrains public code addresses and CSR families. Sequential public decoding and
accepted native PC/clock matching derive that each selected instruction is a
caller; exact request matching then derives worker family, multiplicity and slots.
[ProgramProtocolWindowInputs](Airbender/Review/Trace/UnifiedReduced/PreparedRoundWindows.lean)
uses public reference duration to derive complete counts. Its sequence entry reaches
all three references at the same actual segment states, without selected worker
family/count premises. `ProgramPreparedProtocolInputs` now also derives local
extended-round shape from public LUI preparation, CSR regions and at most forty
ticks between aligned ordered cuts. Family, the ten-position bound and exact worker
duration follow from native matching; raw matching then derives masks before
transport. `ProgramRoundCallerCoverage` now derives region membership exactly for
live round workers; public preparation and raw matching derive all issued masks
without actual worker coverage or supplied masks. In this public profile, full
coverage is equivalent to absence of zero-clock extended-round workers. That
residual global binding stays explicit for whole-pool transport. No new unissued
extended-round counterexample is established. The public sequential/code/preparation/
cut profile remains explicit. This does not establish every accepted execution has that
shape, or validate bigint controls or unissued-worker behavior.

The modular selected-region entry now derives the same window and local controller
shape through aligned sequential/comparison code, modeled setup and minimum
modulus 4194304. `WrappedProgramPreparedProtocolInputs` and
`WrappedProgramProtocolWindowInputs` connect those derived scopes to the existing
complete-reference sequence. Public policies quantify addresses at every clock
in each interval, including repeated RV32 addresses; native schedules and worker
counts are conclusions. Global round-worker coverage remains a witness-shape
boundary, and the public global round-CSR coverage/mask result remains linear.
The unissued-round question, branches/jumps, nonliteral final preparation and
whole caller retirement remain open.

**Closure needed.** Bind complete call protocols to actual caller preparation,
chaining and segmentation in the unrestricted execution claim. Until then,
preserve these restrictions beside any use of a complete hash theorem.

## F09 — Modeled tables and decoder membership can hide implementation mismatches

**Condition.** [PooledHistoryInputs](Airbender/Review/Helpers/Context/Interfaces.lean)
fixes modeled word/subword tables to the public image.
[OperationInputs.tables](Airbender/Review/Helpers/Delegation/Operations.lean)
fixes worker setup to modeled range/operation/XOR/controller tables.
[PooledProgram](Airbender/Review/Helpers/Decoder/PooledProgram.lean)
and request checks assume logical decoder-query membership in tables constructed
from original public Sail decoding.

The lookup behavior and successful source decoding are checked. Correspondence
of those exact modeled rows, native metadata projections and query bindings with
the Rust setup/preprocessor is still unproved; see
[the trust boundary](TRUST_AND_REVIEW.md#modeled-tables-and-logical-arguments).
A proof against the intended table can miss a bug in the actual table or its use.
This is a structural/provenance issue even before cryptography.

**Closure needed.** Review the actual setup identities, row contents, unsupported
decoder entries, selector/immediate/register projection and query placement, then
establish the implementation binding. No concrete decoder/setup discrepancy was
demonstrated in this pass.

## F10 — Caller-cycle observations do not run the full custom CSR reference

**Conclusion boundary.** [CallerCycle and CallerCycleEffects](Airbender/Review/Trace/UnifiedReduced/CallerCycles.lean)
connect actual history states, public fetch, a matched worker's selected effects,
port reads/writes, terminal cells and Sail PC ticking. They do not invoke the full
custom CSR operation with its control, pointer and invalid-call behavior.
[Mixed.execution_soundness](Airbender/Review/Trace/UnifiedReduced/Theorems.lean)
covers standard plus TRIADD/XORROT retirement; delegation callers are outside
that registry.

**Evidence.** F02's invalid bigint calls satisfy the caller-cycle theorem itself.
Thus strengthening fetch/state transport has not silently established the missing
ABI. A complete selected hash span is likewise an architectural-effect result,
not by itself a whole mixed caller-retirement theorem.

**Closure needed.** Compose ordinary/custom and caller steps with the complete
project reference, preserving its invalid-call behavior, all native effects and
terminal PC/cell agreement. Do not infer this result from the current theorem names.

## Remaining boundary register

These are additional assumptions to review for applicability, not additional
demonstrated bugs:

| Boundary | Exact premise or missing connection | Review consequence |
| --- | --- | --- |
| Initialization/teardown | [NativeInputs](Airbender/Review/Helpers/Context/Boundary.lean), [InitialProfile](Airbender/Review/Helpers/Memory/Initialization.lean), boot seed/PC and distinct tracked cells are public inputs. The [retained init/teardown artifact](../../cs/compiled_circuits/inits_and_teardowns_layout_no_caches_gkr.json) has zero degree-1/2 constraints, generic lookups and 16/19-bit range-query expressions. | Public-image soundness does not prove the native initialization/teardown circuit establishes that image; richer retained proof input remains needed for that circuit. F01 is now resolved conditionally through canonical verifier-boundary closure, independently of this missing local circuit proof. |
| Memory/fetch configuration | [FlatMemoryConfiguration and OrdinaryWordAddress](Airbender/Review/Helpers/Memory/Platform.lean) select Machine mode, the direct memory path, PMP disabled, permissive PMA and no modeled special-memory windows; code bounds/alignment and landing-pad restrictions are explicit in execution inputs. | These are supported public-profile conditions. Full faults, interrupts, MMIO, other privilege/protection configurations and the full fetch driver are not covered. |
| Independent external input | [ExternalStream.Ports](Airbender/Review/Helpers/Core/ExternalStream.lean) binds responses to an independently supplied stream. | Exact consumption and execution do not authenticate an oracle or establish a particular externally intended stream. |
| Logical matching | [Accepted](Airbender/Review/Helpers/Context/Model.lean), worker matching and request matching are exact permutations of full tokens. | This is the intended premise for the noncryptographic memory-history result. Product/compression equality must not be silently substituted for it; actual global participation and token construction still need their implementation binding. |
| Artifact/reference fidelity | [Import/generation boundary](TRUST_AND_REVIEW.md#import-and-generation-fidelity): richer no-cache import, original Sail generation and project-reference revision applicability; compiled/cached correspondence is not proved. | Do not transfer these claims to a compiled/cached circuit or a different reference revision without the corresponding implication/binding. |
| Fields and coefficients | The public claims retain prime-field minima and serialized inverse equalities; bigint's integrated operation proof is BabyBear-specific. | These are arithmetic compatibility conditions, not proof defects. A generic field theorem does not establish the actual Proth120 artifact import. |

## Assumptions that stronger claims already derive

The audit did not find a desired read, final arithmetic result or full memory
history supplied as an independent premise in the six ordinary-family integrated
models. [ADD/SUB's model](Airbender/Review/Circuits/AddSub/Model.lean)
is representative: its mapping identifies native observables and the selected
row's actual prefix state, while initialization and modeled tables are separate.
F01 is the important additional endpoint exception in the jump/pooled scope.

- [Complete memory paths](Airbender/Proofs/Trace/MemoryPaths.lean),
  [latest reads](Airbender/Proofs/Trace/LatestReads.lean)
  and [Clean-consistent history](Airbender/Proofs/Trace/MemoryHistory.lean)
  are conclusions of initialized full-token matching and proved clock laws.
- Actual reads, ordinary operand/immediate bounds, decoder preprocessing and row
  order are derived in the connected ordinary scopes.
- Shared worker histories derive pointer/operand bounds and actual transfers;
  the RAM-only public domain in F04 must still stay visible.
- Issued-worker identity, unique invocation clocks and cycle placement are
  derived; the unissued exception in F03 remains.
- Local G bounds, selected-lane/frame facts and exclusive extended-round masks
  have stronger history/protocol connections. Their presence in a weaker local
  calculation interface is not alone evidence of a circuit bug.

For each remaining premise, ask: **is this genuinely public input/profile data,
a logical global-argument condition, a fact proved by a stronger claim, or a
witness/output restriction still awaiting a binding?** F01 shows why the last
category must never be described simply as public context.

## Validation and next review

The scoped Lean build passed for `Tests.JumpSailHistory`, `Tests.InactiveRow`,
`Tests.DelegationZeroInvocation`, `Tests.UnifiedDelegation`,
`Tests.DelegationROMBoundary`, `Tests.DiscardedLoad`, `Tests.BigintAbi`,
`Tests.Blake2RoundCall`, `Tests.KeccakSchedule` and `Tests.KeccakController`,
with no handwritten Airbender/Tests diagnostics. This reused the current checked
sources; it did not add new proofs. The snapshot's full audit/review checkpoint
also passed before this documentation-only pass.

Review F01's explicit canonical boundary contract and the remaining Rust/artifact
and cryptographic correspondence. For unresolved F02–F04, review the actual request
and worker acceptance argument first; then review F07/F08's witness-shape
restrictions and F09's concrete setup binding. Closing a remaining finding should
supply that connection or explicitly revise the claimed scope; adding the missing
property as an assumption is not closure.
