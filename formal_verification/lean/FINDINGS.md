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
coverage still explicit. General supported-mask coverage and unissued-round
exclusion remain unproved.
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

The new [unissued worker entry](Airbender/Review/Trace/UnifiedReduced/UnissuedWorkers.lean)
derives every unissued read as a full public initialization token. Native worker
writes start at clock two; the mandatory first machine port, strict native memory
order and alignment derive machine clocks at least four. Architectural matching
then excludes every produced token as the source of an unissued read. Values,
canonical limbs and raw zero timestamps come from public initialization, without
operation masks or an added initial-clock floor. For an unissued extended-round
worker, the actual initial x12 high limb characterizes the exclusive-mask ABI
exactly: it equals `flags + 8 * 2^round`, for flags below eight. Both directions
follow from native control assertions and Boolean bits. A publicly zero x12 seed
implies no exclusive mask; multibit encodings likewise fail that ABI. These are
conditional mask consequences, without an accepted unissued-round witness,
worker-exclusion theorem or inertness claim. The accepted G fixture and its actual
0→1 prefix effect remain admitted; tests bind its reads in the worker-only history
and the history containing a later ADDI reset.

Initialized architectural matching now also gives numeric and raw invocation
clock uniqueness for every worker occurrence, including zero. The new
`WorkerInvocationUniqueness` projects each family's actual fixed x10 port, whose
native write offset is two, through the existing memory-key uniqueness proof.
The public tracked domain remains distinct. No operation mask, valid bigint
control, nonzero invocation or whole-pool hash coverage is assumed. The unissued
sublist therefore has at most one occurrence, with identical duplicate rows
counted separately. The [zero-clock regression](Tests/DelegationZeroInvocation.lean)
shows that two copies still pass all native/request checks, while initialized
architectural acceptance rejects them. The original single state-changing G
worker attains the bound, both with and without the later ADDI reset. The
[bigint/COPY regressions](Tests/UnifiedDelegation.lean) instantiate the full result
for live COPY and for both invalid bigint controls. This is a bound on surplus,
without a general exclusion or inertness result.

The [all-worker execution entry](Airbender/Review/Trace/UnifiedReduced/Theorems.lean)
now groups the possible unissued worker as the actual first transfer group at
clock three. Strict native memory order and alignment derive machine clocks at
least four. Full invocation uniqueness isolates its ports, and the native write
floor excludes earlier transfers. Consequently its complete call reads the
original public state and produces the actual prefix end; every later transfer
continues from that state to the shared terminal cells. The raw proof adds no
operation mask, valid bigint control or positive-invocation assumption. The closed
BabyBear result retains the existing modeled tables and extended-round masks for
history realization, without claiming unsupported-control execution. The
[zero-clock regression](Tests/DelegationZeroInvocation.lean) now checks actual
x12 = 0→1→0 at the initial, unissued-call finish and final states in one history,
and isolates exactly the native G ports at clock three. Live COPY and both invalid
bigint controls also instantiate all-worker execution. F03 remains an accepted
state-changing counterexample; this derives its actual call boundaries without
excluding it or proving inertness. Whole caller retirement and full CSR ABI remain
open.

Native memory order and alignment now also derive every machine cycle in the
same all-worker execution, without a supplied positive initial clock. The new
[caller-cycle entry](Airbender/Review/Trace/UnifiedReduced/Theorems.lean) uses that
bound to compose actual fetch, matched worker observations and PC retirement.
Existing clock-parameter entries remain available. An empty-machine logical
fixture with public endpoint clock zero still admits the unissued G prefix and
its actual x12 = 0→1 effect; native boot remains clock four. The earlier G→ADDI
regression also derives its actual ordinary cycle in the same history. Both
invalid bigint controls and LW/SW caller fixtures satisfy the stronger entry.
This removes a derived clock condition from inputs while retaining F02/F03 and
the separate full-CSR/whole-retirement boundaries.

The [PC-relative preparation entry](Airbender/Review/Trace/UnifiedReduced/PCRelativePreparation.lean)
now derives an AUIPC-prepared control from public code and its native PC. The
modular sequential/comparison registry and state/clock matching derive the actual
final instruction address, and accepted arithmetic equations derive its RV32 sum
with the decoded U-immediate. Exact prefix matching retains the canonical output
token at cut minus two; initialized history supplies its actual Sail cut read.
No expected output, desired operand or selected native row is supplied. Only the
final cycle is worker-free, retaining earlier issued/unissued effects. Public
setup/tables and the existing extended-round ABI stay explicit. The
[preparation fixtures](Tests/ControlPreparation.lean) check actual x12 values
65537→524292 at PC four and 65537→61444 at PC 65540 with a sum wrapping 2^32,
retain clock-six tokens, distinguish the immediate alone and reject wrong
immediates or fabricated native reads. This is control preparation and memory
transport. Complete G/Keccak integration now uses the source interface below;
general operand-dependent preparation, jumps/branches and whole caller retirement
remain open. F01–F10 stay exposed.

The [computed hash-window source](Airbender/Review/Trace/UnifiedReduced/ComputedHashWindows.lean)
now admits literal or publicly placed AUIPC instructions before complete selected
G/Keccak references and nonempty ordered lists. AUIPC placement is a condition on
decoded code addresses and U-immediates; it supplies no actual control read.
Native constraints/matching derive the selected instruction, canonical entry
token at cut minus two and actual initialized cut value. Existing reference and
sequence composition retains every gap and intermediate state in one history;
legacy literal signatures now use that same proof. Mode/count/duration, selected
family, nonround worker scope, public domain/setup/tables and logical matching
remain explicit. [Preparation fixtures](Tests/ControlPreparation.lean) check actual
G control 128 from AUIPC at PC 128 and Keccak's wrapped zero reset from PC 4096,
starting from 65537 and retaining clock-six tokens. Wrong placement and incomplete
56/649-call windows are rejected. These fixtures check preparation and guards;
complete reference/list claims are arbitrary-witness theorems under their stated
ABI. The [unissued G-prefix preparation](Tests/DelegationZeroInvocation.lean) remains
admitted through the literal source. No ABI finding is hidden or resolved by this
change. The new public modular-region entry derives selected caller rows, exact
request slots, worker family and count for either preparation source before
reusing the same complete-reference and ordered-list composition. It retains
public mode/code/duration, global nonround scope and all initialization/domain/
table/matching boundaries. Native preparation witnesses derive empty-region
counts without a count premise; incomplete durations, cuts past the native
terminal and regions containing ordinary preparation code are rejected. The
unissued G effect remains in the literal entry's prefix.

The [source-aware round regions](Airbender/Review/Trace/UnifiedReduced/ComputedRoundRegions.lean)
now transport the actual round-zero seed from either preparation source into
raw initialized matching and derive exclusive regional masks. Public modular
controller code and aligned cuts covering at most forty ticks derive selected
family/count/duration and the ten-position bound. Global memory transport retains
explicit full round-worker coverage; the local proof supplies no empty prefix,
global ten-row cap, control read or mask. Legacy LUI regional-mask/global-memory
entries keep their contracts and share that proof. The native AUIPC preparation
at PC 524288 derives x12 = 65537→524288, its canonical clock-six token and an
empty regional/global context. Wrong public flags, invalid cuts and simultaneous
round bits are rejected under the regional ABI. The concrete fixtures cover
preparation/empty regions; nonempty masks remain arbitrary accepted-witness
theorems. The [unissued G-prefix effect](Tests/DelegationZeroInvocation.lean)
stays admitted under the source-aware global context. Source-aware public modular
round-CSR occurrence coverage now derives precisely live regional membership and
every issued mask. It covers aligned repeated-address occurrences; full coverage
is equivalent to absence of zero-clock round workers and does not follow from
public CSR coverage alone. Complete G, extended-BLAKE and Keccak reference lists
may now mix literal/AUIPC preparation in one continuously initialized history.
Public modular caller/controller regions derive selected shape; the existing
composition retains every gap and actual cut state. Full round-worker coverage
stays explicit in the complete entry. Legacy coverage/reference/list signatures
remain and share those proofs. The native preparation/empty-region fixtures
inhabit the new public context and reject incomplete reference counts/durations
and cuts past the native terminal; complete references/lists remain general
accepted-witness theorems, without concrete complete native-window fixtures.
Broader operand-dependent preparation, jumps/branches and whole caller retirement
remain open. No demonstrated terminal-PC, bigint, zero-clock, ROM-shadow or
discarded-load finding is hidden by these entries.

The separate [register-dependent ADDI entry](Airbender/Review/Trace/UnifiedReduced/RegisterPreparation.lean)
now derives its actual final row from public modular code and native clocks, its
source state from the initialized prefix and its operand bounds from memory
induction. Native arithmetic derives the RV32 sum using Sail's signed immediate
extension. The actual cycle supplies its cut read and canonical output token at
cut minus two, including source/destination aliases. No operand read, bound,
selector, intermediate state or desired value is supplied. Only the final cycle
is worker-free; earlier issued/unissued effects and the public domain/setup/table/
round-mask boundaries remain. [Native fixtures](Tests/ControlPreparation.lean)
derive 65537→65665 and 65537→65536, retain clock six and reject a wrong immediate
or fabricated source. The [unissued G-prefix fixture](Tests/DelegationZeroInvocation.lean)
derives actual states 0→1→1, preserving the operand update before ADDI. Legacy
literal/AUIPC signatures remain and share arithmetic/output-token helpers. This
is memory preparation. The third hash-reference source now binds consecutive
public literal→ADDI dataflow to protocol entry constants. Raw prefix/suffix
matching, strict clocks and the existing distinct public domain identify the
actual operand with the preceding literal token before Sail transport or any
regional mask derivation. The public equation mentions instruction constants
only. Both final cycles are worker-free; earlier transfers remain. The existing
complete G/extended-BLAKE/Keccak windows and lists admit this source without
changing their domain/setup/table, coverage or logical-matching boundaries.
Native reversed-row fixtures derive 65537→127→128 and 65537→129→128, including
aliases, signed −1 and canonical clock ten; wrong immediates/constants,
fabricated source reads and incomplete references are rejected. A native unissued
G prefix remains in the same initialized history before literal zero and ADDI
128. These are preparation/empty-region fixtures, not concrete complete reference
windows. Other gap instructions, broader operations and full Sail
retirement remain open. All ABI findings remain exposed.


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
incomplete references are rejected. AUIPC fixtures inhabit the root case, and
the native unissued G-prefix fixture remains admitted with its actual update.
All demonstrated ABI findings remain exposed.
These are preparation/guard fixtures; complete references remain general
accepted-witness theorems. Other gap instructions, broader operations and full
Sail retirement remain open.


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
G-prefix effect remains admitted; all demonstrated ABI findings remain exposed.
These are preparation/guard fixtures; complete
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

The current validation totals are recorded in
[Verification status](VERIFICATION_STATUS.md); importer, axiom and review checks
retain the existing regression roots with no handwritten project diagnostics.

## Review priorities

| ID | Finding | Evidence/status | Condition or weaker claim that limits coverage |
| --- | --- | --- | --- |
| F01 | Jump terminal PC can be noncanonical locally | Resolved in the logical model under explicit total-verifier boundary binding; original counterexample retained | Canonical u32 contribution closure, cryptographic enforcement and Rust/artifact correspondence remain external |
| F02 | Issued bigint controls violate the reference ABI | Accepted counterexamples for x12 = 0 and 65537 | Selected-operation effects and caller-cycle observations do not validate the full CSR |
| F03 | An active worker can run without a caller | Accepted zero-clock worker with an actual state change | Distinct initialized matching bounds it to one and derives its actual first-group states; exclusion remains open |
| F04 | Worker ROM shadows can disagree with public bytes | Accepted COPY/request counterexample | Physical seed images and tracked-RAM profiles exclude the problematic general native case |
| F05 | Raw inactive rows need not stutter | Conditionally resolved by the external contribution-mask boundary; no demonstrated implementation bug | Exact whole-layout masked closure derives active acceptance/execution; Rust/GKR/cryptographic enforcement remains external |
| F06 | Discarded LW differs from original Sail | Accepted native NOP with no original Sail execution | `NoDiscardedLoads`, or the named Airbender NOP profile |
| F07 | Standalone worker claims retain control/participation conditions | Unresolved general binding; discharged in specified stronger scopes | `rounds`, `RoundMask`, `keccakActive` |
| F08 | Complete hash claims retain protocol shape and first-span restrictions | Public-program binding derives selected span/controller shape and all issued round coverage/masks; full coverage exposes the zero-clock extended-round boundary | Mode/duration/preparation, public code profile, controller extents/full coverage and legacy prefix conditions |
| F09 | Decoder/setup models need an implementation binding | Unresolved provenance/structural correspondence | Modeled table equality and logical decoder membership |
| F10 | Caller-cycle effects are weaker than full custom instruction execution | Shared ordinary/caller/worker composition checked; full-call semantic connection blocked | One history and raw PC path do not turn accepted invalid calls into full CSR reference execution |

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

**Derived initialization binding.** The
[unissued worker entry](Airbender/Review/Trace/UnifiedReduced/Theorems.lean)
now roots all reads of every zero-clock worker directly in the public initial
image, including raw timestamps and canonical words. This uses native write-clock
floors and logical memory matching, without supported-operation premises. It
retains the actual G state change above, including when the later ADDI reset is
present. For extended rounds, the actual public x12 high limb now characterizes
exclusive masks exactly; this does not establish exclusion or inertness.

**Derived multiplicity bound.** With a distinct initialized physical-cell domain,
the shared x10 transfer now derives unique numeric and raw invocation clocks for
all four families, including zero. The unissued sublist has at most one occurrence.
`duplicate_unissued_request_checks` preserves native participation and virtual
matching for two identical G rows; `duplicate_unissued_workers_rejected` proves
that architectural acceptance rejects that pool. `unissued_worker_bound_is_sharp`
retains the existing single G worker and its actual state change. This strengthens
the multiplicity bound while keeping the demonstrated unissued-worker finding.

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

## F05 — Padding erasure resolved under an explicit contribution-mask boundary

**Local evidence retained.** [InactiveRow](Tests/InactiveRow.lean) checks execute
zero, initial PC zero, final PC four and destination low limb 123 under the retained
local ADD/SUB constraints. This disproves raw stuttering; it does not demonstrate
an implementation bug. The Rust compiler already masks global contributions.

**Checked logical connection.** The user authorized the
[external contribution-mask boundary](Airbender/Review/Helpers/Context/PaddingBoundary/README.md)
on 15 October 2026, analogous to the verifier-PC boundary. Boolean native execute
flags interpret an inactive row's aggregate as identity and retain an active row's
full tuples. Exact masked PC, architectural memory and virtual CSR permutations
keep the whole raw layout and unmasked public endpoints. Erasing identity factors
derives the existing active-trace acceptance contracts and
[whole execution entries](Airbender/Review/Trace/Padding.lean). All raw imported
constraints and retained auxiliary/range/timestamp queries remain checked; active
decoder membership retains its original logical table scope.

**Regression.** [PaddingBoundary](Tests/PaddingBoundary.lean) supplies complete
native clock lookups for the PC 0→4/result-123 inactive case. Two such occurrences
are inserted into the actual initialized [dependent ADD trace](Tests/TraceExecution.lean),
which reaches the same Sail terminal PC/cells. A padding-only forged terminal
transition and a non-Boolean selector are rejected. Active zero-valued tuples stay
present. A colliding scalar encoding does not imply tuple matching. The existing
zero-clock G worker survives projection and both invalid bigint controls inhabit
the new boundary; padding selection is independent of invocation/control validity.

**External trust retained.** The contract is a named theorem premise, not a project
axiom or a proof of Rust verification. It assumes exact symbolic tuple closure
and the binding of compiled masks to actual native execute columns. Product
equality at sampled challenges is insufficient by itself. Address-space
projection, import/compiled correspondence and GKR/cryptographic soundness remain
external. F05 is conditionally resolved at this logical boundary; no inactive
row's desired output or architectural inertness was assumed.

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
this issued result. A separate initialization binding now derives each unissued
worker read and proves that its actual initial x12 high limb equals
`flags + 8 * 2^round` exactly when its native bits form that exclusive mask.
Zero and multibit controls remain unsupported by that ABI. A publicly zero seed
implies no exclusive mask, without asserting an accepted unissued-round witness
or excluding such a worker.
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
registry and global public round-CSR occurrence coverage too. Jumps, branches
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
The unissued-round question and whole caller retirement remain explicit boundaries.
Source-aware final preparation is checked; branch/jump preparation extensions are
outside the frozen registry.

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
Uncovered hash workers are exactly zero-clock residuals; the native unissued G
still changes actual x12 from zero to one. An issued G worker is covered at its
actual clock-five invocation, while its one-call interval cannot satisfy the
56-call reference scope. Missing windows, wrong families, repeated-address omissions
and overlap are rejected. All four COPY/carry/invalid-bigint preparation fixtures
remain admitted outside the hash partition. Whole custom-CSR retirement and
unrestricted invalid-call/ROM behavior remain separate.

**Remaining boundary.** Public code coverage and complete protocol shape remain
explicit. They are not consequences of general acceptance: zero-clock workers
and the invalid-call cases remain exposed. Whole custom-CSR retirement is F10;
optional preparation variants are outside the frozen finalization scope.

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

## F10 — Shared cycle composition does not validate the full custom CSR reference

**Checked connection.** [MixedCycleEffects](Airbender/Review/Trace/UnifiedReduced/MixedCycles.lean)
now combines original ordinary/custom retirement, current public fetch,
[caller observations](Airbender/Review/Trace/UnifiedReduced/CallerCycles.lean),
all workers and the complete native PC/clock path over one initialized history.
`Caller.mixed_cycle_soundness` derives reads, operands, decoding and scheduling
under the existing public configuration, tracked-RAM and unchanged-Sail load
profile. The actual final memory agrees with terminal cells in the retired-PC
view of the native path's terminal endpoint. No successful full custom-CSR
reference sequence is claimed by this observational certificate.

**Retained counterexamples.** F02's invalid bigint calls with controls 0 and
65537 instantiate the combined certificate itself. The same assembly also covers
actual COPY→LW/SW retirement and the zero-clock G's real prefix execution.
The former reference rejects both controls; the latter worker has no caller.
Adding ordinary retirement and terminal observations therefore does not supply
full-call control/pointer/invalid-call semantics. The original standard/custom
[Mixed.execution_soundness](Airbender/Review/Trace/UnifiedReduced/Theorems.lean)
continues to exclude delegation callers from its successful-instruction registry.

**External closure needed.** Bind accepted caller validity and participation to
the complete pinned reference, including invalid calls, or make an explicit
reference/scope decision. Current constraints and matching cannot imply the
missing properties in the face of F02/F03. Worker ROM binding (F04) needs its stated additional inputs. Inactive
padding (F05) now has the separately authorized conditional logical closure. Independent composition work
is checked; the hourly task stops here rather than adding optional preparation
or instruction variants. All generated/import/cryptographic and exceptional-path
milestones remain separately deferred.

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

The current milestone checks the library, both executables, all concrete Lean
test modules, importer regressions, the full axiom audit and review/reference
checks; totals are in [Verification status](VERIFICATION_STATUS.md).
[Modular pooled execution](Airbender/Review/Trace/Modular/README.md) now combines
ADDMOD/SUBMOD/MULMOD/FMAMOD with independent external reads and write hints,
including exact consumption and rejection of short/reordered streams.
[Unified modular execution](Airbender/Review/Trace/UnifiedReduced/ModularExecution.lean)
uses the unified artifact's own equations with standard/TRIADD/XORROT retirement.
The concrete unified trace checks all four dependent modular operations, all four
x0 forms, ADD and TRIADD; a forged FMA old read is locally valid and rejected by
initialized global matching. No circuit, reference, public boundary or finding
classification changes. Existing terminal-PC, inactive-row, invalid-control,
zero-clock, ROM-shadow and discarded-load regressions remain checked.

Review F01's explicit canonical boundary contract and the remaining Rust/artifact
and cryptographic correspondence. For unresolved F02–F04, review the actual request
and worker acceptance argument first; then review F07/F08's witness-shape
restrictions and F09's concrete setup binding. Closing a remaining finding should
supply that connection or explicitly revise the claimed scope; adding the missing
property as an assumption is not closure.
