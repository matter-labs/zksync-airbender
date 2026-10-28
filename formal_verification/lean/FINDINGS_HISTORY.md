# Findings validation history

Historical checkpoints do not establish current-head assurance. See
[verification status](VERIFICATION_STATUS.md) for the evidence inventory.

## Historical integration checkpoints before the rebase

The progress notes in this section describe the pre-#490 relation and their
original validation totals. Current status is in the case register and F03 below.
Their accepted zero-clock execution witnesses are preserved in the
[pre-rebase source](https://github.com/matter-labs/zksync-airbender/blob/010c3cbb3c237b6e125277162dd1011c2f212333/formal_verification/lean/Tests/DelegationZeroInvocation.lean);
current regressions retain the exact raw witness and prove native rejection.

### Issued round coverage and wrapped preparation

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
rejects consuming that token again before the cut.
[`BigintControlBoundaryExecution`](Airbender/Review/Trace/UnifiedReduced/RegisterDataflow.lean)
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

## Historical rebased validation checkpoint — 21 October 2026

At this historical checkpoint, the native artifacts and proof adapters passed the library, both executables,
all 137 concrete test modules, importer regressions and review/source checks.
All 13 setup artifacts, 85 native source hashes and 11 retained circuit identities
are checked. The full audit has 3,850 roots (149 axiom-free), with no added axioms:
all 3,606 still-applicable prior roots remain, 3,605 reports are identical and one
uses fewer axioms. The 53 old accepted-zero execution roots were explicitly
retired because #490 makes those statements false; the exact raw witness,
arithmetic, cancellation, filtering and valid issued execution remain checked,
with current native rejection replacing obsolete acceptance. All 166 public
Review theorem roots remain audited.
The diagonal-query refactor adds 20 checked row/binding roots; all 3,830
post-rebase audit reports remain identical, and the original query theorem's
statement and assumptions are unchanged.

The native JSON round-trip check also retains strict equality with the actual
Rust circuit object. A small [wire-format serializer](Airbender/Import/NativeJson.lean)
implements Rust's omission of an absent
[generic_lookup_padding field](Airbender/Import/Schema.lean); present zero,
nonzero padding and other explicit null fields are retained. This is serialization
fidelity, not a new circuit assumption or cryptographic correspondence claim.


## Validation and next review

The temporary-contract proofs check distinct window domains, decoder filler
exclusion, full occurrence coverage, native command selection and RAM-port token
transport. Regressions retain sparse/reversed distinct windows, reject duplicates
and truncation, retain historical raw zero-clock matching while proving current
native rejection, and exclude the invalid-control and ROM-shadow witnesses only
from the corresponding temporary contracts. Those latter witnesses remain accepted. These are
conditional mathematical results, which alone fix no implementation finding.
AIH-334's separately validated source fix is recorded above.

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
initialized global matching. The subsequent temporary-contract milestone leaves
existing acceptance predicates, circuit artifacts and pinned references unchanged;
its source/comment assessments are recorded above. Existing terminal-PC, inactive-row, invalid-control,
zero-clock, ROM-shadow and discarded-load regressions remain checked.

Review F01's explicit canonical boundary contract and the remaining Rust/artifact
and cryptographic correspondence. For F02/F04/F11, review the public supported-use
domain and its exact-prefix transport, preserving the broader native
counterexamples and lower-level conditional APIs. F07/F08's algorithm/protocol
restrictions and F09's concrete setup binding retain their separate scopes.
Other implementation findings need an actual repair or a justified scope
disposition; adding a proof premise alone does not repair an implementation.
