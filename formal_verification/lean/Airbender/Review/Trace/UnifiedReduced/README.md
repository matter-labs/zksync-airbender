# Unified execution review

This directory states execution claims for the unified artifact: ordinary and
selected custom instruction retirement, caller-cycle observations, and complete
reference effects on selected native-clock windows. The claims share actual
history-derived states. Shared cycle composition now covers every native row in
one history and PC/clock path; full custom-CSR execution remains blocked by the
recorded invalid-call and participation cases.

## Checked results

| Result from accepted history and stated public inputs | Direct theorem in Theorems |
| --- | --- |
| Original standard instructions retire and reach native terminal PC/cells, using public ROM bytes. | [`execution_soundness`](Theorems.lean) |
| Standard instructions plus TRIADD/XORROT retire together; delegation callers are outside the registry. | [`Mixed.execution_soundness`](Theorems.lean) |
| Standard/TRIADD/XORROT plus ADDMOD/SUBMOD/MULMOD/FMAMOD share native initialized execution in BabyBear, including discarded writes and aliased old destinations; external masked padding is supported. | [`Modular.execution_soundness` and `Modular.padded_execution_soundness`](ModularExecution.lean) |
| Every ordinary retirement, caller observation and worker uses one actual history and complete raw PC/clock path, with terminal cells in the final retired-PC view. Full custom-CSR execution remains separate. | [`Caller.mixed_cycle_soundness`](Theorems.lean) |
| Machine and worker reads/writes, bounds and references share one actual initialized history. | [`Caller.mixed_memory_soundness`](Theorems.lean) |
| Exact caller regions, counts and slots follow from state/request matching and public cuts/duration. | [`Caller.window_schedule_soundness` and `Caller.request_window_soundness`](Theorems.lean) |
| Public sequential code identifies caller regions; native matching derives selected worker family, counts and slots. | [`Caller.program_window_schedule_soundness`](Theorems.lean) |
| Modular public code regions derive the same selected family/count/request-slot binding through comparison wraparound. | [`Caller.wrapped_program_window_schedule_soundness`](Theorems.lean) |
| Public CSR controller regions and at most forty ticks derive round-worker family/count/duration and the ten-position bound. | [`Caller.program_round_region_soundness`](Theorems.lean) |
| Modular public controller regions derive local round-worker shape with the same forty-tick extent. | [`Caller.wrapped_program_round_region_soundness`](Theorems.lean) |
| Coverage of public decoded round CSRs derives region membership exactly for live round workers. | [`Caller.program_round_coverage_soundness`](Theorems.lean) |
| Public round CSR coverage and LUI preparation derive every issued round mask from raw matching, without full worker coverage. | [`Caller.program_round_live_masks_soundness`](Theorems.lean) |
| Full controller coverage is equivalent to absence of zero-clock extended-round workers in the public sequential/controller profile. | [`Caller.program_round_global_coverage_boundary_soundness`](Theorems.lean) |
| Modular public round-CSR occurrence coverage derives membership exactly for live round workers, including repeated addresses. | [`Caller.wrapped_program_round_coverage_soundness`](Theorems.lean) |
| Modular occurrence coverage and public preparation derive every issued round mask without full worker coverage. | [`Caller.wrapped_program_round_live_masks_soundness`](Theorems.lean) |
| The modular profile exposes the same equivalence between full coverage and absence of zero-clock round workers. | [`Caller.wrapped_program_round_global_coverage_boundary_soundness`](Theorems.lean) |
| Zero-clock workers read the original public initialization tokens, with actual values and raw clocks. | [`Caller.unissued_worker_reads_soundness`](Theorems.lean) |
| The actual public x12 seed characterizes every exclusive mask of an unissued extended-round worker. | [`Caller.unissued_round_control_soundness`](Theorems.lean) |
| Initialized architectural matching distinguishes all numeric/raw worker invocation clocks, including zero, and bounds the unissued sublist to one occurrence. | [`Caller.worker_invocation_uniqueness_soundness`](Theorems.lean) |
| Every worker has actual pre/post-states in one initialized execution; a zero-clock worker forms the first transfer group directly from public initialization. | [`Caller.all_worker_execution_soundness`](Theorems.lean) |
| Actual joint cut states and projected worker boundaries retain native timestamps. | [`Caller.mixed_window_soundness` and `Caller.mixed_window_projection_soundness`](Theorems.lean) |
| Aligned public sequential/comparison decoding and native matching derive modular RV32 program addresses, including comparison PC wraparound. | [`Caller.wrapped_program_address_soundness`](Theorems.lean) |
| Public ADDI-from-x0/LUI preparation yields actual controls after literal, sequential ordinary/custom or aligned comparison prefixes; native PC/clock matching derives each preparation address. | [`Caller.control_preparation_soundness`](Theorems.lean) |
| AUIPC computes a control from its derived public PC and U-immediate, with an actual initialized cut state and canonical native token at cut minus two. | [`Caller.pc_relative_control_preparation_soundness`](Theorems.lean) |
| Literal, publicly placed AUIPC or literal→ADDI code derives the actual protocol entry read and retained native token. | [`Caller.hash_control_preparation_soundness`](Theorems.lean) |
| Two public literal/ADDI instructions bind a protocol constant, deriving operand tokens from initialized matching before round-mask transport. | [`Caller.literal_addi_hash_preparation_soundness`](Theorems.lean) |
| Finite public literal/AUIPC→ADDI chains derive actual operands, values and canonical tokens across registers and aliases. | [`Caller.register_chain_control_preparation_soundness`](Theorems.lean) |
| Public register-chain expressions bind protocol entry constants through the same complete selected-reference interfaces. | [`Caller.register_chain_hash_preparation_soundness`](Theorems.lean) |
| Public dataflow retains tracked values and real timestamps across intervening arithmetic, bitwise/shift/REV8, comparison and admitted custom writes to other GPRs and LW/SW memory gaps, including discarded-LW NOPs, actual RAM writes/refreshes and retained native timestamps. | [`Caller.register_dataflow_control_preparation_soundness`](Theorems.lean) |
| A final ADDI binds that nonconsecutive dataflow to protocol constants and canonical entry tokens for the existing selected-reference interfaces. | [`Caller.register_dataflow_hash_preparation_soundness`](Theorems.lean) |
| Complete selected G/Keccak references admit either preparation source at their actual joint cut states. | [`Caller.computed_prepared_hash_window_soundness`](Theorems.lean) |
| Nonempty ordered lists may mix all admitted preparation forms while retaining every intervening transfer in one history. | [`Caller.computed_prepared_hash_sequence_soundness`](Theorems.lean) |
| Either preparation source and public modular code derive caller rows, exact request slots, worker family and count. | [`Caller.hash_prepared_public_window_schedule_soundness`](Theorems.lean) |
| Public modular regions derive complete G/Keccak span shape before source-aware reference composition. | [`Caller.wrapped_program_computed_hash_window_soundness`](Theorems.lean) |
| Public modular regions derive every selected shape in an ordered list with literal/AUIPC/register-chain preparation. | [`Caller.wrapped_program_computed_hash_sequence_soundness`](Theorems.lean) |
| Literal or AUIPC code prepares actual regional round-zero seeds; raw matching derives exclusive masks. | [`Caller.computed_round_region_masks_soundness`](Theorems.lean) |
| Public modular controller code and at most forty ticks derive regional shape before source-aware mask transport. | [`Caller.wrapped_program_computed_round_region_soundness`](Theorems.lean) |
| Source-aware regions derive global memory inputs under explicit full round-worker coverage. | [`Caller.computed_protocol_memory_soundness`](Theorems.lean) |
| Public round-CSR occurrences derive live membership/masks for any admitted source, with the zero-clock coverage boundary explicit. | [`Caller.wrapped_program_computed_round_coverage_soundness`](Theorems.lean) |
| Complete G, extended-BLAKE and Keccak lists admit literal/AUIPC/register-chain preparation in one initialized history. | [`Caller.computed_prepared_protocol_sequence_soundness`](Theorems.lean) |
| Public modular caller/controller regions derive every shape before complete source-aware reference/list composition. | [`Caller.wrapped_program_computed_protocol_sequence_soundness`](Theorems.lean) |
| Register-dependent ADDI derives its actual operand/cut states, RV32 result and retained output token, including aliases and earlier worker effects. | [`Caller.register_immediate_control_preparation_soundness`](Theorems.lean) |
| Two preparations share their actual cut states and the complete intervening machine/worker history; neither control is supplied. | [`Caller.control_preparation_window_soundness`](Theorems.lean) |
| Two native windows and their gap execute continuously from one initialization with retained tokens and clocks. | [`Caller.mixed_window_chain_soundness`](Theorems.lean) |
| An arbitrary ordered finite list of native windows and gaps shares that continuous execution. | [`Caller.mixed_window_sequence_soundness`](Theorems.lean) |
| Complete prepared G/Keccak and extended-BLAKE references reach the selected actual cut states; masks are derived. | [`Caller.prepared_hash_window_soundness` and `Caller.prepared_round_window_soundness`](Theorems.lean) |
| Two complete prepared G/Keccak references use the same continuously executed states across the intervening preparation and other effects. | [`Caller.prepared_hash_chain_soundness`](Theorems.lean) |
| A nonempty ordered list of complete prepared G/Keccak references binds every span to that same continuous execution. | [`Caller.prepared_hash_sequence_soundness`](Theorems.lean) |
| Public LUI preparation and raw matching derive exclusive masks inside each selected extended-BLAKE caller region, retaining earlier workers. | [`Caller.prepared_round_region_masks_soundness`](Theorems.lean) |
| Ordered complete G/extended-BLAKE/Keccak lists share one execution when prepared controller regions cover every extended-round worker. | [`Caller.prepared_protocol_sequence_soundness`](Theorems.lean) |
| Public caller regions derive each selected span's worker family/count before all three references compose continuously. | [`Caller.program_prepared_protocol_sequence_soundness`](Theorems.lean) |
| Modular selected span/controller regions derive shape before the same continuous complete-reference composition, retaining explicit global round coverage. | [`Caller.wrapped_program_prepared_protocol_sequence_soundness`](Theorems.lean) |
| Original current-state caller fetch, selected worker observations and PC retirement meet at the same boundaries; native memory order derives positive row clocks. | [`Caller.native_caller_cycles_soundness` and `Caller.caller_cycles_soundness`](Theorems.lean) |

Field/inverse, public boot/configuration/program/domain, modeled tables and logical
matching remain explicit. Window claims additionally retain cut alignment/location,
duration, mode/count and prefix ABI conditions. No intermediate states or scheduling
answers are supplied. Caller-cycle observations still admit the checked bigint
invalid controls, so they are not full custom-CSR execution.

[Modular regression](../../../../Tests/UnifiedModularExecution.lean) checks all
four dependent modular operations, all four x0 forms, an ordinary ADD consumer
and TRIADD in a single reversed-row trace with actual public instruction bytes.

Start with [Theorems](Theorems.lean) and choose the exact public claim.
[Execution](Execution.lean), [CustomExecution](CustomExecution.lean) and
[MixedExecution](MixedExecution.lean) distinguish ordinary instructions,
pinned TRIADD/XORROT forms and their composed registry.
[Shared inputs](../../Helpers/UnifiedReduced/README.md) supply public state,
program/domain, modeled tables, matching and profile conditions.

Ordinary/custom mixed retirement derives current-state fetch, reads, selectors
and terminal PC/cells. Delegation callers are outside that instruction registry.

[CallerCycles](CallerCycles.lean) binds full-family fetch, actual worker observations
and Sail PC retirement at shared cycle boundaries. The native entry derives
positive caller clocks from strict memory order and four-alignment, without a
separate positive initial-clock premise. The earlier clock-parameter entry remains
available. The issued bigint invalid-control fixtures still satisfy these
observations, so a full custom-CSR ABI remains separate.

[MixedWindows](MixedWindows.lean) and [WindowProjection](WindowProjection.lean)
expose actual cut states. [JointHashWindows](JointHashWindows.lean),
[PreparedHashWindows](PreparedHashWindows.lean) and
[PreparedRoundWindows](PreparedRoundWindows.lean) bind complete selected references
at those boundaries. Prepared G/Keccak spans admit earlier workers, including
unissued effects; only the last preparation cycle is worker-free. The original
first-span extended-BLAKE entry retains its empty prefix. Public preparation/count/duration and these restrictions
remain explicit; cuts do not reset clocks or supply intermediate states.
The public ordinary registry may contain different literal writes or arbitrary
ADD/SUB/ADDI/LUI/AUIPC operands along a straight path with callers. Each preparation
cut derives its final literal and register from
that public address. Prepared G/Keccak windows inherit this scope, allowing explicit
mode changes or resets between spans; completion alone does not restart a protocol.
G/Keccak require their own family only inside the selected span. Bigint, G and
Keccak workers outside it remain in joint history; this scope excludes extended
round workers because their masks need separate transport. It adds no bigint
control-validity condition. [Control preparation](ControlPreparation.lean) also
connects two prepared controls through one intervening native window.
[`WindowChain.Realizes`](MixedWindows.lean) names the retained tokens, actual states
and complete prefix/span/gap transfers. The second span starts from the first
span's actual finish after executing the gap. [Prepared hash chains](PreparedHashWindows.lean)
bind both complete references to those same states; neither gap effects nor clocks
are reset. Empty and nonempty gaps, fabricated gap states, and an unissued prefix
effect are checked in [native chain regressions](../../../../Tests/ControlPreparation.lean)
and [the zero-clock regression](../../../../Tests/DelegationZeroInvocation.lean).
These are memory/reference claims; instruction retirement remains separate.
The [arithmetic-prefix regression](../../../../Tests/ControlPreparation.lean)
derives actual ADD→ADDI-reset states 65537→131074→0 in that same continuous history,
despite reversed native rows. The preparation read uses the actual clock-six ADD
token, and the reset retains clock ten. Fabricated reads fail joint matching.
The [`SequentialProgram`](../../Helpers/UnifiedReduced/ControlPreparation.lean)
profile also admits LW/SW, bitwise/shifts, REV8 and supported TRIADD/XORROT before
the final literal. Original public decoding and native constraints derive the
PC-increment selectors; jumps, branches and wraparound comparisons remain outside
this profile. The same fixture checks TRIADD→ADDI with actual states
65537→196611→0 and rejection of a fabricated reset read. Prefix retirement and
discarded-load semantics remain separate from preparation/memory transport.
The separate [`WrappedSequentialProgram`](../../Helpers/UnifiedReduced/ControlPreparation.lean)
adds the four original comparisons and public code alignment, with modeled setup
and `4194304 ≤ p` explicit. Native constraints and matching derive modular RV32
program addresses. The [comparison-wrap regression](../../../../Tests/UnifiedComparison.lean)
checks SLTIU at `0xfffffffc` followed by ADDI at zero, actual x12 = 65537→1→0
in one history, retained clocks six/ten and rejection of a fabricated read or
wrong literal. Prepared entries using control preparation inherit this variant;
selected caller/controller region shape and global round-CSR occurrence coverage
now also use modular addresses. Jumps, branches and nonliteral preparation remain
open, as does whole caller retirement.

[`PCRelativePreparedBoundaryExecution`](PCRelativePreparation.lean) now exposes an
actual AUIPC-prepared cut from the same initialized mixed history.
[`PCRelativePreparedControl`](../../Helpers/UnifiedReduced/PCRelativePreparation.lean)
retains its canonical output token and original write clock. Public modular
sequential/comparison decoding and native state/clock matching derive the final
instruction's address; native arithmetic equations derive its RV32 sum with the
U-immediate, including overflow. No expected output or selected native row is
supplied. Only the final cycle is worker-free; earlier effects remain in the
prefix. The entry retains public setup/tables and extended-round masks through
existing history realization. The [preparation fixtures](../../../../Tests/ControlPreparation.lean)
check x12 = 65537→524292 at PC four and 65537→61444 for a sum wrapping 2^32 at
PC 65540, both with clock-six tokens. The immediate alone gives a different
value. Wrong immediates and fabricated native reads are rejected. This is
preparation and memory transport. Complete G/Keccak references now consume this
preparation through the source interface below. General operand-dependent
preparation and jumps/branches remain open.

[`HashControlPreparation`](ComputedHashWindows.lean) combines the literal source
and AUIPC source without changing either legacy contract. AUIPC's decoded public
instruction address and U-immediate must compute the chosen protocol entry
constant. This public code-placement policy supplies no current-state control
read; native matching identifies its actual instruction and derives the canonical
entry token at cut minus two. The same history derives the actual cut read.
[`ComputedPreparedHashWindowInputs`](ComputedHashWindows.lean) connects that source
to the existing complete G/Keccak reference and exact caller binding. Nonempty
ordered lists may mix all three forms; each gap and reference uses the same continuous
native execution and derived boundary states. Mode/count/duration, selected family,
public domain/setup/tables and logical matching remain explicit. The current
complete entries retain the nonround worker scope. The separate
[`WrappedProgramComputedHashInputs`](ComputedHashWindows.lean) and
[`WrappedProgramComputedHashWindowInputs`](ComputedHashWindows.lean) replace
selected family/count premises with public modular code regions and duration.
Native matching derives caller rows, exact request slots, worker family and
count before invoking the same window/list composition. The global nonround
boundary still quantifies every worker. Source-aware extended-round masks now
use the separate regional entry below; complete extended-round reference/list
integration uses the all-family source-aware entry described there.
Legacy literal entry points use the same composition proof and retain their
signatures. [Concrete preparation fixtures](../../../../Tests/ControlPreparation.lean)
check AUIPC at PC 128 for G's control 128 and a wrapped sum at PC 4096 for Keccak's
control zero, actual reads from 65537, canonical tokens and clock six. A wrong
public placement and incomplete 56/649-call windows are rejected. These fixtures
check preparation and incomplete-span guards; the complete reference/list claims
are arbitrary-witness theorems under their stated span ABI. The existing unissued
G-prefix preparation remains admitted through the literal source. Bigint-control,
worker ROM-shadow, terminal-PC and discarded-load boundaries stay unchanged.
The same native preparation witnesses derive empty selected regions with zero
callers/workers; complete scopes reject incomplete durations, cuts past the
native terminal and regions containing ordinary preparation code. The literal
public-region fixture retains the unissued G worker in its actual prefix.

[`ComputedRoundRegionInputs`](ComputedRoundRegions.lean) admits any admitted source
for an extended-round controller. The actual canonical round-zero token seeds
the existing raw matching/control argument, which derives every selected mask.
[`WrappedProgramComputedRoundRegionInputs`](ComputedRoundRegions.lean) derives
regional family/count/duration and the ten-position bound from public modular
code, aligned ordered cuts and at most forty ticks.
[`ComputedPreparedProtocolInputs`](ComputedRoundRegions.lean) retains explicit
full round-worker coverage when transporting those masks to global memory.
No desired read, mask, empty prefix or global ten-row cap is supplied. Legacy
LUI mask/global-memory entries retain their signatures and share this proof.
Native AUIPC preparation at PC 524288 derives x12 = 65537→524288 and the canonical
clock-six token. The empty regional/global context is inhabited; wrong public
flags, invalid cuts and simultaneous round bits are rejected under the ABI.
These concrete fixtures cover preparation/empty regions; nonempty masks are
arbitrary accepted-witness theorems. The unissued G-prefix effect remains
admitted in the source-aware global context. Public modular round-CSR occurrence
coverage now derives precisely live regional membership and every issued mask
for any admitted source, including repeated RV32 addresses. Full coverage is equivalent
to absence of zero-clock round workers; it does not follow from CSR coverage alone.
[`ComputedProtocolWindowInputs`](ComputedRoundRegions.lean) connects any admitted source
to complete G, extended-BLAKE and Keccak reference lists in one history. Its
selected family/count/duration remain explicit.
[`WrappedProgramComputedPreparedProtocolInputs`](ComputedRoundRegions.lean) and
[`WrappedProgramComputedProtocolWindowInputs`](ComputedRoundRegions.lean) replace
selected shape premises with public modular caller/controller code and cuts.
All gaps and actual intermediate states are derived through the existing shared
composition. Full round-worker coverage, domain/setup/tables and logical matching
remain explicit. Legacy coverage/reference/list entries retain their signatures
and share these proofs. Native preparation/empty-region fixtures inhabit the
public context and reject incomplete counts/durations and cuts past the terminal;
the complete reference/list claims remain general accepted-witness theorems.
Broader operand-dependent preparation, jumps/branches and whole caller retirement
remain separate.

The separate [`RegisterImmediatePreparation`](../../Helpers/UnifiedReduced/RegisterPreparation.lean)
identifies a final ADDI with any source register and a nonzero destination through
public modular code. Initialized history derives the actual source state and
operand bounds; imported arithmetic derives
[`registerImmediateValue`](../../Helpers/UnifiedReduced/RegisterPreparation.lean)
using Sail's original sign extension. The
[`RegisterImmediatePreparedBoundaryExecution`](RegisterPreparation.lean) retains
that initialized prefix, the actual native cycle, exact prefix matching and its
canonical output token at cut minus two. The
[`RegisterImmediatePreparedControl`](../../Helpers/UnifiedReduced/RegisterPreparation.lean)
connects the actual source read to the actual cut read, including aliases. Only
the final cycle is worker-free; earlier effects remain. No desired read, bound,
selector, intermediate state or result is an input. Native fixtures check actual
65537→65665 and 65537→65536, clock six, a wrong immediate and a fabricated source.
An unissued G-prefix fixture retains actual 0→1→1 states, distinguishing the
operand from its public initial value. Literal/AUIPC contracts remain and share
arithmetic/output-token helpers. This is memory preparation.

The third `HashControlPreparation` source uses
[`LiteralAddiPreparation`](../../Helpers/UnifiedReduced/RegisterPreparation.lean):
a public literal writes a source register immediately before a public ADDI.
Raw prefix/suffix matching, strict native clocks and the existing distinct public
domain derive the first-read word from the literal token. This precedes Sail
transport and regional round-mask derivation, so no mask or desired read is
assumed to bind the protocol value. A public literal/immediate equation selects
the protocol entry constant. The convenient
[`Caller.literal_addi_hash_preparation_soundness`](Theorems.lean) derives seed
uniqueness from the existing public cell domain. Both final cycles are worker-free;
all earlier effects remain. The source reaches the same complete G, extended-BLAKE
and Keccak windows/lists, including public modular shape and raw regional masks.
Coverage/domain/setup/tables and logical matching remain explicit. Native
reversed-row fixtures derive 65537→127→128 and 65537→129→128 with aliases,
signed −1 and canonical clock ten; wrong immediates/constants, fabricated operands
and incomplete references are rejected. An accepted unissued G prefix remains in
one initialized history before literal zero and ADDI 128. The fixtures cover
preparation and empty-region guards; full reference/list claims remain general
accepted-witness theorems. Other gap instructions, broader operations and
full Sail retirement remain open.


[`PublicRegisterPreparation`](../../Helpers/UnifiedReduced/RegisterChains.lean)
now expresses arbitrary finite consecutive ADDI chains rooted in a literal or
AUIPC. Each value index is computed from the public instruction expression,
including changes of nonzero register and aliases. Induction derives every actual operand
token from raw initialized matching and strict clocks, then native arithmetic
derives the next output. The legacy two-step source shares this proof and keeps
its signatures. No desired read, operand bound, intermediate state or selector
is supplied. Only selected preparation cycles are worker-free; earlier effects
remain. The
[`RegisterChainPreparedBoundaryExecution`](RegisterChains.lean) retains one
initialized prefix, the actual cut read and canonical token at cut minus two.
The protocol entry derives seed uniqueness from the existing public domain and
uses only a public expression/entry-constant equation. Its source reaches all
existing complete G, extended-BLAKE and Keccak windows/lists before Sail and
regional masks, retaining their existing coverage/domain/setup/table and logical
matching boundaries. Reversed-row native three-instruction fixtures derive actual
x12 = 127/129 → x10 = 128 → x12 = 128 and canonical clock fourteen; wrong
instructions/constants, fabricated middle reads and incomplete references are
rejected. Existing AUIPC fixtures inhabit the root and the actual unissued
G-prefix effect remains. Concrete fixtures cover preparation/guards; complete
references are general accepted-witness theorems. Other gap instructions,
broader operations and full Sail retirement remain open.


[`PublicRegisterDataflow`](../../Helpers/UnifiedReduced/RegisterDataflow.lean)
now permits intervening public ADDIs to other nonzero GPRs. A gap may read and
refresh the tracked register; public decoding derives its real destination and
raw initialized matching proves value preservation through readonly ports. The
other register's actual write stays in the same native history. Induction
alternates these gaps with computed ADDIs before Sail or regional masks. No
inert-gap, desired operand/state, bound or selector is an input. The
[`RegisterDataflowBoundaryExecution`](RegisterDataflow.lean) preserves the actual
native timestamp through exact prefix matching; after a gap it need not equal
cut minus two. A final public
ADDI derives the fresh canonical token required by all existing complete selected-
reference windows/lists, keeping their domain/setup/table, coverage and logical-
matching boundaries explicit. Selected ordinary cycles are worker-free; caller
gaps retain all worker effects in the same history. Reversed-row native fixtures prepare x12 = 127/129, copy it to
x10 from initial 65537 in the gap, then derive x12 = 128 with signed +1/−1.
The gap refresh retains clock eight; final output retains clock fourteen. A
forged source clock ten passes local native constraints/timestamp lookups but
fails joint matching. Constant/incomplete-reference guards and the actual
unissued G prefix remain. Concrete fixtures cover preparation/guards; complete
references are general accepted-witness theorems.

Caller gaps now preserve tracked GPRs outside x10/x12. Public modular code
excludes ordinary entries at the selected address; accepted decoding and PC/clock
matching derive the caller. The original imported port descriptors derive the
write footprint of all four worker layouts: bigint/BLAKE can write x12, Keccak
can write x10, and other fixed-register accesses only refresh values. RAM writes
remain in the same initialized history. No worker-free gap, selected worker,
valid control, nonzero invocation, desired read or inert effect is an input.
The raw token induction feeds the existing final ADDI and complete selected-reference
interfaces, retaining their domain/setup/table, coverage and matching boundaries.
A [reversed-row literal→COPY→ADDI fixture](../../../../Tests/UnifiedDelegation.lean) derives x13 = 0→127→127 while COPY
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
A [native COPY-with-carry fixture](../../../../Tests/UnifiedDelegation.lean) reads a 256-bit all-ones source from public RAM,
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
[Concrete reversed-row traces](../../../../Tests/UnifiedDelegation.lean) check COPY→ORI→ADDI
and carry-COPY→ORI→ADDI, plus both invalid incoming controls 0/65537. The actual
worker write retains clock seven, normalized one clock ten, and final control 128
clock fourteen. One initialized history retains the worker return and final control.
A fabricated clock-six source passes native constraints/timestamps and fails shared
matching. XORI is rejected by the public scope, and XORI of return one with one
cannot supply normalized one. An incomplete 56-call G window remains rejected.
The existing public domain, modeled tables, logical matching and complete selected
protocol scopes remain explicit. General operand-dependent x10/x12 results,
broader operations and whole caller retirement remain open.


[`WrappedProgramCallerRegion`](../../Helpers/UnifiedReduced/WindowSchedule.lean)
states the public ordinary-exclusion/full-CSR-family policy at every clock in the
selected interval. Native matching derives counts and unique request slots without
PC injectivity or no-wrap assumptions. The corresponding
[`WrappedProgramPreparedProtocolInputs`](PreparedRoundWindows.lean) derives local
controller shape before reusing the existing raw-mask and reference proofs.
Public cuts, preparation, reference duration and global extended-round worker
coverage remain explicit. The need to justify supported masks or exclude unissued
round workers remains;
unissued G effects and both bigint-control gaps remain admitted. The original
linear entries and their global issued-round coverage/mask results remain available.

[`WindowSequence.Realizes`](MixedWindows.lean) extends this connection to an
arbitrary finite list. Its initial cut follows the actual prefix; every segment
executes its gap from the preceding actual finish, then its complete window.
[`WindowsOrdered`](MixedWindows.lean) makes cut order/alignment explicit and permits
empty windows and gaps. [`PreparedHashSequenceResult`](PreparedHashWindows.lean)
binds each complete G/Keccak reference, request permutation and caller count to
the corresponding segment. Every span keeps its own public preparation,
mode/count/duration and nonround worker scope; protocol shape is not inferred from
general acceptance. Three-window regressions retain actual controls across empty
and nonempty gaps, reject overlap/unaligned cuts, and preserve the unissued prefix.

The broader [prepared protocol inputs](PreparedRoundWindows.lean) allow extended
BLAKE alongside G, Keccak and bigint in the same history.
[`RoundRegionInputs`](PreparedRoundWindows.lean) binds each LUI restart to a
homogeneous caller region with at most ten positions. Raw prefix/window matching
derives its masks before any mask-dependent Sail transport; its control token
keeps the actual preparation timestamp. Earlier workers and earlier controller
regions stay in the prefix. [`PreparedProtocolInputs`](PreparedRoundWindows.lean)
requires these regions to cover every extended-round worker. This explicit
coverage replaces the global empty-prefix/family/ten-row restrictions in this
entry point; it does not derive unrestricted protocol validity from acceptance.
[`PreparedProtocolWindowInputs`](PreparedRoundWindows.lean) retains each selected
complete span's preparation, family, count and duration. The sequence theorem binds
all three complete references to their actual segment states without resetting
clocks. Completion alone is still not a controller restart. The regional seed,
wrong-flag/two-bit and retained-unissued-effect regressions are linked above.

[`ProgramProtocolWindowInputs`](PreparedRoundWindows.lean) replaces those selected
worker family/count premises with a public
[`ProgramCallerRegion`](../../Helpers/UnifiedReduced/WindowSchedule.lean).
The ordinary registry uses `SequentialProgram`; public PC/clock intervals exclude
ordinary entries and identify the CSR family. Accepted matching derives the actual
caller region and worker count from the public reference duration. The stronger
sequence theorem reaches the same complete references and actual segment states.
[`ProgramPreparedProtocolInputs`](PreparedRoundWindows.lean) now also derives the
local extended-round controller shape. Its
[`ProgramRoundRegionInputs`](PreparedRoundWindows.lean) supplies public CSR regions,
LUI preparation and at most forty ticks between ordered aligned cuts. Matching
derives local worker family/count, the ten-position bound and exact duration;
the existing regional proof derives masks before transport and reference composition.
[`ProtocolContextInputs`](PreparedRoundWindows.lean) shares public code/memory/table
conditions with the legacy regional interface. Global extended-round coverage
remains explicit, since live matching does not exclude surplus zero-clock workers.
Empty regions retain actual clock-six preparation tokens; wrong flags/family,
oversized/reversed/unaligned cuts and simultaneous round bits are rejected in
[preparation regressions](../../../../Tests/ControlPreparation.lean) and
[unified regressions](../../../../Tests/UnifiedDelegation.lean).
The stronger context retains the actual unissued G-prefix effect in
[zero-clock regressions](../../../../Tests/DelegationZeroInvocation.lean).
Public preparation/mode/duration and aligned ordered cuts remain explicit;
global controller coverage and unrestricted protocol validity remain open. COPY→ADDI and both
invalid bigint control fixtures check the schedule connection; wrong CSR family
and inclusion of ordinary code are rejected in
[the unified regressions](../../../../Tests/UnifiedDelegation.lean).

[`ProgramRoundCallerCoverage`](PreparedRoundWindows.lean) places each public decoded
extended-round CSR in a prepared region. Native PC/clock matching locates its actual
caller, and full CSR/request matching identifies the actual worker in that region.
[`RoundWorkerCoverage`](PreparedRoundWindows.lean) states the checked equivalence:
an extended-round worker belongs to a region exactly when its invocation is live.
Public LUI preparation and raw regional matching then derive exclusive masks for
every issued round worker. This local proof uses `ProtocolContextInputs`, with
full worker coverage reserved for global mask-dependent transport. The
[two-bit regression](../../../../Tests/ControlPreparation.lean) rejects two selected
round bits from these public inputs and a live target, without assumed masks or
whole-pool coverage.
The coverage equivalence assumes neither whole-pool worker coverage nor nonzero
invocations. Full coverage
is consequently equivalent to absence of zero-clock extended-round workers in this
public sequential/controller profile; their general exclusion or mask behavior
still needs a binding before global transport. Public-code regressions require a
nonempty covering interval for a decoded round CSR and preserve empty LUI-prepared
cuts. The actual unissued G worker and its prefix update remain admitted.

[`WrappedProgramRoundCallerCoverage`](PreparedRoundWindows.lean) extends coverage
to the aligned sequential/comparison registry. It covers every aligned clock
between the supplied native endpoints at which a public round CSR equals the
modular program address. Accepted constraints and state matching derive each
caller's clock interval; modular PC matching locates the actual occurrence and
request matching identifies its worker. This avoids a PC-injectivity or no-wrap
premise. The modular coverage, issued-mask and full-coverage boundary theorems
above retain the same unissued-round limitation. Regressions reject covering only
one of two occurrences 2^32 ticks apart in a public code-policy fixture (without
an accepted-trace claim), admit an empty prepared cut, reject two issued round
bits without whole-pool coverage, and retain the actual zero-clock G worker.

[`InitialWorkerReads` and `InitialRoundControl`](UnissuedWorkers.lean) bind the
remaining zero-clock boundary to actual public initialization. Strict memory order
and native alignment force positive machine clocks; worker writes start at two.
Every unissued read precedes clock two, so matching roots its full raw token in
the public seed. The derived value is canonical and keeps its zero timestamp.
This needs no operation mask or extra initial-clock floor. The actual initial
x12 high limb equals flags below eight plus `8 * 2^round` exactly when the native
bits form that exclusive round mask. Zero and multibit controls remain outside
the ABI. The zero-seed no-mask regression is conditional; it makes no accepted
unissued-round existence or exclusion claim. The actual G fixture still reads
zero, writes one and affects the prefix before a later ADDI reset. These native
read proofs do not execute an unsupported hash reference or make a worker inert.

[`WorkerInvocationUniqueness`](UnissuedWorkers.lean) now projects the shared native
x10 access from the existing initialized-memory key-uniqueness theorem. Every
family writes this fixed register at invocation plus two, so all numeric and raw
invocation clocks are distinct, including zero. The unissued sublist has at most
one occurrence. The public physical-cell domain remains distinct; supported
operation masks and opcode validity are not assumptions. Two identical zero-clock
G rows still satisfy native/request checks, but architectural acceptance rejects
the duplicate pool. The existing single G worker attains the bound and keeps its
actual prefix effect. Live COPY and both invalid bigint controls instantiate this
stronger result. General worker exclusion, inertness and unsupported-round mask
behavior remain separate from this multiplicity bound.

[`MixedWorkerExecution` and `UnissuedPrefixExecution`](UnissuedWorkers.lean) now
derive all workers' actual call states within one architectural history, including
the possible zero-clock worker. Full invocation uniqueness isolates its native
ports at transfer clock three. Strict memory order and alignment put machine rows
at clock four or later; all other workers are later as well. Its actual pre-state
is therefore the original public state, with no earlier transfers. The same
history retains every later transfer and reaches the shared terminal cells.
Every machine row also has derived cycle states in that same history, using its
native positive clock rather than an extra positive initial-clock premise. The
raw grouping and observation proof needs only public initialization, distinct
aligned cells and accepted native matching, without operation masks or a positive
invocation premise. The closed BabyBear entry reuses existing realization inputs,
including modeled setup/tables and the explicit extended-round masks; it does not
claim execution of unsupported round controls. The G→ADDI regression derives
actual x12 = 0→1→0 at these call/prefix/final states, and live COPY plus both invalid
bigint controls retain all-worker execution. A separate empty-machine fixture
has public endpoint clock zero while its unissued G worker still changes x12
from zero to one; this is a logical boundary fixture, with native boot still at
clock four. The new caller entry admits it, both invalid bigint controls and the
LW/SW caller fixtures. Caller retirement, full control ABI and worker
exclusion/inertness remain separate.

Keep surplus zero-clock prefix effects, worker ROM-shadow transport,
broader preparation/protocol binding, full mixed caller retirement and inactive padding as separate
outstanding obligations. [Status](../../../../VERIFICATION_STATUS.md) records the scope.

[Issued hash segmentation](Segmentation.lean)
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

## Shared cycle composition and stopping boundary

[RetirementProfile](../../Helpers/UnifiedReduced/RetirementProfile.lean) retains
public configuration, complete register initialization, readonly code, tracked-RAM
data and the unchanged-Sail discarded-load restriction. It supplies no operands,
reads, selected instructions, worker outputs or valid-control condition.
[MixedCycleEffects](MixedCycles.lean) combines the complete raw native PC/clock
path with original ordinary/custom retirement, caller observations and every
worker's actual call states in one initialized architectural history. The same
history reaches the terminal cells; its final retired view uses that path's
terminal PC. This conclusion is not a sequence of successful full custom-CSR
reference steps. The public theorem does not claim native worker ROM transport.

The native COPY→LW/SW fixtures instantiate the shared certificate; both invalid
bigint controls also instantiate it. The unissued G fixture retains its real
prefix execution. These cases show exactly why observation composition does not
supply the missing full-call semantics. Further instruction/preparation variants
are outside the frozen scope. Stronger execution requires justified invalid-call,
worker participation and ROM bindings; inactive padding is conditionally erased
under the separately authorized external contribution boundary. The hourly continuation ends at these external blockers.

The [external padding boundary](../../Helpers/Context/PaddingBoundary/README.md)
now projects whole masked machine/worker layouts into these same execution
contracts through [padded entries](../Padding.lean). Selection uses native execute
flags, preserving active zero-clock workers and invalid bigint controls. Exact
masked state/memory/request matching and Rust/GKR correspondence stay explicit;
this does not strengthen the full custom-CSR or worker-ROM claims.
