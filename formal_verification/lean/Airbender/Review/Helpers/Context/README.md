# Shared context review

[Timestamp](Timestamps.lean) and [column](Columns.lean) definitions preserve the
source formalization's two 19-bit clock limbs, four-tick step and three ordered
port slots. Clock inputs expose initial/prior bounds and alignment; clock effects
state derived advancement and strict previous-write ordering.

[Native ADD/SUB extraction](../../../Proofs/AddSub/Timestamp.lean) connects the
v2 equations and all eight timestamp queries to the unchanged generic clock
lemmas. [Native row data and logical matching](Model.lean) preserve the source's
small registry/token structure, restricted to v2 ADD/SUB. The
[PC/state representation](PCState/Model.lean) retains raw PC/time pairs; unconnected
v3 modeled decoder tables are omitted; native v2 ten-column decoder placement is
retained by the row registry, separately from table membership.

[History proofs](../../../Proofs/Trace/History.lean) derive row/prior clock bounds
and alignment from accepted state/memory matching and only initial clock inputs.
V2's two carry equations replace the source's BabyBear inverse argument. These
context definitions have no whole-execution dependency.

[Word-memory registry](WordMemory.lean) separately binds the checked word-memory
artifact, mixed ports, ten-column decoder query and native ROM setup type. Its
[public decoding](../../Trace/Families/WordMemory/Decoder.lean) now recovers actual
LW/SW source evidence. The [word-memory clock instance](../../../Proofs/Trace/Families/WordMemory/History.lean)
now reuses shared matching proofs to derive every per-row/prior clock input from
the public seed boundary. [Complete logical history](../../Trace/Families/WordMemory/History.lean)
and native word ranges are checked. [Sail cell histories](../../Trace/Families/WordMemory/SailHistory.lean)
now derive actual transfers and intermediate states in native clock order;
[architectural projection](../../Trace/Families/WordMemory/Projection.lean) now
retains full native matching with separate public shadow seeds. Physical native
boot/ROM binding and original instruction execution remain pending. The arithmetic
execution registry is unchanged.

[The control registry](JumpBranchSlt.lean) now binds the native jump/branch/SLT
artifact, all three register ports and raw state/decoder columns. [Clock extraction](../../../Proofs/JumpBranchSlt/Timestamp.lean)
reuses the word-memory structure with control-specific borrow/carry/query indices;
[its proved shared instance](../../../Proofs/Trace/Families/JumpBranchSlt/History.lean)
derives all row/prior clocks from actual public seeds/PC and accepted matching.
[One short history claim](../../Trace/Families/JumpBranchSlt/History.lean) obtains
complete Clean consistency and newest reads. No expected read, per-row clock or
ordering premise is added. [Aliased JAL and lower-clock carry tests](../../../../Tests/ControlHistory.lean)
pass; stale matching and missing explicit register data reject. Control word bounds,
actual Sail cell/instruction execution and terminal cell matching remain separate.

## Unsigned MUL/DIV context

[The native registry](MulDiv.lean) binds all imported constraints, state/clock columns, three register ports and decoder metadata. [Initialized history](../../Trace/Families/MulDiv/History.lean) supplies the shared Clean clock/history connection. Original instruction execution remains separate.

## Shift/binop context

[The native registry](ShiftBinop.lean) retains the complete imported artifact,
three register ports, state/clock columns and decoder metadata. [Metadata checks](../../../Proofs/ShiftBinop/ClockMetadata.lean)
keep the actual tagged setup geometry and port clocks. [Clock extraction](../../../Proofs/ShiftBinop/Timestamp.lean)
uses both native carry equations and all eight timestamp queries. [The family instance](../../../Proofs/Trace/Families/ShiftBinop/History.lean)
and [short public history claim](../../Trace/Families/ShiftBinop/History.lean)
derive every local/prior clock input and latest reads from initialization and
native matching. [Twenty-four initialized cases](../../../../Tests/ShiftHistory.lean)
retain readonly x0 refreshes; stale aliases fail matching. Word bounds and
original Sail cell/instruction execution remain separate.

## Shift/binop initialized ranges

[The native public decoder interface](../Decoder/ShiftBinop.lean) retains full
sparse/padded membership. [Native write preservation](../../../Proofs/Trace/Families/ShiftBinop/Values.lean)
now combines decoded masks and actual contributions with the unchanged time
induction, deriving [all native word ranges](../../Trace/Families/ShiftBinop/Values.lean).
[Canonical packed keys](../../Trace/Families/ShiftBinop/Sources.lean) use these
derived source bounds. [All twenty-four initialized regressions](../../../../Tests/ShiftValues.lean)
retain original code bytes, actual x0 masking and readonly refreshes. No expected
read, key, result or local range premise is introduced.

## Shift/binop whole numerical results

[The initialized result claim](../../Trace/Families/ShiftBinop/Theorems.lean)
now consumes these native histories and derived source bounds to prove whole
SLL/SRL/SRA/XOR/OR/AND results and canonical actual masked writes. No expected
source, result or local range premise is added. [Complete regressions](../../../../Tests/ShiftResults.lean)
retain original public bytes and all twenty-four ordinary/x0 cases. Original
Sail cell/GPR and instruction execution remain separate connections.

## Shift/binop original Sail cell and GPR transport

[The initialized register-history claim](../../Trace/Families/ShiftBinop/Registers.lean)
now derives all actual Sail segment states, original GPR reads/writes, final cell
matching and code/misa frames. [Native zero preservation](../../../Proofs/Trace/Families/ShiftBinop/ZeroRegister.lean)
uses full decoder membership and actual masked writes, retaining readonly alias
refreshes. [Complete regressions](../../../../Tests/ShiftRegisters.lean) cover all
twenty-four ordinary/x0 rows and twelve discarded whole-state stutters. Actual
original instruction execution and PC/fetched composition remain next.

## Shift/binop original Sail clause execution

[The initialized clause-history claim](../../Trace/Families/ShiftBinop/Clauses.lean)
now adds retained original instruction execution to actual native GPR histories.
Source bounds, selected operands, sign extension and SRAI's low-five-bit count
are derived. [Twenty-four complete fixtures](../../../../Tests/ShiftClauses.lean)
reach actual original clauses and twelve whole-data-state x0 stutters; actual
RV32 decoding excludes shift amounts 32 and 63. PC retirement/fetched composition
remain next.

## Shift/binop complete original fetched execution

[The short fetched-execution claim](../../Trace/Families/ShiftBinop/FetchedExecution.lean)
now derives original byte fetch/stateful decoding/preparation/retirement and exact
terminal PC/cells from actual public initialization and accepted native matching.
[Native PC equations](../../../Proofs/ShiftBinop/PC.lean) derive bounded modular
successors; actual GPR history supplies code/misa frames and decoder replay.
[All twenty-four cases and empty execution](../../../../Tests/ShiftFetched.lean)
retain exact terminal values and twelve x0 retirements. Remaining ordinary/subword,
CSR/delegation and unified protocol coverage is still separate.

## Actual native reduced context

[The regenerated reduced registry](ReducedMachine.lean) retains actual native
state/decoder columns, all three mixed/register ports and an explicit four-field
modeled setup type. [Native clock extraction](../../../Proofs/ReducedMachine/NativeTimestamp.lean)
and [exact metadata](../../../Proofs/ReducedMachine/NativeClockMetadata.lean)
discharge the shared clock contract. [Public initialized history](../../Trace/Families/ReducedMachine/History.lean)
then derives all local/prior clocks, chronology, logical Clean memory consistency
and latest reads from original public seeds and native matching. These context
definitions introduce no whole-execution dependency. Word ranges still need
proved decoded write preservation and shared range induction; original execution
and physical/protocol/terminal/init enforcement are separate.

## Actual native reduced initialized shift ranges

[Concrete native setup selection](../../Trace/Families/ReducedMachine/FixedData.lean)
lets the actual pool's numerical certificates feed proved local masked-write
preservation. [Initialized ranges](../../Trace/Families/ReducedMachine/Values.lean)
reuse shared time induction and original public seeds; [canonical source keys](../../Trace/Families/ReducedMachine/Sources.lean)
derive the native natural packing without a low-read or key premise. These are
selected-shift trace conclusions; original Sail GPR/cell execution, other combined
profiles and preprocessing/physical/protocol/terminal boundaries remain open.

## Native reduced complete numerical shift results

[The initialized result claim](../../Trace/Families/ReducedMachine/Results.lean)
now derives full canonical RV32 candidates and original-rd/x0 actual writes
from proved native source bounds, public decoding and concrete fixed-pool
acceptance. The context registry and explicit public fixture are unchanged.
No range/result/table-equivalence answer is added to the public interface.
Original Sail cell/GPR transport, numerical PC/instruction execution and
physical/setup/protocol/terminal boundaries remain separate.

## Native reduced original GPR states

[The original Sail register-history claim](../../Trace/Families/ReducedMachine/Registers.lean)
now derives every state and GPR transfer, code/misa frame, original decoder replay
and final cell matching for selected native shifts. New actual mixed-port address
proofs and x0 preservation justify shared history reuse; readonly aliases stay
in one pre-state. No per-row state/read/write or register-space answer is input.
Public cell-domain alignment stays explicit. Original operand/clause/PC execution,
other combined profiles and physical/setup/protocol boundaries remain separate.

## Native reduced original clauses

[The initialized original shift clause history](../../Trace/Families/ReducedMachine/Clauses.lean)
now executes retained Sail clauses at the actual GPR after-state. Native selected
operands, original SRAI encoding, source bounds and all read/write/state inputs
are derived; no per-row result or intermediate state is supplied. Readonly
immediate/x0 aliases remain in matching. Numerical PC/preparation/retirement
and fetched execution, other profiles and physical/setup/protocol closure remain
separate from this original-clause result.

[Selected native reduced fetched execution](../../Trace/Families/ReducedMachine/FetchedExecution.lean)
now composes original preparation/clause/retirement over native-clock-ordered
states and PC links derived by actual matching. Original public initialization,
full stateful shift decoding and aligned tracked domain are the inputs; local
states/ranges/reads/results/PC are conclusions. This selected successful four-byte
profile does not certify other combined operations or general native setup/ROM/
physical/protocol/padding/terminal/init/completeness boundaries.

[Two complete positive nonempty native traces](../../../../Tests/NativeReducedPositive.lean)
now exercise actual117-equation/22-lookup acceptance,activity,state/memory matching
and original public seed/PC/decoder construction before fetched execution. Native
clock/order/state/read/results remain derived. This concrete SLL/x0 evidence does
not certify other combined profiles or universal physical/public/setup bindings.

## Native full-domain logical token boundary

[The native ledger roots](../../Circuits/ReducedMachine/TokenLedgerTheorems.lean) bind all ordinary main/worker/public
tokens to the checked scalar product and retain exact precompression matching as
an explicit logical trust boundary. Identical inactive incoming port/state tokens
cancel only as duplicate-preserving multisets. Initialization/teardown, every worker
access and caller requests remain. [Controls](../../../../Tests/NativeTokenLedger.lean) do not establish
initialized worker history, active ranges/key refinement, fulfillment or physical
cryptographic extraction. Original initialized execution interfaces are unchanged.

## Native active main-state path

[The main-state theorem](../../Circuits/ReducedMachine/MainStateHistoryTheorems.lean) derives actual active main chronology,
clock bounds, four-tick counts and distinct0/1/2 write slots from complete native
body acceptance and the same explicit full token matching. All ordinary main rows
are considered before selecting execute1. Worker/init memory tokens and inactive
caller requests remain in their original ledgers. This is no initialized worker
memory history, CSR/MOP/Sail execution, issuance/accounting or physical extraction
claim. Original initialized execution interfaces are unchanged.

## Native adjacent initialization records

[The initialization ordering roots](../../Circuits/ReducedMachine/InitializationOrderingTheorems.lean) derive repeated adjacent
actual token-address exclusion from native ordering polynomials, complete body
remainder/borrow checks and unmasked padding. Only zero padding can repeat at
adjacent comparison positions; the last two physical rows are excluded. This
supplies no global uniqueness, address range, public seed image, initialized
worker read or physical extraction. Original initialized execution is unchanged.

## Native initialization-address pair oracles

[The same-main pair roots](../../Circuits/ReducedMachine/InitializationRangeTheorems.lean) retain all ordinary native rows and
the existing complete body, auxiliary chain, padding and adjacent ordering.
Separate base4/quartic28 observations yield the source pair equation, including
its duplicate-pole limit. Address ranges and logical lookup extraction are still
open; these local relations do not establish initialized worker reads or change
original execution.

## Complete native scalar16 family

[The same-main scalar16 roots](../../Circuits/ReducedMachine/Scalar16Theorems.lean) derive ordinary auxiliary-sum
equality and reserved-last consistency from the native polynomial divisor.
All four body pairs and the initialization-address pair remain, including every
ordinary row and pole auxiliary. Physical multiplicity/setup observations do not
yet authenticate the public scalar table or extract lookup membership. Address
bounds, combined initialized worker history and accounting remain open.

## Constructed native scalar16 lookup boundary

[The same-main constructed lookup roots](../../Circuits/ReducedMachine/Scalar16LookupTheorems.lean) retain the complete
source component and derive both initialization-address bounds from ALL actual
family queries on the constructed prefix/zero-tail table. The last normalization
value is derived symbolically. Logical lookup membership remains an explicit
cryptographic extraction boundary; no initialized worker history or accounting
is supplied, and original execution is unchanged.

## Natural initialization sorting

[Actual same-main sorting and nonpadding uniqueness](../../Circuits/ReducedMachine/InitializationSortedTheorems.lean) follow from
the existing complete source, derived full-family address ranges, native
subtraction and six padding polynomials. All ordinary rows are included; repeated
padding remains. Public windows/image/seeds and combined worker memory history
are separate obligations; original execution is unchanged.

## Public initialization endpoint binding

[All twelve actual public boundary polynomials](../../Circuits/ReducedMachine/InitializationBoundaryTheorems.lean) bind both six-field
endpoint records and derive the public address interval for every ordinary row.
The normalized last row is excluded. Cross-chunk windows, public image/seeds
and combined initialized worker history remain separate obligations.

## Native initialization windows

[Successful native windows and global nonpadding uniqueness](../../Circuits/ReducedMachine/InitializationWindowTheorems.lean) retain
the actual zero-terminal fallback and all padding records. The fallback derives
a wholly padded previous ordinary chunk. The indexed normalized batch is separate
from full main-ledger/protocol extraction, public seeds and initialized workers.

## Same-main initialization ledger

[Constructed same-main initialization views](../../Circuits/ReducedMachine/InitializationBatchTheorems.lean) retain complete main/
caller/worker arguments and the SAME full logical ledger. Bounds/order/uniqueness,
both-sided unmasked token membership and existing main chronology share one actual
proof list. Public seeds and initialized combined worker memory remain open.

## Actual native seed ledger

[Native seed domains and padding cancellation](../../Circuits/ReducedMachine/InitializationLedgerTheorems.lean) derive canonical
RAM32 zero seeds and exact duplicate-preserving matching equivalences on the same
full ledger. Six-field padding cancellation keeps active ports and every worker
access. Public domain/image/seed coverage and combined worker history remain open.

## Observed native seed domain

[Unique observed seed cells](../../Circuits/ReducedMachine/InitializationSeedDomainTheorems.lean) derive actual seed-address/cell Nodup
and exact canonical zero-token encoding on the SAME native main list. This is an
observed domain; independent public image coverage, alignment, shadow/architectural
separation and combined worker history remain separate.

## Complete native seed boundary

[Complete GPR/RAM seeds and memory matching](../../Circuits/ReducedMachine/InitializationSeedBoundaryTheorems.lean) retain all32 public
registers, x0 timestamps and all43 worker ports, deriving exact shadow partition
and memory-only matching from the SAME full ledger. Actual Sail public-image
reads and initialized combined worker memory remain open.

## Constructed original initial image

[Original Sail reads and complete native memory matching](../../Circuits/ReducedMachine/InitializationPublicImageTheorems.lean) derive
architectural initial-image reads from explicit PC/GPR/RAM inserts, preserving
the exact ROM and separate native shadows. The declared three-byte logical halo
supports unaligned RV32 cell reads. Arbitrary public-state coverage, combined
chronological worker history, keys and accounting remain open.

## Actual native main-memory history

[Actual read sources and main history](../../Circuits/ReducedMachine/NativeMemoryHistoryTheorems.lean) derive read-token provenance
for every selected worker batch, and complete Clean main-memory history when the
batch is explicitly constructed empty. The real accepted trace retains actual
seeds/teardown and all main ports. Nonempty-worker chronology, active read bounds,
keys/accounting and original CSR/MOP/worker Sail execution remain open.

## Actual active-worker clock sources

[The actual worker-clock source theorem](../../Circuits/ReducedMachine/ActiveWorkerClocksTheorems.lean) derives that any unbounded
actual read clock has an exact multiplicity-one worker-write source on the same
complete ledger. Accepted inactive workers have both raw clock limbs zero; all
worker observations remain. Active clock progress/bounds, initialized worker
reads, keys and request accounting remain open.
