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
