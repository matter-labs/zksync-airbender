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
