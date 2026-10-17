# Memory helper review

[Ports](Ports.lean) preserves the shared address/value/timestamp interpretation.
Native v2 direct shuffle-RAM ports use two 16-bit words; their metadata is
[resolved from physical columns](../../../Import/Parse.lean) and retained by the
[ADD/SUB artifact](../../Circuits/AddSub/Artifact.lean). The actual destination
write maps to logical variables 37/38, separately from its old value and raw hint.

[History](History.lean) preserves the source's explicit initialization writes and
native transfer events. [Row/token acceptance](../Context/Model.lean) compares
actual native address/time/value tokens, preserving raw field limbs injectively.
The checked [trace claim](../../Trace/History.lean) constructs complete Clean
online consistency and newest preceding reads from matching, initial clock
boundaries and unique seed addresses. No expected read value is supplied.
[Initial image](InitialImage.lean) and [public boundary](PublicImage.lean) now bind
seed values and initial PC to actual Sail reads; missing data rejects construction.
[Image proofs](../../../Proofs/Trace/InitialImage.lean) are copied unchanged and
derive seed bounds, zero clocks, address injectivity and read-state preservation.
[Value proofs](../../../Proofs/Trace/Values.lean) now derive native read/write/terminal
word bounds using initialized history and the decoded zero flag.
The same public seed boundary and generic history induction now support the
[word-memory registry](../../Trace/Families/WordMemory/History.lean), including
all native mixed ports and discarded shadow reads. Its
[write rules](../../../Proofs/Trace/Families/WordMemory/Values.lean) preserve ranges
through RAM copies, ROM data selection and actual x0-masked writes. Architectural
ROM-shadow projection remains separate.
[Sail history](SailHistory.lean) retains the shared actual-read/write representation;
[its proof](../../../Proofs/Trace/SailHistory.lean) derives all intermediate states
from Clean consistency and public seeds. V2 masked writes preserve x0; public
RAM alignment supplies byte-window disjointness. [Grouped row reads/writes](../../../Proofs/Trace/PortReads.lean)
transport actual Sail accesses, including readonly alias stutters.
The [word-memory instance](../../Trace/Families/WordMemory/SailHistory.lean) now
uses the same realization/grouping with checked mixed-port x0 preservation. It
recovers actual source-register reads, RAM/register writes and intermediate
states for the full supplied native cell image. Architectural ROM-shadow
projection remains separate. Instruction
execution and physical zero-boot/ROM interpretation remain pending.
[Indirect descriptors](IndirectPorts.lean) are retained reusable definitions;
v2 batched worker arguments and indirect-port import remain pending.
