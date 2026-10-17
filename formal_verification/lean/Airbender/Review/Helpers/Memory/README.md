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
Public Sail image binding and derived word bounds remain pending.
[Indirect descriptors](IndirectPorts.lean) are retained reusable definitions;
v2 batched worker arguments and indirect-port import remain pending.
