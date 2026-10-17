# Memory helper review

[Ports](Ports.lean) preserves the shared address/value/timestamp interpretation.
Native v2 direct shuffle-RAM ports use two 16-bit words; their metadata is
[resolved from physical columns](../../../Import/Parse.lean) and retained by the
[ADD/SUB artifact](../../Circuits/AddSub/Artifact.lean). The actual destination
write maps to logical variables 37/38, separately from its old value and raw hint.

Importing a descriptor does not establish initialized latest-write consistency.
[Indirect descriptors](IndirectPorts.lean) are retained reusable definitions;
v2 batched worker arguments and indirect-port import remain pending.
