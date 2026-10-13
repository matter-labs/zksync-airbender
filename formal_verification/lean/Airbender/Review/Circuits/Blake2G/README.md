# BLAKE2 G circuit review

This directory models one G mixing operation: four state words and two message
words produce four updated state words under the imported controller and port
encoding. The observable relation uses Clean's original G function.
Address/control contracts and a local bounded-word interface are distinct from
executing a complete work-vector protocol.

Start with [Theorems](Theorems.lean) and [Model](Model.lean) for one G mixing
operation. The reference reuses Clean's original G, shared by BLAKE2s and BLAKE3;
the local claim is not complete compression.

The local model explicitly retains four input-word bounds. Integrated worker
history derives the operation bounds through [Memory](Memory.lean); keep those
two interfaces distinct.

[Artifact](Artifact.lean), [Row](Row.lean), [Addresses](Addresses.lean) and
[Execution](Execution.lean) name imported controls, ports and effects.
[Controller](Controller.lean) describes behavior;
[controller rows](Tables/Controller.lean) and [setup](Tables/Setup.lean) are modeled tables.
[Protocol](Protocol.lean) fixes the complete-span constants.

[Shared worker context](../../Helpers/Delegation/README.md) provides initialized matching.
[Worker spans](../../Trace/Workers/Blake2G/README.md) own complete work-vector
execution; caller preparation/chaining and whole mixed retirement remain separate.
