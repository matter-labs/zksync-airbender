# BLAKE2 G circuit review

This directory models one G mixing operation: four state words and two message
words produce four updated state words under the imported controller and port
encoding. The observable relation uses Clean's original G function.
Address/control contracts and a local bounded-word interface are distinct from
executing a complete work-vector protocol.

## Checked results

The [local soundness claims](Theorems.lean) prove the four-word output equals
Clean's original G under the imported native controller and four operand bounds.
The [integrated worker claim](../../Trace/Workers/Blake2G/Theorems.lean)
derives operation bounds and actual reads/writes from initialized accepted history.
Its complete-span claims bind the 56/80-call work-vector fold and terminal tokens;
that is broader than the local G calculation.

Start with [Theorems](Theorems.lean) and [Model](Model.lean) for one G mixing
operation. The reference reuses Clean's original G, shared by BLAKE2s and BLAKE3;
the local claim is not complete compression.

The local model explicitly retains four input-word bounds. Integrated worker
history derives the operation bounds through [Memory](Memory.lean); keep those
two interfaces distinct.

[Artifact](Artifact.lean), [Row](Row.lean), [Addresses](Addresses.lean) and
[Execution](Execution.lean) name imported controls, ports and effects.
[Controller](Controller.lean) describes behavior. [Controller rows](Tables/Controller.lean)
project the actual [native JSON region](Tables/ControllerData.lean);
[kernel proofs](../../../Proofs/Blake2G/ImportedController.lean) check all 512 keys,
seven outputs and discriminator against the reference and the concrete setup rows.
The generalized [`setup`](Tables/Setup.lean) still accepts arbitrary controllers;
its XOR regions remain modeled pending their table migration.
[Protocol](Protocol.lean) fixes the complete-span constants.

[Shared worker context](../../Helpers/Delegation/README.md) provides initialized matching.
[Worker spans](../../Trace/Workers/Blake2G/README.md) own complete work-vector
execution; caller preparation/chaining and whole mixed retirement remain separate.

[Complete reference micro-calls](Call.lean) now read the actual x10/x11/x12 and
selected operands, use the existing pure controller/address/G references, and
execute the exact Sail writes with their full frame. The valid counter range
is part of the existing successful complete-span protocol.
[Full-state span execution](../../Trace/Workers/Blake2G/ReferenceCalls.lean)
derives that counter, pointer ABI and every operand from the accepted initialized
span; no per-row valid-control, pointer or expected-output premise is added.
Mixed instruction fetch/PC retirement and global request participation stay separate.
