# Shared helper review

[Properties](Properties.lean) defines soundness, completeness and the observable
circuit model independently of any decoder/history claim. [Core](Core/README.md)
contains reused word and original Sail definitions; [tables](Tables/README.md)
states the current range-table boundary. [Context](Context/README.md) exposes
clock contracts and native logical matching; [decoder](Decoder/README.md) exposes
the native ten-column query; [memory](Memory/README.md) exposes
port interpretation and initialized history. Their definitions remain independent
of public whole-execution claims.

[Native mul/div arithmetic](../Circuits/MulDiv/README.md) reuses the unchanged
shared [integer byte-column theorem](../../Proofs/Arithmetic/Multiplication.lean).
Its v2 circuit connection derives all byte, carry and output bounds from actual
queries/assertions; the existing word and logical-history definitions are
unchanged. Original Sail execution is still a separate connection for this family.

## Unsigned MUL/DIV helpers

[Stateful public setup](Decoder/StatefulSetup.lean) retains actual extension-configuration reads. [The native context](Context/MulDiv.lean) and [full decoder membership](Decoder/MulDiv.lean) feed the [initialized trace claims](../Trace/Families/MulDiv/README.md).
