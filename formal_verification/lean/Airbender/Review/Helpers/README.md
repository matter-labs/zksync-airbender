# Shared helper review

[Properties](Properties.lean) defines soundness, completeness and the observable
circuit model independently of any decoder/history claim. [Core](Core/README.md)
contains reused word and original Sail definitions; [tables](Tables/README.md)
states the current range-table boundary. [Context](Context/README.md) exposes
clock contracts and native logical matching; [memory](Memory/README.md) exposes
port interpretation and initialized history. Their definitions remain independent
of public whole-execution claims.
