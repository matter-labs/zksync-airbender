# Shared helper review

[Properties](Properties.lean) defines soundness, completeness and the observable
circuit model independently of any decoder/history claim. [Core](Core/README.md)
contains reused word and original Sail definitions; [tables](Tables/README.md)
states the current range-table boundary. [Context](Context/README.md) exposes
clock contracts; [memory](Memory/README.md) exposes native port interpretation.
Shared initialized history will be backported before whole-trace claims are added.
