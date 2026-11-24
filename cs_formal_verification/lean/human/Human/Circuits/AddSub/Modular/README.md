# Modular ADD/SUB operations

[Model.lean](Model.lean) defines the four modular opcodes, their native selector
columns, Montgomery arithmetic, public input words and witness mappings.
Its interface states participation, selector values and initial-PC bounds.

This directory has no separate claim. The
[machine targets](../../../Compiler/NativeTargets.lean) state whole-run execution.
The kernel checks the arithmetic and RV correspondence used by their proofs.
Input mappings and interface premises are part of the reviewed spec. The
[ADD/SUB guide](../README.md) states the circuit import boundary and row scope.
