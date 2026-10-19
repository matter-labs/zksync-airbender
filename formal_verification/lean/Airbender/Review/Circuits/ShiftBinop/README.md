# Shift/binop review guide

Start with [the original-constructor projection](Decoder.lean), [literal native
export/public fixture](NativeData.lean), then the [short data certificate](../../Trace/Families/ShiftBinop/NativeDecoder.lean).
The certificate covers twelve ordinary register/immediate forms, their original
x0 variants, an unsupported ADD hole and every native decoder row.

[Internal assembly](../../../Proofs/ShiftBinop/NativeSetup.lean) reads public
bytes, runs original Sail decoding and proves the actual compressed padding
structurally through [the constant-tail helper](../../../Proofs/Tables/ConstantTail.lean).
[Concrete regressions](../../../../Tests/ShiftDecoder.lean) check original x0,
full 16-bit signed immediate limbs, SRAI funct7 payload and unsupported forms.
[Strict importer regressions](../../../../Tests/ArtifactImport.lean) keep the
native profile separate from arithmetic/control exports.

This directory currently certifies decoder data only. The native compiled
circuit still requires dynamic table-selector import and exact large-table
membership. Its import remains rejected; circuit soundness, initialized Sail
execution, custom CSR/oracle semantics and physical cryptographic enforcement
are unfinished. General Rust/JSON/compiler refinement is a separate boundary.

## Native binary table prerequisite

[Two short helper claims](../../Helpers/Tables/NativeBinary.lean) now connect actual native XOR/OR/AND rows to original Clean membership and bytewise semantics, retaining the actual conditional zero row and native offsets. [Internal assembly](../../../Proofs/Tables/Binary.lean) reuses full literal-block source output certificates and structural geometry; [regressions](../../../../Tests/NativeBinary.lean) check complete native data and reject malformed keys/results. This does not import the compiled circuit: dynamic selectors, large 16-bit shift tables, custom CSR/oracle semantics and initialized family execution remain unfinished.
