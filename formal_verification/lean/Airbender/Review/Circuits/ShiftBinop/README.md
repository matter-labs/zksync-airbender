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

## Native shift scalar and sign-fill tables

[The short helper claims](../../Helpers/Tables/NativeShiftScalars.lean) now connect actual native truncation, zero-padded range and every sign-fill row to original Clean membership and exact results, including negative shift zero. [Internal assembly](../../../Proofs/Tables/ShiftScalars.lean) uses structural constant-block geometry across 64 symbolic domains and independent RV32 mask arithmetic. [Regressions](../../../../Tests/NativeShiftScalars.lean) check boundary cases and malformed queries. Native compiled offsets retain unexported regions. The four large logical-shift tables, dynamic constraint import and initialized family execution remain unfinished.

## Native low-input SRL rows

[Two short helper claims](../../Helpers/Tables/NativeSrlLow.lean) identify actual native SRL-low membership with original Clean semantics and derive bounds, zero high output and exact RV32 logical shift for all 2,097,152 rows. [Internal assembly](../../../Proofs/Tables/SrlLow.lean) reuses the source block checker with six symbolic actual-block certificates and independent bitvector arithmetic. [Regressions](../../../../Tests/NativeSrlLow.lean) cover shift/final-bit boundaries and malformed queries. The other three logical-shift tables, dynamic constraint import and initialized family execution remain unfinished.

## Native high-input SLL rows

[Two short helper claims](../../Helpers/Tables/NativeSllHigh.lean) connect original Clean membership to all 2,097,152 actual high-input SLL rows and derive bounds, zero low output and exact wrapped RV32 shift. [Internal assembly](../../../Proofs/Tables/SllHigh.lean) uses six symbolic actual-block partitions, ten checked stored templates and independent bitvector arithmetic. Generic size/output proofs avoid imported-data normalization under unchanged ceilings. [Regressions](../../../../Tests/NativeSllHigh.lean) cover discarded/final bits, shift boundaries and malformed queries. Low-input SLL, high-input SRL, dynamic constraint import and initialized family execution remain unfinished.

## Native low-input SLL rows

[Two short helper claims](../../Helpers/Tables/NativeSllLow.lean) connect original Clean membership to all 2,097,152 actual low-input SLL rows and derive both limb bounds and exact reconstructed RV32 shifts. [Internal assembly](../../../Proofs/Tables/SllLow.lean) reuses the complete native SLL-high low column and a checked 73-block high suffix, with six symbolic native carry partitions. [Regressions](../../../../Tests/NativeSllLow.lean) cover first carry, shifts sixteen/31, surviving/discarded bits and malformed queries. High-input SRL, dynamic constraint import and initialized family execution remain unfinished.
