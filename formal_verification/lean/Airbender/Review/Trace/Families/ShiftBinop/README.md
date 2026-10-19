# Shift/binop trace guide

[The public decoder-data certificate](NativeDecoder.lean) proves that actual
native preprocessing/materialization agrees with independently read public
bytes and original Sail decoding across the complete million-row capacity.
Its fixed fixture covers twelve ordinary forms, their original x0 destinations
and an unsupported ADD hole. No table-equality premise is supplied.

[Internal proof assembly](../../../../Proofs/ShiftBinop/NativeSetup.lean) reuses
existing sparse setup and structural compressed-tail proofs. [Regressions](../../../../../Tests/ShiftDecoder.lean)
check every original decode, native x0 flags, full immediate limbs, encoded SRAI,
unsupported constructors and retained sentinel padding.

Dynamic constraint/table import and exact native membership are the next
checkpoint. Numerical soundness, initialized history, original instruction
retirement and complete fetched execution remain unfinished for this family.
The exporter uses an empty CSR allow-list; custom CSR/oracle semantics and
general Rust/compiler/cryptographic refinement remain separate.

## Native zero and binary rows

[The table helper claims](../../../Helpers/Tables/NativeBinary.lean) now certify the actual native zero/XOR/OR/AND prefix, all binary outputs and exact original Clean membership. [Internal assembly](../../../../Proofs/Tables/Binary.lean) derives byte bounds/results from actual native data, with [malformed-query regressions](../../../../../Tests/NativeBinary.lean). Large 16-bit shifts and dynamic constraint import are next; initialized history, original retirement and fetched shift/binop execution remain open.

## Native shift scalar and sign-fill tables

[The short helper claims](../../../Helpers/Tables/NativeShiftScalars.lean) now connect actual native truncation, zero-padded range and every sign-fill row to original Clean membership and exact results, including negative shift zero. [Internal assembly](../../../../Proofs/Tables/ShiftScalars.lean) uses structural constant-block geometry across 64 symbolic domains and independent RV32 mask arithmetic. [Regressions](../../../../../Tests/NativeShiftScalars.lean) check boundary cases and malformed queries. Native compiled offsets retain unexported regions. The four large logical-shift tables, dynamic constraint import and initialized family execution remain unfinished.
