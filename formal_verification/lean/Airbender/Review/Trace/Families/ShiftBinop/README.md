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

## Native low-input SRL rows

[Two short helper claims](../../../Helpers/Tables/NativeSrlLow.lean) identify actual native SRL-low membership with original Clean semantics and derive bounds, zero high output and exact RV32 logical shift for all 2,097,152 rows. [Internal assembly](../../../../Proofs/Tables/SrlLow.lean) reuses the source block checker with six symbolic actual-block certificates and independent bitvector arithmetic. [Regressions](../../../../../Tests/NativeSrlLow.lean) cover shift/final-bit boundaries and malformed queries. The other three logical-shift tables, dynamic constraint import and initialized family execution remain unfinished.
