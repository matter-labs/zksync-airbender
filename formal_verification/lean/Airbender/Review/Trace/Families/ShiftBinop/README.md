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
