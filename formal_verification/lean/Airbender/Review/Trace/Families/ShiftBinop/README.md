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

## Native high-input SLL rows

[Two short helper claims](../../../Helpers/Tables/NativeSllHigh.lean) connect original Clean membership to all 2,097,152 actual high-input SLL rows and derive bounds, zero low output and exact wrapped RV32 shift. [Internal assembly](../../../../Proofs/Tables/SllHigh.lean) uses six symbolic actual-block partitions, ten checked stored templates and independent bitvector arithmetic. Generic size/output proofs avoid imported-data normalization under unchanged ceilings. [Regressions](../../../../../Tests/NativeSllHigh.lean) cover discarded/final bits, shift boundaries and malformed queries. Low-input SLL, high-input SRL, dynamic constraint import and initialized family execution remain unfinished.

## Native low-input SLL rows

[Two short helper claims](../../../Helpers/Tables/NativeSllLow.lean) connect original Clean membership to all 2,097,152 actual low-input SLL rows and derive both limb bounds and exact reconstructed RV32 shifts. [Internal assembly](../../../../Proofs/Tables/SllLow.lean) reuses the complete native SLL-high low column and a checked 73-block high suffix, with six symbolic native carry partitions. [Regressions](../../../../../Tests/NativeSllLow.lean) cover first carry, shifts sixteen/31, surviving/discarded bits and malformed queries. High-input SRL, dynamic constraint import and initialized family execution remain unfinished.

## Native high-input SRL rows

[Two short helper claims](../../../Helpers/Tables/NativeSrlHigh.lean) connect original Clean membership to all 2,097,152 actual high-input SRL rows and derive both limb bounds and exact reconstructed RV32 shifts. [Internal assembly](../../../../Proofs/Tables/SrlHigh.lean) reuses native SRL-low for the entire high column and a 73-block low suffix, retaining all 146 low blocks, ten rotated templates and five symbolic prefix certificates. [Regressions](../../../../../Tests/NativeSrlHigh.lean) cover cross-shift/reset edges, shifts sixteen/31, final bits and malformed queries. All four native logical-shift limb tables now have helper membership/results; dynamic constraint import and initialized shift/binop execution remain unfinished.

## Native dynamic import prerequisite

[The complete local artifact](../../../Circuits/ShiftBinop/Artifact.lean) now retains
all four selector witnesses as tagged Clean query fields. [Every actual table region](../../../Circuits/ShiftBinop/Tables/Native.lean)
is retained with its native offset, including the explicitly scoped compilation
CSR fixture. [Structural proofs](../../../../Proofs/ShiftBinop/NativeLookup.lean) cover
all stored rows; [regressions](../../../../../Tests/ShiftArtifact.lean) check metadata
and selector preservation. This supplies the next numerical-family prerequisite;
initialized shift/binop history/execution and runtime CSR binding remain open.
