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

The sections below preserve the successive decoder/table checkpoints. The current
[routing claim](Routing.lean) binds all four table tags and operand selection to
original public decoding; [lookup claims](Lookups.lean) connect the complete native
dynamic import to exact helper membership and derive all selector domains.
Numerical circuit soundness, initialized Sail execution, custom CSR/oracle
semantics and physical cryptographic enforcement remain unfinished. General
Rust/JSON/compiler refinement is a separate boundary.

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

## Native high-input SRL rows

[Two short helper claims](../../Helpers/Tables/NativeSrlHigh.lean) connect original Clean membership to all 2,097,152 actual high-input SRL rows and derive both limb bounds and exact reconstructed RV32 shifts. [Internal assembly](../../../Proofs/Tables/SrlHigh.lean) reuses native SRL-low for the entire high column and a 73-block low suffix, retaining all 146 low blocks, ten rotated templates and five symbolic prefix certificates. [Regressions](../../../../Tests/NativeSrlHigh.lean) cover cross-shift/reset edges, shifts sixteen/31, final bits and malformed queries. All four native logical-shift limb tables now have helper membership/results; dynamic constraint import and initialized shift/binop execution remain unfinished.

## Complete native dynamic lookup import

[The local artifact](Artifact.lean) now retains all fifty equations, eight timestamp
queries, the four actual witness selectors and complete native state/port/setup
metadata. [The actual tagged table](Tables/Native.lean) spans all twelve compiled
regions and 10,817,537 rows; [structural proofs](../../../Proofs/ShiftBinop/NativeLookup.lean)
retain every stored row. [Regressions](../../../../Tests/ShiftArtifact.lean) check
selector evaluation, all native metadata and explicit profile rejection.

The [CSR data](Tables/NativeCsrData.lean) uses the exact compilation-test profile:
nondeterminism enabled, empty delegation CSR list. Proving-time CSR setup binding,
custom CSR/oracle/delegation behavior, numerical family soundness and initialized
shift/binop Sail execution remain separate. Import fidelity is not a compiler
refinement proof. All previous native helper claims retain their checked scope.

## Accepted tagged-query resolution

[Short public claims](Lookups.lean) extract all four actual queries and their
canonical selectors from native Clean acceptance. [Structural partition](../../../Proofs/ShiftBinop/NativeRegions.lean)
covers every stored region and proves tag uniqueness; [resolution](../../../Proofs/ShiftBinop/NativeResolution.lean)
connects selected rows to the existing binary/scalar/logical-shift helper proofs.
Tag zero requires three zero fields. [Regressions](../../../../Tests/ShiftLookups.lean)
check valid boundaries, malformed values/tags, crossed SLL regions and field wrap.
Runtime CSR binding, operation routing and initialized family execution remain
separate. These files are task-authored v2 assembly over the already pinned data
and helper interfaces; they add no source-v3 coverage claim.

## Original public decoding and operation routing

[The short public claim](Routing.lean) derives ordinary native routing from actual
public-byte construction, native decoder membership and accepted constraints.
[References and observables](RoutingModel.lean) keep the six-bit mask, distinct
funct3 and actual four-slot order visible. [Internal assembly](../../../Proofs/ShiftBinop/Routing.lean)
derives the table tags, register/immediate operand selection and zero ordinary
request multiplicity. SRA routes truncation/sign-fill/SRL-low/SRL-high; SRAI keeps
its native funct7 immediate bits. [Complete native rows](../../../../Tests/ShiftRouting.lean)
cover all twelve forms and x0 variants, with checked original public routing and
malformed-tag/operand/CSR-bit rejection. Numerical word results, actual Sail
register reads, initialized family execution and delegation protocol soundness
remain unfinished.
