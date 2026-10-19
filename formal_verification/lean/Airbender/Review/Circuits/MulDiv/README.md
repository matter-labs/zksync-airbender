# Unsigned MUL/DIV circuit review

## Checked results

[Artifact](Artifact.lean) retains all native v2 equations and 20 lookups,
including six three-column byte-pair queries covering eleven byte columns.
Its trace/port/decoder/setup metadata comes from the same pinned layout.
Table ID eight, its full 65,536-row extent and offset zero are retained.
Optimized-out variables carry scratch metadata and cannot be consumed.

[Actual exported data](../../Helpers/Tables/NativeSmallRangeData.lean) comes
from the pinned native table driver. [The symbolic certificate](../../../Proofs/MulDiv/SmallRange.lean)
checks every row and its tag, connecting the original Clean lookup to actual
exported membership without an equivalence premise. [Native byte bounds](../../../Proofs/MulDiv/ByteBounds.lean)
are derived from those exact queries, with no supplied numerical ranges.
[Regressions](../../../../Tests/MulDivArtifact.lean) retain endpoint membership
and reject overflow, nonzero padding and wrong tags; importer mutations cover
query omissions/order, scratch uses and native table geometry.

[The numerical theorem](Theorems.lean) now proves all four unsigned results,
including zero divisors and the actual masked destination write. Review
[the operation/observable definitions](Model.lean), then its explicit accepted
constraints, packed mask, input register limb bound and destination-zero flag.
Every intermediate/output bound comes from native constraints. [Product](../../../Proofs/MulDiv/Product.lean),
[division](../../../Proofs/MulDiv/Division.lean) and [result assembly](../../../Proofs/MulDiv/Results.lean)
keep byte-column calculations, Mersenne31 inverse 32768, strict remainder bounds,
zero-divisor behavior and both actual write limbs outside the public claim.

[Forty full local assignments](../../../../Tests/MulDivWitness.lean) cover five
boundary operand pairs and both write modes for [MUL](../../../../Tests/MulDivMul.lean),
[MULHU](../../../../Tests/MulDivMulhu.lean), [DIVU](../../../../Tests/MulDivDivu.lean)
and [REMU](../../../../Tests/MulDivRemu.lean). Each checks all native constraints,
applies the public numerical claim and rejects an altered actual write.

[Original public decoding](Decoder.lean), initialized history and derived numerical
interfaces are now checked in [the trace guide](../../Trace/Families/MulDiv/README.md).
Actual stateful Sail decoding retains misa.M and original x0 instructions.
Original Sail operation execution, preparation/retirement and fetched traces remain open.
The row interfaces are not assumed trace results. No v3 semantic theorem is
promoted without its checked v2 connection. Rust/JSON/compiler refinement,
physical argument enforcement and completeness remain separate boundaries.
Follow the [plan](../../../../FORMAL_VERIFICATION_PLAN.md).

## Original Sail register connection

[The public register-history claim](../../Trace/Families/MulDiv/Registers.lean) now derives original same-pre-state reads, actual masked writes and every segment state. Actual code/misa frames replay the original stateful decoder. Original MUL/DIV operation clauses and PC retirement remain separate.

## Original local execution and PC retirement

[Original constructor/clause dispatch](Sail.lean) retains all four opcodes and x0 destinations. [The short trace claim](../../Trace/Families/MulDiv/Execution.lean) derives their actual local preparation/retirement from initialized native histories. [Clause calculations](../../../Proofs/MulDiv/Clauses.lean) reuse pinned source arithmetic proofs; [native PC gates](../../../Proofs/MulDiv/PC.lean) retain aligned RV32 rollover. Complete fetched composition remains separate.
