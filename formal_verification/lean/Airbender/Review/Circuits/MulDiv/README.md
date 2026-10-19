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

MUL/MULHU/DIVU/REMU arithmetic, zero-divisor behavior, native x0 handling,
original public decoding, initialized history and Sail execution remain open.
No v3 semantic theorem is promoted by this artifact checkpoint. Rust/JSON/
compiler refinement, full physical argument enforcement and completeness remain
separate boundaries. Follow the [plan](../../../../FORMAL_VERIFICATION_PLAN.md).
