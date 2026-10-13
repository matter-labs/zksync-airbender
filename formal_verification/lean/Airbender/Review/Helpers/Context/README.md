# Rows, registries and public context

This directory defines the native row/state model and the public context in which
rows are interpreted. Acceptance states actual constraint satisfaction, active-row
membership and logical state/memory permutations; boundary records bind
initialization, program, tables and configuration. Selected-row context locates a
pre-state in the same history without assuming the desired instruction result.

[Model](Model.lean) defines imported row interpretation, native state/memory
tokens and acceptance: actual constraints, active rows and logical permutations.
[Columns](Columns.lean), [Timestamps](Timestamps.lean) and [PCState](PCState/Model.lean)
preserve the full native encodings and clock/state boundaries.

[Registries/Pooled](Registries/Pooled.lean) admits six families with their actual
artifact layouts. The other registry modules provide family-specific trace data
and public inputs; they do not assert instruction execution.

[Boundary](Boundary.lean) binds public state/program/domain and initial clocks.
[Interfaces](Interfaces.lean) packages shared per-circuit history/table inputs.
[PooledBoundary](PooledBoundary.lean) provides physical-image and native-boot
boundaries for the integrated execution claim.

[RowContext](RowContext.lean) constructs a selected row's pre-state by applying
earlier native writes. Successful reads, operand bounds and ISA effects remain
proof conclusions. Follow [Memory](../Memory/README.md) and
[Decoder](../Decoder/README.md) for those interpretations.

Review every public field, including configuration and terminal-PC conditions.
Acceptance includes active rows; global inactive padding neutrality remains open.
These definitions do not depend on a whole-execution contract.
