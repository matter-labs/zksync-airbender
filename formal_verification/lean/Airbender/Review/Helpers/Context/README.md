# Rows, registries and public context

This directory defines the native row/state model and the public context in which
rows are interpreted. Acceptance states actual constraint satisfaction, active-row
membership and logical state/memory permutations; boundary records bind
initialization, program, tables and configuration. Selected-row context locates a
pre-state in the same history without assuming the desired instruction result.

## Checked connections

Accepted state matching and the imported clock laws yield the native instruction
order and its connected boundary path; see
[`ordered_row_state_path`](../../../Proofs/Trace/RowHistory.lean).
The memory permutation plus unique initialization and strict timestamps yields
[complete memory histories and latest-write reads](../Memory/README.md#logical-memory-result).

[`outgoing_bounds`](PCState/Theorems.lean) proves both outgoing PC limbs bounded
under its logical interface and low-limb condition, including terminal boundaries.
[Verifier boundary](VerifierBoundary/README.md) now binds canonical typed statement
contributions to the actual imported PC-state lists. Accepted matching and
permutation cancellation derive the raw terminal bound; cryptographic enforcement
and Rust/artifact correspondence remain external. None of these
results assumes the desired row reads or an independently chosen execution order.

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
