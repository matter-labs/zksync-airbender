# Rows, registries and public context

This directory defines the native row/state model and the public context in which
rows are interpreted. Acceptance states actual constraint satisfaction, active-row
membership and logical state/memory permutations; boundary records bind
the public initial `RV.State`, program and tables. Selected-row context locates a
pre-state in the same history without assuming the desired instruction result.

## Checked connections

Accepted state matching and the imported clock laws yield the native instruction
order and its connected boundary path; see
[`ordered_row_state_path`](../../../../proven/Proven/Trace/RowHistory.lean).
The memory permutation plus unique initialization and strict timestamps yields
[complete memory histories and latest-write reads](../Memory/README.md#logical-memory-result).

[`outgoing_bounds`](../../../../proven/Proven/Final/Helpers/Context/PCState/Theorems.lean) proves both outgoing PC limbs bounded
under its logical interface and low-limb condition, including terminal boundaries.
Binding that interface to standalone jump teardown remains open. None of these
results assumes the desired row reads or an independently chosen execution order.

[Model](Model.lean) defines imported row interpretation, native state/memory
tokens and acceptance: actual constraints, active rows and logical permutations.
[FamilyLayout](FamilyLayout.lean) registers the restricted ADD/SUB + word-memory scope's
artifacts; it is kept apart so that only modules using those artifacts rebuild when they change.
[Columns](Columns.lean), [Timestamps](Timestamps.lean) and [PCState](PCState/Model.lean)
preserve the full native encodings and clock/state boundaries.

[Registries/Pooled](Registries/Pooled.lean) admits six families with their actual
artifact layouts. The other registry modules provide family-specific trace data
and public inputs; they do not assert instruction execution.

[RVBoundary](RVBoundary.lean) binds the public `RV.State`, program table (`RV.read`, `RV.decode`),
tracked cells and initial clocks (`RVNativeInputs`); there is no machine-configuration premise.
[RVInterfaces](RVInterfaces.lean) packages the shared per-circuit history/table inputs
(`RVPooledHistoryInputs`: initialization and the two modeled ROM tables built from the ROM image).
[RVPooledBoundary](RVPooledBoundary.lean) provides the native-boot boundary of the integrated execution
claim (`RVPooledBootInputs`: seeds from the inits/teardowns circuit, terminal-PC condition).

[RowContext](RowContext.lean) and [RVRowContext](RVRowContext.lean) construct a selected row's
`RV.State` pre-state by applying earlier native writes (a RAM write stores four bytes in RAM at any address,
shadow RAM below `ROM_END` included, and never changes the ROM image). Successful reads, operand bounds and ISA effects remain
proof conclusions. Follow [Memory](../Memory/README.md) and
[Decoder](../Decoder/README.md) for those interpretations.

Review every public field, including the terminal-PC condition.
Acceptance includes active rows; global inactive padding neutrality remains open.
These definitions do not depend on a whole-execution contract.
