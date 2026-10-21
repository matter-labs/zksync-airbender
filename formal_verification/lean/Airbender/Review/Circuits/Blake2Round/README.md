# Extended BLAKE circuit review

This directory models the phase-dependent extended-BLAKE worker, including
preparation, message selection, eight G updates and chaining/finalization
behavior. Row, control and address contracts identify the selected phase and its
memory effects. Complete seven-/ten-round compression is a sequence-level
statement in the worker Trace directory.

## Checked results

[`Native.operation_execution`](../../Trace/Workers/Blake2Round/Theorems.lean)
proves the selected row's preparation, eight-G mixing, chaining/control and
address effects on actual port values. Its standalone operation inputs retain
the exclusive mask ABI. Complete compression and native-window claims bind actual
initial/final blocks; the prepared unified scope additionally derives masks
from accepted public LUI preparation and matching.

The [native control proof](../../../Proofs/Blake2Round/ExclusiveMask.lean) also
characterizes the mask boundary in both directions: an exclusive round mask is
equivalent to a high control limb equal to flags below eight plus `8 * 2^round`.
Only imported control assertions and Boolean bits are used; no XOR-table semantics
or supported-mask premise is supplied. Zero and multibit encodings remain outside
that ABI. The [unified unissued-worker entry](../../Trace/UnifiedReduced/UnissuedWorkers.lean)
binds this classification to the actual public x12 seed, without proving worker
exclusion or inertness.

Start with [Artifact](Artifact.lean), [Row](Row.lean) and [Execution](Execution.lean)
for the imported operation view. Follow [Preparation](Preparation.lean),
[Mixing](Mixing.lean) and [Finalization](Finalization.lean) for the worker phases.

[Control](Control.lean), [Schedule](Schedule.lean) and [`setup`](Tables/Setup.lean)
describe controller flags, round selection and imported lookup contents.
The [fixed rows](Tables/XorData.lean) come from this circuit's own artifact;
[kernel proofs](../../../Proofs/Blake2Round/ImportedXor.lean) check their connection
to the shared XOR semantics and native fields.
The [native layout adapter](../../../Proofs/Blake2Round/NativeLayout.lean) reads
both G phases into a [shared arithmetic frame](../../../Proofs/Blake2G/Frame.lean).
Chunk and rotation proofs use lookup evidence alone; native carry, input and
writeback projections stay in the adapter modules.
[Addresses](Addresses.lean) and [Memory](Memory.lean) connect native indirect ports
to initialized worker history.

There is no local Theorems module here: the public complete-compression claims
live in [worker execution](../../Trace/Workers/Blake2Round/README.md). Review their
public flags, seven-/ten-round scope, fixed pointers, actual reads and terminal binding.
The completion control does not automatically restart a new protocol.
[Delegation context](../../Helpers/Delegation/README.md) and selected unified
windows retain their own matching, table and prefix conditions.

[Complete round calls](Call.lean) connect the existing pure round reference to
actual pre-state controller/pointer/operand reads and the exact 43 Sail writes,
including the full frame. The successful ABI couples all mode flags to the full
x12 word and the admitted round. [Full-state span execution](../../Trace/Workers/Blake2Round/ReferenceCalls.lean)
derives that ABI, canonical RAM pointers and all operands from the existing
seven-/ten-round public protocol and initialized history. No new per-row valid
controller, pointer, expected output or reference-execution premise is added.
Mixed caller fetch/PC retirement and total participation remain separate.
