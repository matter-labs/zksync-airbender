# Extended BLAKE circuit review

This directory models the phase-dependent extended-BLAKE worker, including
preparation, message selection, eight G updates and chaining/finalization
behavior. Row, control and address contracts identify the selected phase and its
memory effects. Complete seven-/ten-round compression is a sequence-level
statement in the worker Trace directory.

## Checked results

[`Native.rv_operation_execution`](../../../../proven/Proven/Final/Trace/Workers/Blake2Round/RVTheorems.lean)
proves the selected row's preparation, eight-G mixing, chaining/control and
address effects on actual port values. Its standalone operation inputs retain
the exclusive mask ABI. Complete compression and native-window claims bind actual
initial/final blocks; the prepared unified scope additionally derives masks
from accepted public LUI preparation and matching.

Start with [Artifact](Artifact.lean), [Row](Row.lean) and [Execution](Execution.lean)
for the imported operation view. Follow [Preparation](Preparation.lean),
[Mixing](Mixing.lean) and [Finalization](Finalization.lean) for the worker phases.

[Control](Control.lean), [Schedule](Schedule.lean) and [`setup`](Tables/Setup.lean)
describe controller flags, round selection and the lookup table, read from the
exported setup data (`artifacts/setup/blake-round.json`).
[Addresses](Addresses.lean) and [Memory](Memory.lean) connect native indirect ports
to initialized worker history.

There is no local Theorems module here: the public complete-compression claims
live in [worker execution](../../Trace/Workers/Blake2Round/README.md). Review their
public flags, seven-/ten-round scope, fixed pointers, actual reads and terminal binding.
The completion control does not automatically restart a new protocol.
[Delegation context](../../Helpers/Delegation/README.md) and selected unified
windows retain their own matching, table and prefix conditions.

[Mask.lean](Mask.lean) states the full native Boolean-mask behavior.
`Airbender.Blake2Round.Mask.SoundnessClaim` covers zero and multiple selected rounds.
`Airbender.Blake2Round.Mask.SatisfiableClaim` gives a separate assignment witness.
The [final proofs](../../../../proven/Proven/Final/Circuits/Blake2Round/Mask.lean) reuse the existing indexed arithmetic, XOR and address lemmas.
The message limbs can contain sums of ten source limbs.
