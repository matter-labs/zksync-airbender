# Extended BLAKE circuit review

This directory models the phase-dependent extended-BLAKE worker, including
preparation, message selection, eight G updates and chaining/finalization
behavior. Row, control and address contracts identify the selected phase and its
memory effects. Complete seven-/ten-round compression is a sequence-level
statement in the worker Trace directory.

Start with [Artifact](Artifact.lean), [Row](Row.lean) and [Execution](Execution.lean)
for the imported operation view. Follow [Preparation](Preparation.lean),
[Mixing](Mixing.lean) and [Finalization](Finalization.lean) for the worker phases.

[Control](Control.lean), [Schedule](Schedule.lean) and [setup](Tables/Setup.lean)
describe controller flags, round selection and modeled lookup contents.
[Addresses](Addresses.lean) and [Memory](Memory.lean) connect native indirect ports
to initialized worker history.

There is no local Theorems module here: the public complete-compression claims
live in [worker execution](../../Trace/Workers/Blake2Round/README.md). Review their
public flags, seven-/ten-round scope, fixed pointers, actual reads and terminal binding.
The completion control does not automatically restart a new protocol.
[Delegation context](../../Helpers/Delegation/README.md) and selected unified
windows retain their own matching, table and prefix conditions.
