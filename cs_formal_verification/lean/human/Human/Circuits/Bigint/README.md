# Bigint circuit review

This directory models limb-based 256-bit worker operations, their control
selection and indirect memory effects. The local contracts describe arithmetic,
equality and carry results together with the sixteen pointer-derived address
bindings. They interpret worker observations without claiming that every matched
caller control is valid under the full project ABI.

## Checked results

[`Memory.rv_addresses_soundness`](../../../../slop/Slop/Final/Circuits/Bigint/RVTheorems.lean) proves all sixteen native indirect
addresses from initialized accepted history, without per-row pointer bounds.
[`Native.rv_operation_execution`](../../../../slop/Slop/Final/Trace/Workers/Bigint/RVTheorems.lean) connects
the seven selected arithmetic/equality/copy effects to actual port observations.
Pointers may address any RAM cell, shadow RAM below `ROM_END` included (`RV.State.delegationRAM`).
The issued invalid-control fixture remains admitted at its stated scope.

Start with [RVTheorems](RVTheorems.lean) for native indirect-address soundness and
[RVMemory](RVMemory.lean) (with [Memory](Memory.lean)) for its model and public-history assumptions.
[Addresses](Addresses.lean) names the sixteen indirect addresses.

[Control](Control.lean), [Additive](Additive.lean), [Equality](Equality.lean),
[Multiplication](Multiplication.lean) and [Execution](Execution.lean) select
the seven operation references. [Artifact](Artifact.lean) and [`setup`](Tables/Setup.lean)
bind imported equations and modeled lookup rows.

Address correctness and native operation observations do not establish full
caller-control validity. The [bigint control fixture](../../../../test/Tests/UnifiedDelegation.lean) shows rows with x12 = 0 and no control
bit, and with x12 = 65537 and the ADD bit, accepted by the imported constraints; the pinned bigint reference rejects both.
[Shared worker context](../../Helpers/Delegation/README.md) derives reads and bounds.
[Worker execution](../../Trace/Workers/Bigint/README.md) and
[caller composition](../../Trace/Delegation/README.md) have broader, explicit scopes.
