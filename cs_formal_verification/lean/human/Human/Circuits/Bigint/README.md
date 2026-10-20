# Bigint circuit review

This directory models limb-based 256-bit worker operations, their control
selection and indirect memory effects. The local contracts describe arithmetic,
equality and carry results together with the sixteen pointer-derived address
bindings. They interpret worker observations without claiming that every matched
caller control is valid under the full project ABI.

## Checked results

[`Memory.addresses_soundness`](../../../../slop/Slop/Final/Circuits/Bigint/Theorems.lean) proves all sixteen native indirect
addresses from initialized accepted history, without per-row pointer bounds.
The [shared pointer ABI](PointerABI.lean) derives canonical, aligned, distinct RAM
bases under its public tracked-domain conditions.
[`Native.operation_execution`](../../../../slop/Slop/Final/Trace/Workers/Bigint/Theorems.lean) connects
the seven selected arithmetic/equality/copy effects to actual port observations.
The issued invalid-control and ROM-shadow fixtures remain admitted at their stated scope.

Start with [Theorems](../../../../slop/Slop/Final/Circuits/Bigint/Theorems.lean) for native indirect-address soundness and
[Memory](Memory.lean) for its model and public-history assumptions.
[Addresses](Addresses.lean) and [PointerABI](PointerABI.lean) name the sixteen
indirect addresses and shared aligned/RAM pointer claim.

[Control](Control.lean), [Additive](Additive.lean), [Equality](Equality.lean),
[Multiplication](Multiplication.lean) and [Execution](Execution.lean) select
the seven operation references. [Artifact](Artifact.lean) and [`setup`](Tables/Setup.lean)
bind imported equations and modeled lookup rows.

Address correctness and native operation observations do not establish full
caller-control validity. Issued public controls 0 and 65537 remain checked
counterexamples to the pinned bigint reference ABI; worker ROM shadows remain separate.
[Shared worker context](../../Helpers/Delegation/README.md) derives reads and bounds.
[Worker execution](../../Trace/Workers/Bigint/README.md) and
[caller composition](../../Trace/Delegation/README.md) have broader, explicit scopes.
