# Bigint circuit review

This directory models limb-based 256-bit worker operations, their control
selection and indirect memory effects. The local contracts describe arithmetic,
equality and carry results together with the sixteen pointer-derived address
bindings. They interpret worker observations without claiming that every matched
caller control is valid under the full project ABI.

## Checked results

[`Memory.addresses_soundness`](Theorems.lean) proves all sixteen native indirect
addresses from initialized accepted history, without per-row pointer bounds.
The [shared pointer ABI](PointerABI.lean) derives canonical, aligned, distinct RAM
bases under its public tracked-domain conditions.
[`Native.operation_execution`](../../Trace/Workers/Bigint/Theorems.lean) connects
the seven selected arithmetic/equality/copy effects to actual port observations.
The issued invalid-control and ROM-shadow fixtures remain admitted at their stated scope.

Start with [Theorems](Theorems.lean) for native indirect-address soundness and
[Memory](Memory.lean) for its model and public-history assumptions.
[Addresses](Addresses.lean) and [PointerABI](PointerABI.lean) name the sixteen
indirect addresses and shared aligned/RAM pointer claim.

[Control](Control.lean), [Additive](Additive.lean), [Equality](Equality.lean),
[Multiplication](Multiplication.lean) and [Execution](Execution.lean) select
the seven operation references. [Artifact](Artifact.lean) and [setup](Tables/Setup.lean)
bind imported equations and actual native setup rows. The six fixed-table
regions come from [setup JSON](../../../../artifacts/setup/README.md); their exact
carry-range and low-byte meanings are proved in
[ImportedSetup](../../../Proofs/Bigint/ImportedSetup.lean), then used by the existing
lookup and multiplication proofs. No row-equivalence premise is added.

Address correctness and native operation observations do not establish full
caller-control validity. Issued public controls 0 and 65537 remain checked
counterexamples to the pinned bigint reference ABI; worker ROM shadows remain separate.
[Shared worker context](../../Helpers/Delegation/README.md) derives reads and bounds.
[Worker execution](../../Trace/Workers/Bigint/README.md) and
[caller composition](../../Trace/Delegation/README.md) have broader, explicit scopes.

[Complete successful calls](Call.lean) now bind the actual pre-state x10/x11/x12 and
both canonical RAM operands to the existing seven reference operations. Atomic
Sail cell writes specify the complete post-state and frame; the original Sail
PC preparation/tick supplies retirement. No native assignment appears in this
reference relation. [Mixed caller soundness](../../Trace/UnifiedReduced/BigintCalls.lean)
derives it from accepted constraints, initialized history and the derived pointer
ABI under the explicit lower-level valid-command contract. Controls 0/65537
remain accepted by the original relation and are rejected by this full reference.
