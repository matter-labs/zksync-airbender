# Native lookup selectors

Each family module lists the native group, gate, operand and expansion path of
every lookup selector. Start with [AddSub.lean](AddSub.lean).
[LookupSelectors.lean](../LookupSelectors.lean) states `CachedLookupSelectorsClaim`:
the lists cover the native query operands in order and each expansion succeeds.
[NativeLookups.lean](../NativeLookups.lean) defines the tuple interpretation.

The kernel checks the selector claim against the imported circuit. The circuit
file import has the trusted boundary stated in the [import guide](../../Import/README.md).
