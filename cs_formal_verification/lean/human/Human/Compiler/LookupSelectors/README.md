# Native lookup selectors

Each family module lists the native group, gate, operand and expansion path of
every lookup selector. Start with [AddSub.lean](AddSub.lean).
[LookupSelectors.lean](../LookupSelectors.lean) states `CachedLookupSelectorsClaim`:
the lists cover the native query operands in order, each expansion succeeds,
and each group is the group of its native output chain. The claim also states
`TableSidesRead`: the table side of each lookup group reads its declared
multiplicity column and the setup columns of `tableOperand`.
[NativeLookups.lean](../NativeLookups.lean) defines the tuple interpretation.

The `Workers/` directory states the same selectors for the worker circuits:
[Bigint](Workers/Bigint.lean), [G](Workers/BlakeG.lean), [round](Workers/BlakeRound.lean),
[column parity](Workers/KeccakColumnParity.lean), [theta/rho](Workers/KeccakThetaRho.lean)
and [chi](Workers/KeccakChi5.lean).
[WorkerLookups.lean](../WorkerLookups.lean) selects their captures and states
`CachedWorkerLookupSelectorsClaim`. [WorkerPublicSetup.lean](../WorkerPublicSetup.lean)
defines their public tables. [WorkerCertificates.lean](../WorkerCertificates.lean)
states the native gate, placement, lookup and participation fields.

The kernel checks the selector claim against the imported circuit. The circuit
file import has the trusted boundary stated in the [import guide](../../Import/README.md).
