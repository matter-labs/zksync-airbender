# Keccak circuit review

This directory models the native Keccak worker's phase-dependent lane operations
and control updates. Mode-specific relations reuse original Clean permutation
components, while address/controller contracts identify the physical indirect
ports. These local effects are distinct from the complete call schedule and
permutation-state binding.

## Checked results

[`Native.operation_execution`](../../../../slop/Slop/Final/Trace/Workers/Keccak/Theorems.lean)
proves all seven native lane-mode effects against the existing Clean references,
including actual ports and modeled physical lane selection. History derives
pointer/read/range facts. Complete permutation and window claims additionally
bind the reference output and terminal tokens for the 649-call protocol;
invalid-control fallback is outside that complete protocol.

Start with [Artifact](Artifact.lean), [Execution](Execution.lean) and
[Controls](Controls.lean) for the seven native modes.
[Theta](Theta.lean), [Rho](Rho.lean), [Mix](Mix.lean), [Chi](Chi.lean) and [Iota](Iota.lean)
select the original Clean operations and the circuit's phased lane effects.

[Controller](Controller.lean) describes physical lane selection;
[controller rows](Tables/Controller.lean) and [`setup`](Tables/Setup.lean) are modeled tables.
[Addresses](Addresses.lean), [ControlUpdate](ControlUpdate.lean) and [Memory](Memory.lean)
connect the actual indirect ports and controls to shared initialized history.

The public complete-permutation claims live in
[worker execution](../../Trace/Workers/Keccak/README.md), rather than a local Theorems module.
Invalid-control fallback is outside the complete 24-round protocol; do not
infer caller ABI or padding neutrality from a supported local mode.
[Delegation context](../../Helpers/Delegation/README.md) keeps those boundaries explicit.
