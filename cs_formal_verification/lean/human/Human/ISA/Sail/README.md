# Sail boundary

[Theorems.lean](Theorems.lean) separates decode and single-step soundness from their
non-vacuity statements. The final wrappers expose both statements. The
[restatement audit](../../../../test/Checks/Restatements.lean) proves that each
soundness and witness pair has the same meaning as the combined statement.

[WholeRun.lean](WholeRun.lean) defines the finite machine run, architectural cell
reads and agreement with the RV state. It declares the run simulation,
construction of an agreeing configured machine and preservation of configuration
through a supported fetch. Each statement has a separate non-vacuity statement.
[MachineTargets.lean](MachineTargets.lean) declares one machine-level conclusion
for each production machine target.
[NativeTargets.lean](NativeTargets.lean) states the direct cached-certificate
variants. Their [final proofs](../../../../proven/Proven/Final/ISA/NativeTargets.lean)
compose native acceptance, whole RV execution and the finite machine simulation.
[WholeRun proofs](../../../../proven/Proven/Final/ISA/WholeRun.lean) expose the run,
configuration and fetch results with separate witnesses.

The Airbender machine uses the specification's own definitions for loads into x0,
`mop.rr.N`, `mop.r.N`, CSR 0x7c0 and all delegations. These are machine overrides.
The equivalence applies to this configured Airbender machine. The full unsigned
target excludes `mop.r.N`; the reduced and unified targets use the modeled
xor-rotate behavior. Special5 remains outside the production machine targets.

Sail generation and its pinned sources are documented in
[the generation guide](../../../../../sail/README.md).
