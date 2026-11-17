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
[Interpreter.lean](Interpreter.lean) relates `runSail` to lean-sail's `interpretSailEffects`.
The kernel cannot evaluate the hash maps of lean-sail's state, so the claims use `runSail`.
The simulation holds for every effect except the cycle-counter read, which the generated model does not use.
Lean-sail can stop where `runSail` continues: on a register or byte that is not in its map, or on a tagged request.

The Airbender machine uses the specification's own definitions for loads into x0,
`mop.rr.N`, `mop.r.N`, CSR 0x7c0 and all delegations. These are machine overrides.
Sail gives Zimop instructions a zero result; this machine gives them the stated custom effects.
A load into x0 does not access memory in this machine.
The machine decodes with `RV.decode`. Other enabled Sail extensions, such as A, have no instruction step.
A standard instruction step requires `nextPC % 4 = 0`.
Delegation stores can update shadow RAM below the ROM boundary. Ordinary stores to ROM have no step.
The equivalence applies to this configured Airbender machine. Both unrolled targets exclude `mop.r.N`.
Unified admits `mop.r.N` with N = 16, 12, 8 or 7, and `mop.r.N x0` for every N as a no-op.
Special5 remains outside the production machine targets.
Each whole-run conclusion holds for every configured start that agrees with the public initial state.
The final input is the public input after the number of reads in the submitted CPU trace.

The [valid-use claims](../ValidUse/README.md) connect valid bigint, BLAKE2s and Keccak calls to their reference functions.
Their RAM buffers, controls and complete reference schedules are public ABI premises.

Sail generation and its pinned sources are documented in
[the generation guide](../../../../../sail/README.md).
