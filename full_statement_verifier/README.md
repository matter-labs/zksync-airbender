## Verifiers set

In practice we will use just two verifier binaries:

- one that enters at `verify_base_or_recursion_unrolled_circuits`. It is expected to be proven using unrolled circuits in reduced configuration, and as input it accepts either a proof that uses full machine set of unrolled circuits, or reduced set of unrolled circuits
- one that enters at `verify_unrolled_or_unified_circuit_recursion_layer`. It is expected to be proven using unified circuit, and as input expects either proof with reduced set of unrolled circuits, or proof that uses unified circuit

In general, recursive verification of course depends on the setup, but we do not compare it against some constant and only ensure that all circuits of the same type use the same setup (except recursion ones that do not depend on any binary at all). Then we propagate commitment to the used set of setup keys to the output of recursion program, and then some very final verifier can compare it against expected constant