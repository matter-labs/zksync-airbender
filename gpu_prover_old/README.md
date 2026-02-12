# gpu_prover

## How to add a new circuit

The active GPU path has two circuit families:

- unrolled execution circuits, described by `CircuitType::Unrolled(...)` in `src/circuit_type.rs`
- delegation circuits, described by `CircuitType::Delegation(...)` in `src/circuit_type.rs`

### Adding a new unrolled execution circuit

- under `native/witness/circuits`, add a new `name_of_the_circuit.cu` file by copying the closest existing unrolled kernel
- adjust the `NAME` inside the new file
- add the new file to `native/CMakeLists.txt` so it is built into `gpu_prover_native`
- add or extend the matching enum variant in `src/circuit_type.rs`
  - use `UnrolledMemoryCircuitType` for load/store-style families
  - use `UnrolledNonMemoryCircuitType` for arithmetic and control-flow families
  - update `UnrolledCircuitType::Unified` only if you are changing the unified reduced recursion circuit itself
- wire the witness kernel in `src/witness/witness_unrolled.rs`
- update `src/witness/memory_unrolled.rs` if the circuit needs different RAM or lookup-layout handling
- add the corresponding precomputation handling in `src/execution/precomputations.rs`
- update `src/execution/tracing.rs` and `src/execution/prover.rs` so the new circuit can be scheduled and traced by the active replay pipeline

### Adding a new delegation circuit

- under `native/witness/circuits`, add a new `name_of_the_circuit.cu` file by copying the closest existing delegation kernel
- adjust the `NAME` inside the new file
- add the new file to `native/CMakeLists.txt` so it is built into `gpu_prover_native`
- add a new `DelegationCircuitType` variant in `src/circuit_type.rs`
- add the mapping to and from the delegation type id in `src/circuit_type.rs`
- wire the witness kernel in `src/witness/witness_delegation.rs`
- update `src/witness/memory_delegation.rs` if the delegation ABI changes the RAM access layout
- add the corresponding precomputation handling in `src/execution/precomputations.rs`
- update `src/execution/tracing.rs` so replay emits the right trace payload for the new delegation
