# gpu_prover

## How to add a new circuit

- for a new main circuit
    - under `native/witness/circuits` add a new `name_of_the_circuit.cu` file by copying an existing one for a main
      circuit
    - adjust the `NAME` inside the new file
    - add the new file to `native/CMakeLists.txt` list of files for the `gpu_prover_native` library
    - create a new enum variant in `src/circuit_types.rs` for the new circuit in `MainCircuitType` enum and add the
      handling of the variant in the functions inside implementation of `MainCircuitType`
    - create binding for the circuit with the `generate_witness_main_kernel` macro inside `src/witness/witness_main.rs`
      file and add the kernel as a variant towards the end of the `generate_witness_values_main` function
    - add handling of the new variant in the `get_main_circuit_precomputations` function in
      `src/execution/precomputations.rs`
    - add handling of the new variant in the `spawn_cpu_worker` function in `src/execution/prover.rs`
- for a new delegation circuit
    - under `native/witness/circuits` add a new `name_of_the_circuit.cu` file by copying an existing one for a
      delegation circuit
    - adjust the `NAME` inside the new file
    - add the new file to `native/CMakeLists.txt` list of files for the `gpu_prover_native` library
    - create a new enum variant in `src/circuit_types.rs` for the new circuit in `DelegationCircuitType` enum and add
      the handling of the variant in the functions inside implementation of `DelegationCircuitType`
    - add the mapping to/from `DELEGATION_TYPE_ID` and the witness factory function for the `DelegationCircuitType` enum
    - create binding for the circuit with the `generate_witness_delegation_kernel` macro inside
      `src/witness/witness_delegation.rs` file and add the kernel as a variant towards the end of the
      `generate_witness_values_delegation` function
    - add handling of the new variant in the `get_delegation_circuit_precomputations` function in
      `src/execution/precomputations.rs`

## Configuration

### Environment variables

- `PROVER_GPU_MEMORY_FRACTION` — optional float in the range `(0.0, 1.0]`. Caps the prover's
  device allocation to that fraction of **total** GPU memory (it allocates `min(free, total * fraction)`).
  Useful for co-locating another GPU process (e.g. a SNARK prover) on the same device. When unset —
  or set to a malformed / out-of-range value — the prover keeps its default behavior of allocating all
  free GPU memory. Read once in `ProverContextConfig::default()`.

  Example: `PROVER_GPU_MEMORY_FRACTION=0.6` caps the prover at ~60% of the GPU.
