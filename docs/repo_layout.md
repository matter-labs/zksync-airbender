# Repo Layout

What follows is a very rough and partly incomplete layout of our repo. What is NOT present in this repository is our "kernel" ZKsync OS, which runs on top of the RISC-V CPU, and is found in another repository.

## Crates and Scripts

- blake2s_u32/ - native BLAKE2s/3 implementation.
- circuit_defs/ - CPU to GPU circuit glue code, RISC-V ISA circuit tests, CPU prover chunking implementation, core stark verifier logic.
- cs/ - all air circuit APIs and implementations.
- examples/ - simple mock CPU "kernel" programs used for testing.
- execution_utils/ - utility code to test the prover.
- fft/ - native and verifier FFT implementations in multiple layout formats to mirror various GPU layouts.
- field/ - native optimized CPU prover and verifier Mersenne31 basic and extension field implementations.
- full_statement_verifier/ - full STARK verifier logic, with support for chunking.
- gpu_prover/ - main `Rust -> CUDA` GPU prover implementation.
- gpu_witness_eval_generator/ - `Rust -> CUDA` GPU prover's witness generator.
- non_determinism_source/ - `NonDeterminism` storage reader trait, implemented in `prover` crate.
- poseidon2/ - native Poseidon2 implementation.
- prover/ - main CPU prover implementation with its five stages.
- risc_v_simulator/ - simple RISC-V simulator used for some forms of witness tracing.
- riscv_common/ - custom RISC-V bytecode to be used by "kernel" OS programs.
- reduced_keccak/ - Keccak-256 implementation for RV32, used in recursion flows.
- tools/ - high-level shell programs used to conduct proving, GPU proving, and verification.
- docker/ - container files and scripts for reproducible environments.
- trace_holder/ - basic trait implementation for CPU prover trace layout options.
- transcript/ - non-interactive CPU prover's Fiat-Shamir transform implementation.
- verifier/ - core recursive and native verifier code.
- verifier_common/ - code related to the recursive verifier.
- verifier_generator/ - serialization code to generate constant parameters/constraints for verifier.
- witness_eval_generator/ - code that assists in serializing witness generation closures for GPU passover.
- worker/ - CPU prover's parallelization utilities implementation.
- build.sh - high-level script to help build all needed tools and files.
- profile.sh - high-level script to profile witness generation.
- recreate_verifiers.sh - high-level script to help generate verifier parameters.
- recursion.sh - high-level script to test a more complicated CPU proving pattern, which includes some layers of recursion.

## Prover Implementations

- CPU:
    - circuit_defs/
        - trace_and_split/ - primary code to perform division of complex prover workload into batches.
    - prover/
        - prover_stages/ - contains all prover stages for a STARK IOP batch, stages 1-5 all feed into each other and output a final proof.
        - merkle_trees/ - code optimized to perform Merkle trees with trimmed tree root nodes and leaf packing of polynomials with shared columns.
        - tracers/ - helper code for supporting witness gen of memory argument.
        - witness_evaluator/ - code to help evaluate our special witness generation closures.
- GPU: 
    - gpu_prover/ - rather comprehensive mix of CUDA and Rust glue code, to mirror our CPU prover.
    - gpu_witness_eval_generator/ - code to help evaluate our special witness generation closures.

## AIR Circuits

- cs/
    - cs/ - basic AIR polynomial APIs used everywhere to compose our circuits in a programmatic manner, similar to using a custom DSL. `circuit.rs` trait and `cs_reference.rs` trait implementations are at the heart of all our circuits.
    - definitions/ - AIR API extensions.
    - delegation/ - custom BLAKE and BigInt precompile circuits and their abis.
    - devices/ - AIR API extensions, mostly for constraints that are orthogonally shared between branching opcodes. `optimization_context.rs` contains the bulk of it.
    - machine/
        - decoder/ - circuit for the decoding operation of a RISC-V cycle, called by machine configurations
        - machine_configurations/ - the starting point for all our RISC-V circuits, contained in five configurations which all crash when a trap occurs: a normal full ISA, a full ISA which allows for delegation (default for main proving), a full ISA which allows for delegation but is optimized to exclude signed multiplication and division, a minimal ISA for the recursion verifier program, a minimal ISA that supports delegation (default for recursive verifier proving).
        - ops/ - the circuits to implement each orthogonally branching opcode, which are then called by machine configurations to compose a full RISC-V circuit.
    - one_row_compiler/ - a layout compiler that converts our Rust AIR constraints into proper witness trace matrices.
    - csr_properties.rs - code that contains the definition of our CSRRW lookup table, used for Delegation and long-term memory storage access.
    - tables.rs - code that contains the definition of almost all our lookup tables.
    - *.json - files used to serialize parameters and circuit information for the GPU.

## Testcases

- circuit_defs/
    - opcode_tests/ - code that embeds the entirety of the standard official RISC-V testcases and runs them through our circuits, to provide a basic foundation for safety and consistency.

Most of the circuits are also hand audited by multiple members of Matter Lab's internal crypto team. We also have realistic and complex test cases that simulate real proving scenarios and complex bytecode, providing an even more comprehensive testing surface. Sometimes we employ SMT solver scripts to validate our optimizations.

Testing the prover itself is, of course, not required due to the nature of Zero-Knowledge proofs. It is sufficient to ensure that the verifier and the circuits are secure.

## Utilities

- tools/ - High-level CLIs and scripts for proving, GPU proving, verification, and reproduction.
- docker/ - Container files and scripts for reproducible environments.

## Verifier

See `verifier/`, `verifier_common/`, `verifier_generator/`, and `full_statement_verifier/` crates.
