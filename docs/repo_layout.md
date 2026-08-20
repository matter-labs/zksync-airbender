# Repo Layout

What follows is a very rough and partly incomplete layout of our repo. What is NOT present in this repo is our "kernel" ZKsync OS which runs on top of the RiscV cpu, and is found in another repo.

## Crates and Scripts
- blake2s_u32/ - native blake2s/3 implementation
- circuit_defs/ - cpu to gpu circuit glue code, RiscV ISA circuit tests, cpu prover chunking implementation, core stark verifier logic
- cs/ - all air circuit apis and implementations
- examples/ - simple mock cpu "kernel" programs used for testing
- fft/ - native and verifier fft implementations in multiple layout formats to mirror various gpu layouts
- field/ - native optimised cpu prover and verifier Mersenne31 basic and extension field implementations
- full_statement_verifier/ - full stark verifier logic, with support for chunking
- gpu/ - Rust->CUDA GPU prover crate stack (see the "gpu:" section under Prover Implementations)
- non_determinism_source/ - NonDeterminism storage reader trait, implemented in `prover` crate
- program_prover/ - CPU program proving engines (unrolled and unified execution)
- prover/ - main cpu prover implementation with its 5 stages
- prover_pipeline/ - production prove-to-artifact pipeline: base + recursion driver, CPU/GPU backends, proof artifact schema and verification
- riscv_common/ - custom RiscV bytecode to be used by "kernel" OS programs
- riscv_transpiler/ - bytecode preprocessing, transpiler VM execution, replay, and witness layouts used by the active proving path
- tools/ - high-level shell programs used to conduct proving, gpu proving, and verification
- transcript/ - non-interactive cpu prover's Fiat-Shamir transform implementation
- verifier/ - core recursive and native verifier code
- verifier_common/ - code related to recursive verifier
- verifier_generator/ - serialisation code to generate constant parameters/constraints for verifier
- witness_eval_generator/ - code that assists in serialising witness generation closures for gpu passover
- worker/ - cpu prover's parallelisation utilities implementation
- build.sh - high-level script to help build all needed tools and files
- profile.sh - high-level script to profile witness generation
- recreate_verifiers.sh - high-level script to help generate verifier parameters
- recursion.sh - high-level script to test more complicated cpu proving pattern which includes some layers of recursion


## Prover Implementations
- cpu:
    - circuit_defs/
        - trace_and_split/ - primary code to perform division of complex prover workload into batches
    - program_prover/ - the CPU proving engines (unrolled and unified execution) that drive `prover`
    - prover_pipeline/ - base + recursion driver over either backend, plus the proof artifact and its verification
    - prover/
        - prover_stages/ - contains all prover stages for a stark iop batch, stages 1-5 all feed into each other and output a final proof
        - merkle_trees/ - code optimised to perform merkle trees with trimmed tree root nodes and leaf packing of polynomials with shared columns
        - tracers/ - helper code for supporting witness gen of memory argument
        - witness_evaluator/ - code to help evaluate our special witness generation closures
- gpu: the Rust->CUDA GPU prover crate stack. Every crate lives at `gpu/<dir>/` but is named `gpu_<dir>` (e.g. `gpu/core/` is crate `gpu_core`). Dependency edges only point down the stack: `core < { ntt, ops, hash, cub } < prover_context < trace < gkr < whir < circuit_prover < execution_prover < program_prover`.
    - core/ (`gpu_core`) - GPU substrate: static device/host allocators, device structures + accessors, field, callbacks, nvtx, machine type, utils; owns the base CUDA headers shared by the kernel crates
    - ntt/ (`gpu_ntt`) - the NTT subsystem (launchers + twiddles + CUDA kernels)
    - ops/ (`gpu_ops`) - generic math/transform kernels (simple, powers, squaring, transpose, bit-reverse, batch-inverse)
    - hash/ (`gpu_hash`) - blake2s hashing + Merkle trees + gather + the Fiat-Shamir transcript (commit/squeeze/PoW)
    - prover_context/ (`gpu_prover_context`) - shared device/host allocators, CUDA streams, and transfer coordination
    - trace/ (`gpu_trace`) - GPU witness generation and trace commitment
    - gkr/ (`gpu_gkr`) - GKR forward/backward execution, proof layout, setup, and protocol kernels
    - whir/ (`gpu_whir`) - WHIR folding, query, and proof-of-work scheduling
    - circuit_prover/ (`gpu_circuit_prover`) - the CUDA-backed single-circuit proving pipeline over the trace, GKR, and WHIR crates
    - execution_prover/ (`gpu_execution_prover`) - the execution-level driver (`ExecutionProver`) that proves all of a program's circuits
    - program_prover/ (`gpu_program_prover`) - the program-level driver + full recursion pipeline; assembles proofs into `ProgramProof`, builds the non-determinism streams the `fsv_*` verifier binaries consume, and (behind a non-default `verifiers` feature) verifies proofs natively
    - gkr_model/ (`gpu_gkr_model`) - pure-CPU model of the GKR layout (address audit, storage layout, circuit transform); no CUDA
    - gkr_compiler/ (`gpu_gkr_compiler`) - CPU-only compiler for committed forward schedules and backward VM programs; offline search is feature-gated
    - witness_eval_generator/ (`gpu_witness_eval_generator`) - pure-CPU Rust->CUDA codegen that emits the committed `witness_generation_fn.cuh` witness bodies
    - native_build/ (`gpu_native_build`) - shared CUDA/native build-script helper (a build-dependency only)
- gkr_eval_ir/ - GPU-independent GKR evaluation DAG and checked lowering model

## AIR Circuits
- cs/
    - cs/ - basic AIR polynopmial apis used everywhere to compose our circuits in a programmatic manner (similar to using a custom DSL). `circuit.rs` trait and `cs_reference.rs` trait impl. are at the heart of all our circuits
    - definitions/ - AIR api extensions
    - delegation/ - custom precompile circuits and their abis (Blake, U256 BigInt)
    - devices/ - AIR api extensions, mostly for constraints that are orthogonally shared between branching opcodes. `optimization_context.rs` contains the bulk of it
    - machine/
        - decoder/ - circuit for the decoding operation of a RiscV cycle, it's called by machine configurations
        - machine_configurations/ - the starting point for all our RiscV circuits, contained in five configurations which all crash when a trap occurs: a normal full isa, a full isa which allows for delegation (default for main proving), a full isa which allows for delegation but is optimised to exclude signed multiplication and division, a minimal isa for the recursion verifier program, a minimal isa that supports delegation (default for recursive verifier proving)
        - ops/ - the circuits to implement each orthogonally branching opcode, they are then called by machine configurations to compose a full RiscV circuit
    - one_row_compiler/ - a layout compiler that converts our Rust AIR constraints into proper witness trace matrices
    - csr_properties.rs - code that contains the definition of our CSRRW lookup table (used for Delegation and long-term memory storage access)
    - trables.rs - code that contains the definition of almost all our lookup tables
    - *.json - files used to serialise parameters and circuit information for the gpu

most of the circuits are also hand audited by multiple members of the crypto team. we also have realistic and complex testcases which simulate real proving scenarios and complex bytecode, providing an even more complete testing surface. sometimes we employ SMT solver scripts to validate our optimisations.

Testing the prover itself is of course not required, due to the nature of Zero-Knowledge proofs, since it is sufficient to ensure that the verifier and the circuits are secure.

## Utilities
TODO

## Verifier
TODO
