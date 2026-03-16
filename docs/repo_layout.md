# Repo Layout

What follows is a very rough and partly incomplete layout of our repo. What is NOT present in this repo is our "kernel" ZKsync OS which runs on top of the RiscV cpu, and is found in another repo.

## Crates and Scripts
- blake2s_u32/ - native blake2s/3 implementation
- circuit_defs/ - cpu to gpu circuit glue code, RiscV ISA circuit tests, cpu prover chunking implementation, core stark verifier logic
- cs/ - all air circuit apis and implementations
- examples/ - simple mock cpu "kernel" programs used for testing
- execution_utils/ - utility code to test the prover
- fft/ - native and verifier fft implementations in multiple layout formats to mirror various gpu layouts
- field/ - native optimised cpu prover and verifier Mersenne31 basic and extension field implementations
- full_statement_verifier/ - full stark verifier logic, with support for chunking
- gpu_prover/ - main Rust->CUDA gpu prover implementation
- gpu_witness_eval_generator/ - Rust->CUDA gpu prover's witness generator
- non_determinism_source/ - NonDeterminism storage reader trait, implemented in `prover` crate
- prover/ - main cpu prover implementation with its 5 stages
- riscv_common/ - custom RiscV bytecode to be used by "kernel" OS programs
- riscv_transpiler/ - bytecode preprocessing, transpiler VM execution, replay, and witness layouts used by the active proving path
- tools/ - high-level shell programs used to conduct proving, gpu proving, and verification
- trace_holder/ - basic trait impl for cpu prover trace layout options
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
    - prover/
        - prover_stages/ - contains all prover stages for a stark iop batch, stages 1-5 all feed into each other and output a final proof
        - merkle_trees/ - code optimised to perform merkle trees with trimmed tree root nodes and leaf packing of polynomials with shared columns
        - tracers/ - helper code for supporting witness gen of memory argument
        - witness_evaluator/ - code to help evaluate our special witness generation closures
- gpu: 
    - gpu_prover/ - rather comprehensive mix of cuda and rust glue code, to mirror our cpu prover
    - gpu_witness_eval_generator/ - code to help evaluate our special witness generation closures

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
