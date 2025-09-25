# ZKsync Airbender Overview

ZKsync Airbender is a zero-knowledge virtual machine (zkVM) and proving system that generates cryptographic proofs for RISC-V program execution. It serves as the Proving Layer for [ZKsync OS](https://github.com/matter-labs/zksync-os), enabling verifiable computation of blockchain state transitions.

### The ZKsync Architecture Problem

ZKsync aims to scale Ethereum by moving computation off-chain while maintaining security through zero-knowledge proofs. However, this creates a fundamental challenge:

- **Execution Layer**: We need a fast, efficient system to execute transactions and compute state transitions.
- **Proving Layer**: We need a separate system to generate cryptographic proofs of the execution correctness.
- **Determinism**: Both systems must produce identical results to maintain security.

Airbender solves this by providing a specialized zkVM that can prove RISC-V program execution:

1. **ZKsync OS** executes transactions and computes state transitions.
2. **Airbender** proves that the same execution would produce identical results (verifiable, on RISC-V).
3. **Deterministic execution** ensures both systems produce the same outputs.


### ZKsync OS: The Execution Layer

[ZKsync OS](https://github.com/matter-labs/zksync-os) is the state transition function for ZKsync. ZKsync OS is implemented as a Rust program that needs to be compiled to two targets:
- One is compiled to x86 and runs in the sequencer.
- The second one is compiled to RISC-V and fed as an input to the ZKsync Airbender prover to produce the validity proof of the state transition.

The main goals for ZKsync OS are:

- EVM equivalence: ZKsync OS should be able to process EVM transactions, keeping the EVM semantics (including gas model).
- Customizability: ZKsync OS should be easily configurable and extendable.
- Performance: The proving of an ERC20 transfer should have a cost of $0.0001. Additionally, we should be able to handle 10,000 TPS.

### Airbender: The Proving Layer

Airbender is the zkVM that proves RISC-V execution, whose role is to verify that the RISC-V execution matches what the x86 sequencer computed:

- **Input**: The ZKsync OS binary compiled to RISC-V.
- **Output**: Zero-knowledge proof that the execution was correct.

### Step-by-Step Process

1. **Transaction Processing**: ZKsync OS (x86) executes transactions and updates state.
2. **RISC-V Compilation**: The same ZKsync OS is compiled to RISC-V for proving.
3. **Deterministic Replay**: Airbender executes the RISC-V binary with identical inputs in the simulator, the internal RISC-V interpreter, to replay the binary with the exact same inputs and to produce the execution trace/witness before proving.
4. **Proof Generation**: Airbender generates a ZK proof of the execution correctness.
5. **Verification**: Anyone can verify the proof without re-running the computation.

## Key Technical Components

### RISC-V Execution Environment

Airbender provides a bare-metal RISC-V execution environment with:

- **Custom CSR (Control Status Registers)**: For delegation calls to specialized circuits.
- **No Exception Handling**: Exceptions aren't trapped at runtime; instead, constraint relations make illegal paths unsatisfiable. If an access would be misaligned or illegal, there is no witness that satisfies the polynomial relations, causing proof generation to fail.
- **Trusted Code Assumption**: Memory accesses are assumed to be properly aligned and within bounds.
- **Delegation Support**: Precompiles for cryptographic operations .

### Delegation System

Airbender supports "delegations" - specialized precompiles that handle complex operations:

- **Big Integer Operations**: U256 arithmetic with custom CSR `0x7ca`.
- **Cryptographic Hashing**: BLAKE2s with custom CSR `0x7c7`.
- **Non-deterministic Data**: External oracle access via CSR `0x7c0`.

### Multi-Machine Support

Different execution modes for different use cases:

- **Full ISA**: Complete RISC-V instruction set support.
- **Minimal Machine**: Optimized subset for specific workloads.
- **Delegation-Enabled**: Support for custom precompiles and external data.

## Getting Started

1. **Write Programs**: Use the [Writing Programs guide](./writing_programs.md) to create RISC-V programs.
2. **Build and Test**: Compile to RISC-V binary and test with the simulator.
3. **Generate Proofs**: Follow the [End-to-end guide](./end_to_end.md) to prove execution.
4. **Integrate**: Use the generated proofs in your ZKsync application.

## Further Reading

- [Writing Programs for Airbender](./writing_programs.md) - How to create RISC-V programs.
- [End-to-End Proving](./end_to_end.md) - Complete proving workflow.
- [Delegation Circuits](./delegation_circuits.md) - Understanding precompiles.
- [ZKsync OS Repository](https://github.com/matter-labs/zksync-os) - The execution layer.

---

*This overview provides the high-level understanding needed to work with Airbender. For technical implementation details, see the specific guides linked above.*
