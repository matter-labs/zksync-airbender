# ZKsync Airbender Overview

ZKsync Airbender is a zero-knowledge virtual machine (zkVM) and proving system that generates cryptographic proofs for RISC-V program execution. It serves as the Proving Layer for [ZKsync OS](https://github.com/matter-labs/zksync-os), enabling verifiable computation of blockchain state transitions.

## The ZKsync Architecture

ZKsync scales Ethereum by moving computation off-chain while maintaining security through zero-knowledge proofs. This requires two tightly integrated systems: an execution layer that processes transactions quickly, and a proving layer that generates cryptographic proofs of correctness. The challenge is ensuring both systems produce identical results deterministically.
### ZKsync OS: The Execution Layer
[ZKsync OS](https://github.com/matter-labs/zksync-os) implementing the state transition function as a Rust program compiled to two targets. The x86 version runs in the sequencer for fast transaction processing, while the RISC-V version feeds into Airbender for proof generation. This dual-compilation strategy maintains EVM equivalence while targeting performance goals of $0.0001 per ERC20 transfer and 10,000 transactions per second throughput.
### Airbender: The Proving Layer
Airbender takes the RISC-V binary and generates zero-knowledge proofs that the execution was performed correctly. The key insight is that both systems execute the same code with identical inputs, ensuring deterministic results that can be cryptographically verified without re-execution.

## How Proving Works

The proving process begins when ZKsync OS finishes processing a batch of transactions. The same program, now compiled to RISC-V binary. This simulator performs deterministic replay with identical inputs, generating execution traces that feed into the proof system.

Long-running programs are automatically split into chunks of approximately 4 million cycles each. The system can handle up to 2^36 total cycles per program execution. Each chunk is proven independently, with chunks linked together through memory and delegation arguments. This chunking strategy enables parallel proof generation, significantly improving throughput.

After generating base-layer proofs, Airbender applies recursive compression. The verifier code itself is compiled to RISC-V and proven recursively, reducing multiple proofs into one at each layer. After several iterations, Airbender produces a final recursive proof. This proof is then processed by zkos_wrapper, which converts the proof format and applies additional compression, ultimately producing a single SNARK suitable for on-chain verification. This multi-stage process achieves constant-time verification regardless of the original execution length.

## Proof System Architecture

Airbender builds on STARK technology using the Mersenne31 prime field (2³¹ − 1). This field choice optimally represents 32-bit RISC-V values while enabling efficient arithmetic. The constraint system uses Algebraic Intermediate Representation with polynomial degree capped at 2, keeping proof generation tractable while maintaining security.

Polynomial commitments rely on the FRI protocol, which provides transparency without trusted setup. The combination of Mersenne31 field arithmetic and FRI enables fast proving, especially when accelerated by GPU hardware.

The system has been professionally audited. See the [audit report](../audits/zksync-audit-aug25(Final).pdf) for security analysis.

## Key Technical Components

### RISC-V Execution Environment

Airbender provides a bare-metal RISC-V execution environment operating in machine mode with the RV32IM instruction set. The system uses custom Control Status Registers to enable delegation calls to specialized circuits, allowing heavy operations to be offloaded to optimized precompile circuits.

Exception handling is intentionally omitted. Instead of trapping illegal operations at runtime, the constraint system makes them unprovable. If code attempts misaligned memory access or executes invalid instructions, the polynomial constraints become unsatisfiable and proof generation fails. This trusted code model simplifies the circuit dramatically while ensuring only well-formed programs can be proven.

### Delegation System

Complex cryptographic operations are handled through specialized delegation circuits. When the RISC-V program needs heavy computation like hashing or 256-bit arithmetic, it triggers a delegation via CSR `0x7c0` with a specific delegation type identifier. The BigInt delegation provides U256 operations for EVM-style arithmetic, elliptic curve cryptography, and modular exponentiation. The BLAKE2 delegation accelerates hash computations used in Merkle trees and commitments. A non-determinism oracle at the same CSR address supplies external input data to programs during execution.

These delegations integrate seamlessly with the main circuit through the unified memory argument. Register reads, writes, and memory accesses in delegation circuits participate in the same consistency checks as regular RISC-V operations. From the verification perspective, delegations are proven in separate circuits that can be parallelized with the main execution proofs.

### Machine Configurations

Airbender offers multiple machine configurations optimized for different use cases. The full ISA configuration supports the complete RV32IM instruction set including signed multiplication and division, suitable for proving general-purpose kernel code like ZKsync OS. Minimal machines strip out byte-level memory operations and complex arithmetic, reducing circuit size for recursion layers where the verifier code has simpler requirements.

## Getting Started

New users should begin with the [Writing Programs guide](./writing_programs.md) to understand how RISC-V programs are structured for Airbender. After writing your program, compile it to a RISC-V binary and test execution using the built-in simulator. Once satisfied with correctness, follow the [End-to-end guide](./end_to_end.md) to generate proofs and integrate them into your ZKsync application.

For understanding specialized operations, consult the [Delegation Circuits documentation](./delegation_circuits.md). To learn about different machine configurations and their tradeoffs, see [Machine Configuration](./machine_configuration.md). The [Tutorial](./tutorial.md) provides step-by-step instructions for your first proving workflow.

Deeper technical understanding comes from the [Philosophy and Logic](./philosophy_and_logic.md) document, which explains core architectural decisions. The [Circuit Overview](./circuit_overview.md) details the constraint system design, while [Repository Layout](./repo_layout.md) helps navigate the codebase. For contributing to Airbender development, start with [CONTRIBUTING.md](../CONTRIBUTING.md).

The [ZKsync OS repository](https://github.com/matter-labs/zksync-os) contains the execution layer that Airbender proves. Understanding both systems together gives the complete picture of ZKsync's architecture.
