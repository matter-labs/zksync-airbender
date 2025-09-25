# RISC-V Prover - Tutorial

## What Are We Proving?

We are proving the execution of binaries containing RISC-V instructions with two key features:

* **CSR (Control and Status Registers):** Used for handling input/output operations.
* **Custom Circuits (Delegations):** Special CRSs are used for custom computations, such as hashing.

### Computation Results

By convention, the final results of the computation should be stored in registers `10..18`.
For a simple example, see [`examples/basic_fibonacci`](../examples/basic_fibonacci).

### Inputs and Outputs

Most programs require reading external data. This is done via a special CSR register (`0x7c0`):
* **Reading Data:** The register can fetch the next word of input into the program. See the `read_csr_word` function in `examples/dynamic_fibonacci` for details.
* **Writing Data:** While this register can also write output, this feature is not used during proving. It's used during the "forward running" of ZKsync OS, a separate topic.

Example: [`examples/dynamic_fibonacci`](../examples/dynamic_fibonacci) demonstrates reading input (`n`) and computing the n-th Fibonacci number.

### Delegations (Custom Circuits)

Custom circuits are triggered using dedicated CSR IDs. Currently, only the BLAKE circuit is supported.

How It Works:
* Each circuit has a CSR ID (e.g., BLAKE uses `0x7c2`).
* A memory pointer is passed to the circuit for input/output, formatted in the expected ABI.

**Example:** See [`examples/hashed_fibonacci`](../examples/hashed_fibonacci), specifically the `crs_trigger_delegation` method, which computes the n-th Fibonacci number and returns part of its hash.

---

## How Proving Works
### First Run: Generating Proofs

To start proving:
* Prepare the binary and input file, read via the CSR register.
* Run the first phase of proving using `tools/cli`'s `prove`. This will produce:
  * RISC-V proofs, one for every ~1M steps.
  * Delegate proofs, e.g., Blake, for every batch of calls.

Each proof is an FRI proof that can be verified:
* Individually - use the `verify` command.
* In bulk - use the `verify-all` command.

### Second Run: Recursion

In this phase:
* The verification code, from the previous step, is compiled into RISC-V and itself proven recursively.
* This process reduces the number of proofs.
  * Current reduction ratio: ~2.5:4, approximately half as many proofs.
* After several iterations, only a few proofs remain. These can be verified by other systems (e.g., Boojum) and sent to Layer 1 (L1).

## Getting Started

Try it yourself by following [`.github/workflow/ci.yaml`](../.github/workflow/ci.yaml).
Alternatively, run [`./recursion.sh`](../recursion.sh) to test the three levels of recursion.

---

## Technical Details
### Machine Types

There are two machine types:
* Standard: Full set of instructions.
* Reduced: Subset of operations, optimized for faster verification.

Currently, we use Reduced machines only for verification since they require fewer iterations.

### Checking recursion correctness
At the base level, the user program being proven outputs its result into **8 registers**.

In the verification layers, **16 registers** are returned, where:
* The first 8 registers mirror the user program's return values.
* The last 8 registers contain a hash representing a chain of verification keys. This chain is computed as:
 `blake(blake(blake(0 || user_program_verification_key)|| verifier_0_verification_key) || verifier_1_verification_key)...`

#### Optimization
If the verifier's verification keys remain the same across layers, no new elements are added to the chain in subsequent layers.

#### Verification Key Computation
The verification key for the program is calculated as: `blake(PC || setup_caps)`, Where:
* **PC:** The program counter value at the end of execution.
* **setup_caps:** A Merkle tree derived from the program.
