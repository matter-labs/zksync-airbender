# RISC-V Prover - Tutorial


## TL;DR

To run the Airbender, you need three things:
* a cli tool (tools/cli)
* your compiled program (app.bin)
* optionally - file with inputs to your program.

The TL;DR of creating a proof is (run this from tools/cli directory):

```shell
cargo run --release -- prove --bin YOUR_BINARY --input-file YOUR_INPUTS --output-dir /tmp/output --until final-proof
```

This will run your program with a given inputs, do necessary recursion proofs etc, and put the final proof in /tmp/output directory.

The command above would use only cpu - you can switch to use gpu, by compiling with `--features gpu` and passing `--gpu` flag.

## Creating & verifying proofs

### Generating a binary

Your program can be implemented in any programming language as long as you can compile it to riscV. All of our examples are using rust.

You can see the basic example in `examples/basic_fibonacci`.

Our examples are compiled using regular 'cargo', but your program must adapt to couple rules:

* no std - it must not use any std functionality 
* data fed via special read_csr_word instructions - it must not read/write to any files, network etc
* final results (8 x u32) should be reported via `zksync_os_finish_success`, and they become the public input.

After you compile your program to .bin format (for example using `cargo objcopy  -- -O binary app.bin`
), you can pass it to prover CLI above.

### Creating proofs

As explained in TL;DR section - you can generate proofs by running `prove` command from the CLI tool.

The `--until` command controls the recursion - if your program runs longer, it might result in multiple proofs. The subsequent recursion
runs are responsible "verifying & re-proving" - resulting in a single proof in the end.

### Verification

The output of the cli is a single FRI proof.

You can verify the proof in multiple ways:
* via cli (see "verify-all" command)
* in your server - include the same library as verify-all command
* in web browser - see TODO (this is verifier library compiled to wasm)

If you'd like to verify your proof on ethereum, it might be worth wrapping it into SNARK, which would make ethereum verification a lot cheaper.
Please see zkos-wrapper repository for details on how this can be done.

### Verification keys

To verify proofs coming from the unknown source, you should create a verification key (which is a "hash" of the expected program, and recursion verifiers). This can be done using the cli tool, and then passed to verify command.


## Higher level explanations

### What Are We Proving?

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

Custom circuits (delegations) are triggered via a dedicated CSR at `0x7C0` and selected by a per-circuit `DELEGATION_TYPE_ID`. Currently, two delegation circuits are supported: BLAKE2 with compression and BigInt with control.

How it works:
* The program writes the desired `DELEGATION_TYPE_ID` through CSR `0x7C0` to request a delegated operation.
* Inputs/outputs are passed via registers and memory pointers as defined by the circuit’s ABI (see the Delegation Circuits doc for exact register conventions).

**Example:** See [`examples/hashed_fibonacci`](../examples/hashed_fibonacci), specifically the `crs_trigger_delegation` method, which computes the n-th Fibonacci number and returns part of its hash.

---

## How Proving Works
### First Run: Generating Proofs

To start proving:
* Prepare the binary and input file, read via the CSR register.
* Run the first phase of proving using `tools/cli`'s `prove`. This will produce:
  * RISC-V proofs, one for every ~1M steps.
* Delegate proofs (e.g., BLAKE2 with compression, BigInt with control) for every batch of calls.

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
