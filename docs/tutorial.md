# Airbender Prover - Tutorial


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

By convention, the final results of the computation should be stored in registers 10..18.
For a simple example, see `examples/basic_fibonacci`.

### Inputs and Outputs

Most programs require reading external data. This is done via a special CSR register (0x7c0):

* **Reading Data:** The register can fetch the next word of input into the program. See the `read_csr_word` function in `examples/dynamic_fibonacci` for details.
* **Writing Data:** While this register can also write output, this feature is not used during proving (it's used during the "forward running" of ZKsync OS, a separate topic).

Example: `examples/dynamic_fibonacci` demonstrates reading input (n) and computing the n-th Fibonacci number.

### Delegations (Custom Circuits)
Custom circuits are triggered using dedicated CSR IDs. Currently, we have 2 delegation circtuits - one for blake and one for big integer.


**How It Works:**

Each circuit has a CSR ID (e.g., Blake uses `0x7c2`).

A memory pointer is passed to the circuit for input/output, formatted in the expected ABI.

**Example:** See `examples/hashed_fibonacci`, specifically the `crs_trigger_delegation` method, which computes the n-th Fibonacci number and returns part of its hash.

## How Proving Works

### First Run: Generating Proofs
To start proving:

* Prepare the binary and input file (read via the CSR register).
* Run the first phase of proving using tools/cli prove. This will produce:
  * RISC-V proofs (one for every ~1M steps).
  * Delegate proofs (e.g., Blake, for every batch of calls).

Each proof is a FRI proof that can be verified:

* `Individually:` Use the `verify` command.
* `In Bulk:` Use the `verify-all` command.

### Second Run: Recursion
In this phase:

* The verification code (from above) is compiled into RISC-V and itself proven recursively.
* This process reduces the number of proofs.
    * Current reduction ratio: ~2.5:4 (~half as many proofs).
* After several iterations, only a few proofs remain. These can be verified by other systems (e.g., Boojum) and sent to Layer 1 (L1).


## Technical Details

### Machine Types
There are two machine types:

* Standard: Full set of instructions.
* Reduced: Subset of operations, optimized for faster verification.
* Final: this is the "larger" machine (2^23), that tries to limit number of FRI proofs in the final step.

Currently, we use Reduced machines only for verification since they require fewer iterations.

### Checking recursion correctness

At the base level, the user program being proven outputs its result into **8 registers**.

In the verification layers, **16 registers** are returned, where:

* The first 8 registers mirror the user program's return values.
* The last 8 registers contain a hash representing a chain of verification keys. This chain is computed as:

 `blake(blake(blake(0 || user_program_verification_key)|| verifier_0_verification_key) || verifier_1_verification_key)...`

**Optimization**

If the verifier's verification keys remain the same across layers, no new elements are added to the chain in subsequent layers.


**Verification Key Computation**
The verification key for the program is calculated as:

`blake(PC || setup_caps)`

where:
* **PC:** The program counter value at the end of execution.
* **setup_caps:** A Merkle tree derived from the program.