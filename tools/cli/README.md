# CLI tool

With this CLI you can run riscV code, generate the proofs and verify them.

TL;DR:

The command below, will run basic proving + recursion + final proofs, until a single FRI (warning: it requires 128GB of RAM).

```
cargo run --release --no-default-features -- prove --bin YOUR_BINARY --input-file YOUR_INPUTS --output-dir /tmp/output --until final-proof
```

## Other options

You can also:
* just run your program
* create a single (basic proof)
* create a proof until recursion (then 128GB of RAM are not needed)
* verify proofs
* create a SNARK (WIP)

## Running riscV binary.

You can run the riscV binary on the emulator, to see the expected outputs and number of used cycles.

```
cargo run --profile cli  run  --bin ../../examples/basic_fibonacci/app.bin 
```

By default it will run for up to 1_000_000 cycles, but you can specify `--cycles` to set number of cycles manually.

### Options

**machine** - most of the computation can be done on the 'standard' machine. But for some heavily optimized computations (like verifications), we have a 'mini' machine, that supports a subset of the operations (and some special ones too). You can control it via `--machine=mini` flag. Such bytecodes will be compiled with +zimop flag.


## Basic proof generation
To generate the proof, simply run the command below. It will run your binary, and put the FRI files into the outputs/ dir.


```
cargo run --profile cli  prove  --bin ../../examples/basic_fibonacci/app.bin --output_dir output/
```

where the .bin file is the riscV compiled file. You can see more instructions on how to create such file in the basic_fibonacci dir.

**Compilation times** - you might want to use `--profile cli` to minimise the compilation time, as --release might take a long time to compile the veirfication code, and --dev might be generating a proof for a really long time.

### Proofs
You will get one or more proofs as the result - depending on the length of your program (proofs in format `proof_XX.json`) and the amount of delegations (precompiles) that you used (proofs in format `delegation_PRECOMPILE-ID_XX.json`)


## Proof verification
You can verify a single FRI proof, by running:

```
cargo run --profile cli verify --proof output/proof_0.json
```

You can verify all the proofs that your program generated, by running:

```
cargo run --profile cli verify-all --metadata output/metadata.json
```

This will verify all the basic proofs, and also verify that the final results (data stored in the registers) is valid.

## Proof verification from ProgramProof

You can also verify the JSON with ProgramProof (that has all the proofs inlined inside JSON).

Just run:
```
cli verify-all --program-proof /data/1.json
```

## Passing inputs to the program

Most of the programs will have to read data (via CRS register a.k.a oracle).
The CLI handles it via `--input-file` flag, where you can pass the location of the input file (in hex text format).

For example, you can use it with `dynamic fibonacci` to compute (and later prove) the n-th fibonacci number.

```
cargo run --profile cli run --bin ../../examples/dynamic_fibonacci/app.bin --input-file ../../examples/dynamic_fibonacci/input.txt
```

You can also fetch the data directly from the sequencer (for example anvil-zksync), by passing the RPC url and batch number:

```
cargo run --no-default-features -- run --bin /home/cyfra/matter/zksync-os/zksync_os/app.bin --input-rpc http://localhost:8011 --input-batch 1
```

## Verification keys

When you receive the proof, you should also check that it is proving the execution of **your** program. This is done via verification key.

You can run:

```
cargo run --profile cli generate-vk --bin ../../examples/dynamic_fibonacci/app.bin
```

To see the verification key for your binary, and then you can compare it with the one that is printed during proof verification.

**WARNING** verification key depends on multiple factors: your binary, riscV circuit and delegation circuits. Any change to those, and the verification key will change.

## Recursion

You can use the '--until' flag in the 'prove' command to have the system run it for you automatically.

* `--until final-recursion` -- will do recursion, using delegations, requires less ram, but the final result might contain multiple files
* `--until final-proof` - will do recursion, until a single file is left (requires 128GB of RAM)
* `--until snark` - will create a SNARK proof - still WIP

Please see recursion.sh file in the main repo, if you want to do recursion manually.

