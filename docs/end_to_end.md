# Running prover end to end

This guide shows how to prove execution of RISC‑V binaries and generate SNARKs. You can either prove some ethereum transaction (using `zksync-os-server`) or prove execution of a custom binary.

> **Prerequisites**: Before proving, you need a RISC‑V binary. If you haven't written one yet, see the [Writing Programs guide](./writing_programs.md) to learn how to create, build, and test your program.

To run prover end to end, from the RISC-V binary to a SNARK, you will need 3 pieces:
* `cli` from this repo (tools/cli)
* `cli` from the `zkos_wrapper` repo
* `cli` from `era-boojum-validator-cli` repo

## Preparing binary & data
- Rust nightly toolchain
- `cargo‑binutils` and `objcopy`
  - Install: `rustup component add llvm-tools-preview` and `cargo install cargo-binutils`

### Custom code

If you want to prove some custom RISC-V code, first check if the execution is successful. The example command below runs a hashed fibonacci:

```shell
cargo run --release -p cli run --bin examples/hashed_fibonacci/app.bin --input-file examples/hashed_fibonacci/input.txt
```

Remember the final register outputs, as you should compare them with the ones from step 3.

> **Note**: If you're writing your own program, follow the [Writing Programs guide](./writing_programs.md) to create a proper RISC‑V binary with the correct runtime setup and exit convention.

## Proving

There are 3 different setups for proving:
* You don't have GPU
* You have GPU with 24GB VRAM
* You have GPU with 32GB VRAM

### CPU only

If you run your custom code:
```shell
cargo run --release -p cli prove --bin examples/hashed_fibonacci/app.bin --input-file examples/hashed_fibonacci/input.txt  --until final-proof --tmp-dir /tmp
```

### GPU (24GB VRAM)

If you have gpu, you can compile with `--features gpu` flag, and then pass `--gpu` - to make proving go a lot faster:
```shell
cargo run --release -p cli --features gpu prove --bin ../zksync-os/zksync_os/app.bin  --input-rpc http://localhost:8011 --input-batch 1 --output-dir /tmp --gpu --until final-proof
```

Where 'bin' is your RISC-V binary, and `input-file` (optional) is any input data that your binary consumes.

### GPU (32GB VRAM)

Having 32GB VRAM allows you to also run the final-proof on GPU. (TODO: Add instructions)

After a while, you'll end up with a single 'final' file in the output dir, called `final_program_proof.json`

## Wrapping the RISC-V into SNARK

This step works only if you have over 150GB of RAM, and did the `--until final-prove` before. You need to get the `zkos-wrapper` repo, and run:
```
cargo run --release -- --input /tmp/final_program_proof.json --input-binary ../zksync-airbender/examples/hashed_fibonacci/app.bin   --output-dir /tmp
```

Make sure that you pass the same `input-binary` that you used during proving. If not, you'll get a failed assert quickly.

This step, will wrap your boojum 2 prover proof, first into original boojum (together with compression), and then finally into a single SNARK.

### Verify the SNARK

For this step, please use the tool from `era-boojum-validator-cli` repo:

```
cargo run -- verify-snark-boojum-os /tmp/snark_proof.json /tmp/snark_vk.json
```

This tool will verify that the proof and verification key matches.

### Generating verification keys

The code above is using 'fake' CRS - for production use cases, you should pass `--trusted-setup-file` during ZKsyncOS wrapper.

You can also generate verification key for SNARK by running the following from the `zkos_wrapper` repo:
```shell
cargo run --release generate-vk --input-binary ../zksync-airbender/examples/hashed_fibonacci/app.bin --output-dir /tmp --trusted-setup-file crs/setup.key
```
