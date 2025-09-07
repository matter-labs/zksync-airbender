# Running prover end to end

You can either run the proof for some ethereum transaction (using zksync-os-server) or prove execution of a custom binary.

To run prover end to end (from riscV binary to a SNARK), you will need 3 pieces:
* cli from this repo (tools/cli)
* cli from the zkos_wrapper repo
* cli from era-boojum-validator-cli repo

## Preparing binary & data

### Custom code

If you want to prove some custom riscV code, first check if it works (for example running a hashed fibonacci)

```shell
cargo run --release -p cli run --bin examples/hashed_fibonacci/app.bin --input-file examples/hashed_fibonacci/input.txt
```

Remember the final register outputs, as you should compare them with the ones from step 3.


## Proving 

There are 3 options:

* if you don't have GPU
* if you have GPU with 24GB VRAM
* if you have GPU with 32GB VRAM


### CPU only

If you run your custom code:

```shell
cargo run --release -p cli prove --bin examples/hashed_fibonacci/app.bin --input-file examples/hashed_fibonacci/input.txt  --until final-proof --tmp-dir /tmp
```

### GPU (24)

If you have gpu, you can compile with `--features gpu` flag, and then pass `--gpu` - to make proving go a lot faster:

```shell
cargo run --release -p cli --features gpu prove --bin ../zksync-os/zksync_os/app.bin  --input-rpc http://localhost:8011 --input-batch 1 --output-dir /tmp --gpu --until final-proof
```

Where 'bin' is your riscV binary, and input-file (optional) is any input data that your binary consumes.

### GPU (32GB VRAM)

Having 32GB VRAM allows you to also run the final-proof on GPU. (TODO: Add instructions)


After a while, you'll end up with a single 'final' file in the output dir, called `final_program_proof.json`

## Wrapping the riscV into SNARK

This step works only if you have over 150GB of RAM, and did the `--until final-prove` before:

You need to get the zkos-wrapper repo, and run:

```
cargo run --release -- --input /tmp/final_program_proof.json --input-binary ../zksync-airbender/examples/hashed_fibonacci/app.bin   --output-dir /tmp
```

Make sure that you pass the same input-binary that you used during proving (if not, you'll get a failed assert quickly).

This step, will wrap your boojum 2 prover proof, first into original boojum (together with compression), and then finally into a single SNARK.

### verify the snark

For this step, please use the tool from `era-boojum-validator-cli` repo:

```
cargo run -- verify-snark-boojum-os /tmp/snark_proof.json /tmp/snark_vk.json
```

This tool will verify that the proof and verification key matches.

### Generating verification keys

The code above is using 'fake' CRS - for production use cases, you should pass `--trusted-setup-file` during ZKsyncOS wrapper.

You can also generate verification key for snark by running (from zkos_wrapper repo):

```shell
cargo run --release generate-vk --input-binary ../zksync-airbender/examples/hashed_fibonacci/app.bin --output-dir /tmp --trusted-setup-file crs/setup.key
```