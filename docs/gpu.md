# GPU proving

GPU proving uses the same proof targets as the CPU flow, but swaps the proving backend with `--backend gpu`.

```shell
cargo run -p cli --release --features gpu -- prove --bin prover/app.bin --output-dir /tmp/foo --backend gpu
```

Notes:

* Build the CLI with the `gpu` feature so the CUDA libraries are linked.
* Select the GPU backend explicitly with `--backend gpu`.
* Current deployments should plan for at least 32GB of VRAM.
