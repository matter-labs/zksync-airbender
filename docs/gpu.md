# GPU proving



You can use GPU, to greatly improve proving speed.


```shell
cargo run -p cli --release --no-default-features --features gpu prove --bin prover/app.bin --output-dir /tmp/foo --gpu
```

You must compile with 'gpu' feature flag (so that gpu libraries are linked), and you must pass '--gpu' parameter.

Your GPU must support at least 24GB of VRAM.

Current issues:
* It works only on basic & recursion level - final proofs are still done on CPU (we're working on adding them on GPU, but it will require one with 32GB of VRAM).