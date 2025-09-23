# GPU proving

You can use a GPU to greatly improve proving speed.
```shell
cargo run -p cli --release --no-default-features --features gpu prove --bin prover/app.bin --output-dir /tmp/foo --gpu
```

You must compile with the 'gpu' feature flag for the relevant libraries ro be linked, and you must pass the '--gpu' parameter.

Current issues:
* It works only on a basic & recursion level - final proofs are still done on CPU (as they require 150GB of RAM).
