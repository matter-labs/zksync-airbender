# ZK prover example

Hashed fibonacci reads values `n`  and `h` (in hex) from an input file, computes the n-th fibonacci number % 10_000, then applies BLAKE2 hash `h` times.

This example shows how you can use delegation circuits (here - BLAKE2 for hashing).

`input.txt` contains example inputs (`n = 0000000f` = 15 fibonacci iterations, `h = 00000001` = 1 BLAKE2 iteration).

You can try it with the [tools/cli](../../tools/cli) runner as shown below.

## Example commands (from tools/cli directory)

Trace execution to get cycle count and output:
```
cargo run --release run --bin ../../examples/hashed_fibonacci/app.bin --input-file ../../examples/hashed_fibonacci/input.txt
```

Prove on GPU (with recursion):
```
cargo run --release --features gpu prove --bin ../../examples/hashed_fibonacci/app.bin --input-file ../../examples/hashed_fibonacci/input.txt --output-dir /tmp --gpu --until final-recursion
```
To prove on CPU, omit `--gpu`.

## Rebuilding

If you want to tweak the program itself (`src/main.rs`), you must rebuild by running `dump_bin.sh`. You might need to install [cargo-binutils](https://crates.io/crates/cargo-binutils/).
