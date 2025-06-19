# ZK prover example

Hashed fibonacci reads values `n`  and `h` (in hex) from an input file, computes the n-th fibonacci number % 10_000, then applies Blake hash `h` times.

This example shows how you can use delegation circuits (here - blake for hashing).

`input.txt` contains example inputs (`n = 0000000f` = 15 fibonacci iterations, `h = 00000001` = 1 blake iteration).

You can try it with the tools/cli runner as shown below.

## Example commands (from tools/cli directory)

Trace execution and get cycle count:
```
cargo run --profile cli run --bin ../../examples/hashed_fibonacci/app.bin --input_file ../../examples/hashed_fibonacci/input.txt
```

Prove (with recursion):
```
cargo run --release -p cli --no-default-features --features gpu prove --bin ../../examples/hashed_fibonacci/app.bin --input-file ../../examples/hashed_fibonacci/input.txt --output-dir /tmp --gpu --until final-recursion
```

## Rebuilding

If you want to tweak the program itself (`src/main.rs`), you must rebuild by running `dump_bin.sh`. You might need to install [cargo-binutils](https://crates.io/crates/cargo-binutils/).
