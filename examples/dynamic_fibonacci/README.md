# ZK prover example

Dynamic fibonacci reads a number `n` (in hex) from an input file and computes the n-th fibonacci number % 7919.

You can try it with the [tools/cli](../../tools/cli) command-line tool as shown below.

## Example commands (from tools/cli directory)

### Smaller (1-segment) case

Use `input.txt`, which sets `n = 0007a120` (500_000 iterations).

Run the binary through the transpiler VM to get output:
```
cargo run --release -- run --bin ../../examples/dynamic_fibonacci/app.bin --input-file ../../examples/dynamic_fibonacci/input.txt
```

Prove on GPU (`prove` defaults to the `recursion-unified` target):
```
cargo run --release --features gpu -- prove --bin ../../examples/dynamic_fibonacci/app.bin --input-file ../../examples/dynamic_fibonacci/input.txt --output-dir /tmp --backend gpu
```
To prove on CPU, omit `--features gpu --backend gpu`.

### Larger (multi-segment) case

Use `input_large.txt`, which sets `n = 002dc6c0` (3_000_000 iterations). This corresponds to [zkvm_perf](https://github.com/succinctlabs/zkvm-perf)'s `fibonacci40m` case (40m refers to an upper bound on the number of RISC-V cycles. The number of Fibonacci iterations is also [3_000_000](https://github.com/succinctlabs/zkvm-perf/blob/main/eval/src/sp1.rs#L70-L72)).

Run the binary through the transpiler VM to get output with a 40m-cycle execution budget:
```
cargo run --release -- run --bin ../../examples/dynamic_fibonacci/app.bin --input-file ../../examples/dynamic_fibonacci/input_large.txt --cycles 40000000
```

`--cycles 40000000` tells `cli run` to stop after 40m RISC-V cycles if the program does not finish earlier.

Prove on GPU with a matching CPU-side cycle bound:
```
cargo run --release --features gpu -- prove --bin ../../examples/dynamic_fibonacci/app.bin --input-file ../../examples/dynamic_fibonacci/input_large.txt --cpu-cycles-bound 40000000 --output-dir /tmp --backend gpu
```

## Rebuilding

If you want to tweak the program itself (`src/main.rs`), you must rebuild by running `dump_bin.sh`. You might need to install [cargo-binutils](https://crates.io/crates/cargo-binutils/).
