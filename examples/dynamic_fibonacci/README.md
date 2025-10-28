# ZK prover example

Dynamic fibonacci reads a number `n` (in hex) from an input file and computes the n-th fibonacci number % 7919.

You can try it with the [tools/cli](../../tools/cli) runner as shown below.

## Example commands (from tools/cli directory)

### Smaller (1-segment) case

Use `input.txt`, which sets `n = 0007a120` (500_000 iterations).

Trace execution to get cycle count and output:
```
cargo run --release run --bin ../../examples/dynamic_fibonacci/app.bin --input-file ../../examples/dynamic_fibonacci/input.txt
```

Prove on GPU (with recursion):
```
cargo run --release --features gpu prove --bin ../../examples/dynamic_fibonacci/app.bin --input-file ../../examples/dynamic_fibonacci/input.txt --output-dir /tmp --gpu --until final-recursion
```
To prove on CPU, omit `--gpu`.

### Larger (multi-segment) case

Use `input_large.txt`, which sets `n = 002dc6c0` (3_000_000 iterations). This corresponds to [zkvm_perf](https://github.com/succinctlabs/zkvm-perf)'s `fibonacci40m` case (40m refers to an upper bound on the number of RISC-V cycles. The number of Fibonacci iterations is also [3_000_000](https://github.com/succinctlabs/zkvm-perf/blob/main/eval/src/sp1.rs#L70-L72)).

Trace execution to get cycle count and output:
```
cargo run --release run --bin ../../examples/dynamic_fibonacci/app.bin --input-file ../../examples/dynamic_fibonacci/input_large.txt --cycles 40000000
```

`--cycles 40000000` tells the CLI tool to trace and prove up to 40m RISC-V cycles.

Prove on GPU (with recursion):
```
cargo run --release --features gpu prove --bin ../../examples/dynamic_fibonacci/app.bin --input-file ../../examples/dynamic_fibonacci/input_large.txt --cycles 40000000 --output-dir /tmp --gpu --until final-recursion
```

## Rebuilding

If you want to tweak the program itself (`src/main.rs`), you must rebuild by running `dump_bin.sh`. You might need to install [cargo-binutils](https://crates.io/crates/cargo-binutils/).
