# Airbender Prover - Tutorial

## TL;DR

To create a proof you need:

- the CLI tool in `tools/cli`
- your compiled program as `app.bin`
- optionally, the paired `app.text` file and an input file

The default proving target is `recursion-unified`, so a minimal CPU proof command is:

```shell
cargo run --release -p cli -- prove --bin YOUR_BINARY --input-file YOUR_INPUTS --output-dir /tmp/output
```

To use the GPU backend, build with the `gpu` feature and select `--backend gpu`:

```shell
cargo run --release -p cli --features gpu -- prove --bin YOUR_BINARY --input-file YOUR_INPUTS --output-dir /tmp/output --backend gpu
```

## Program format

Your program can be written in any language that can target RISC-V. The examples in this repo use Rust.

In practice, the programs we prove follow these rules:

- no `std`
- no file, network, or host syscalls
- external input is read through the nondeterminism CSR path
- final public outputs are reported through the standard success/finish convention used by the examples

If you have only `app.bin`, the CLI will derive `app.text` automatically by replacing the `.bin` suffix with `.text`.

## Running a program

`cli run` executes the binary through the transpiler VM and prints the final register outputs:

```shell
cargo run --release -p cli -- run --bin examples/basic_fibonacci/app.bin --expected-results 144
```

Useful flags:

- `--text <path>` if the text section is not the default sibling file
- `--input-file <path>` for program input
- `--cycles <n>` to stop after a fixed number of cycles
- `--machine full-unsigned|reduced` to choose the decoder used for `run`

## Creating proofs

The CLI exposes three proof targets:

- `base`
- `recursion-unrolled`
- `recursion-unified` (default)

For most users, the default target is the right one because it runs the whole active recursion pipeline and emits a single proof artifact.

CPU example:

```shell
cargo run --release -p cli -- prove \
  --bin examples/basic_fibonacci/app.bin \
  --output-dir output \
  --output-file proof.json
```

GPU example:

```shell
cargo run --release -p cli --features gpu -- prove \
  --bin examples/basic_fibonacci/app.bin \
  --output-dir output \
  --output-file proof.json \
  --backend gpu
```

If you want to stop after the base layer and continue later, use staged proving:

```shell
cargo run --release -p cli -- prove \
  --bin examples/basic_fibonacci/app.bin \
  --target base \
  --output-dir output \
  --output-file base.json

cargo run --release -p cli -- continue-proof \
  --proof output/base.json \
  --bin examples/basic_fibonacci/app.bin \
  --target recursion-unified \
  --output-dir output \
  --output-file recursion_unified.json
```

`continue-proof` currently supports only CPU-produced artifacts.

## Verifying proofs

The CLI verifies a single proof artifact at a time:

```shell
cargo run --release -p cli -- verify --proof output/proof.json --bin examples/basic_fibonacci/app.bin
```

Verification checks:

- proof validity for the selected target
- security-level compatibility
- binding to the provided program binary and text section
- recursion-chain consistency for recursive targets

## Inputs and delegations

Most programs read external data through the nondeterminism CSR path. `examples/dynamic_fibonacci` shows a minimal input-driven program.

Delegation circuits are triggered through dedicated CSR ids and operate on RAM-backed ABI data. `examples/hashed_fibonacci` shows the current Blake-based delegation flow.

## Current proving shape

The active proving path is split into:

- base execution proving for the user program
- unrolled recursion over execution-family proofs
- unified reduced recursion to compress the recursive proof set further

That means reduced-machine proving is part of the live recursion path, not just a historical verifier-only detail.
