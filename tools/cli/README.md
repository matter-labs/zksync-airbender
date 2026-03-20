# CLI Tool

`cli` generates and verifies program proof artifacts, and runs binaries through the transpiler VM.

## Build

Default build (`security_80`, verification included):

```bash
cargo build -p cli
```

Build with `security_100`:

```bash
cargo build -p cli --no-default-features --features security_100
```

Build with GPU proving support:

```bash
cargo build -p cli --features gpu
```

## Commands

- `prove`
- `prove-batch`
- `continue-proof`
- `verify`
- `run`

## Program Input Files

- `--bin <path>` is required for `prove` and `run`.
- `--text <path>` is optional. If omitted, `.text` is derived from `--bin`.

## Prove

Base layer proof on CPU:

```bash
cargo run --release -p cli -- prove \
  --bin examples/basic_fibonacci/app.bin \
  --target base \
  --backend cpu \
  --output-dir output \
  --output-file proof.json
```

Recursion-unified proof on CPU (`recursion-unified` is the default target):

```bash
cargo run --release -p cli -- prove \
  --bin examples/basic_fibonacci/app.bin \
  --backend cpu \
  --output-dir output \
  --output-file proof.json
```

Base layer proof on GPU:

```bash
cargo run --release -p cli --features gpu -- prove \
  --bin examples/basic_fibonacci/app.bin \
  --target base \
  --backend gpu \
  --output-dir output \
  --output-file proof.json
```

## Verify

```bash
cargo run --release -p cli -- \
  verify \
  --proof output/proof.json \
  --bin examples/basic_fibonacci/app.bin
```

Verification checks:

- security level compatibility (`artifact.security_level` vs build features),
- program hash binding (`program_bin_keccak`, `program_text_keccak`),
- recursion chain hash consistency (for recursion targets),
- proof validity in the selected layer.

## Continue Proof

Use staged proving when you want to keep the base proof artifact, validate it,
and only then continue into recursion:

```bash
cargo run --release -p cli -- prove \
  --bin examples/basic_fibonacci/app.bin \
  --target base \
  --output-dir output \
  --output-file base.json

cargo run --release -p cli -- verify \
  --proof output/base.json \
  --bin examples/basic_fibonacci/app.bin

cargo run --release -p cli -- continue-proof \
  --proof output/base.json \
  --bin examples/basic_fibonacci/app.bin \
  --target recursion-unified \
  --output-dir output \
  --output-file recursion_unified.json

cargo run --release -p cli -- verify \
  --proof output/recursion_unified.json \
  --bin examples/basic_fibonacci/app.bin
```

## Prove Batch

```bash
cargo run --release -p cli -- prove-batch \
  --bin examples/basic_fibonacci/app.bin \
  --input-file input/a.hex \
  --input-file input/b.hex \
  --input-type hex \
  --output-dir output
```

## Run

```bash
cargo run --release -p cli -- run --bin examples/basic_fibonacci/app.bin --expected-results 144
```

`run` machine options:

- `full-unsigned` (default)
- `reduced`

## Input Data

`prove` and `run` support:

- `--input-file <path>`
- `--input-type hex|prover-input-json`
- `--input-rpc <url>`

## Proof Artifact Format

`prove` writes a JSON artifact with:

- `schema_version`
- `security_level`
- `target`
- `backend`
- `batch_id`
- `cycles`
- `program_bin_keccak`
- `program_text_keccak`
- `timings_ms`
- `proof_counts`
- `proof` (`UnrolledProgramProof`)
