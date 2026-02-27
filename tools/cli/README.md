# CLI Tool

`cli` generates and verifies program proof artifacts, and runs binaries in the simulator.

## Build

Default build (`security_80`):

```bash
cargo build -p cli
```

Build with `security_100`:

```bash
cargo build -p cli --no-default-features --features security_100
```

Build with verification support:

```bash
cargo build -p cli --no-default-features --features include_verifiers_80
cargo build -p cli --no-default-features --features include_verifiers_100
```

Build with GPU proving support:

```bash
cargo build -p cli --no-default-features --features gpu,security_80
```

`include_verifiers` is an alias for `include_verifiers_80`.

## Commands

- `prove`
- `prove-batch`
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
cargo run --release -p cli --no-default-features --features gpu,security_80 -- prove \
  --bin examples/basic_fibonacci/app.bin \
  --target base \
  --backend gpu \
  --output-dir output \
  --output-file proof.json
```

## Verify

```bash
cargo run --release -p cli --no-default-features --features include_verifiers_80 -- \
  verify \
  --proof output/proof.json \
  --bin examples/basic_fibonacci/app.bin
```

Verification checks:

- security level compatibility (`artifact.security_level` vs build features),
- program hash binding (`program_bin_keccak`, `program_text_keccak`),
- recursion chain hash consistency (for recursion targets),
- proof validity in the selected layer.

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
