# CLI Tool

`cli` generates and verifies program proof artifacts, and runs binaries through the transpiler VM.

## Build

Default build (`security_100`, verification included):

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

Deterministic proof-of-work is enabled by default. Disable it for GPU timing
runs while keeping the other default features:

```bash
cargo build --release -p cli --no-default-features \
  --features gpu,verifier_common/proof_utils
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

## L1 Feeder Checkpoint (CPU only)

`--target l1-feeder` continues a `recursion-unified` proof with the high-LDE
(base LDE 16, merged memory and witness commitment) feeder layers: one layer of
the special-opcodes unified verifier, then rounds of the L1 feeder verifier
until the last proof is a single chunk whose feeder verification run fits
`2^22` cycles. The artifact is the input of the L1 wrap. Each feeder proof
is proven with the bounded default CPU storage policy; the whole `l1-feeder`
continuation of `basic_fibonacci` peaked at about 117 GB of RAM.

```bash
cargo run --release -p cli -- continue-proof \
  --proof output/recursion_unified.json \
  --bin examples/basic_fibonacci/app.bin \
  --target l1-feeder \
  --output-dir output \
  --output-file l1_feeder.json

cargo run --release -p cli -- verify \
  --proof output/l1_feeder.json \
  --bin examples/basic_fibonacci/app.bin
```

## L1 Proof (CPU only)

`--target l1` continues an `l1-feeder` checkpoint (or runs through it) and
proves the L1 feeder verifier's execution as one Proth120 packed unified proof
with Keccak commitments, the proof shape the EVM verifier consumes. The
artifact (schema 4) keeps the BabyBear feeder sidecar and adds the `l1` bundle
(proof, commitment-mode data, profile tag, layout hash). On a 48-core host the
wrap of `basic_fibonacci` took about 18 minutes and peaked at about 47 GB.

```bash
cargo run --release -p cli -- continue-proof \
  --proof output/l1_feeder.json \
  --bin examples/basic_fibonacci/app.bin \
  --target l1 \
  --output-dir output \
  --output-file l1.json

cargo run --release -p cli -- verify \
  --proof output/l1.json \
  --bin examples/basic_fibonacci/app.bin \
  --feeder-only
```

There is no native verifier for the Proth120 proof: plain `verify` fails on an
L1 artifact, and `--feeder-only` checks only the feeder sidecar, the recursion
chain and the bundle's profile, layout and packing parameters, and says that
the Proth proof was not verified.

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
- `program_cycles` (cycles of the base layer, the program's own count)
- `program_bin_keccak`
- `program_text_keccak`
- `timings_ms`
- `proof_counts`
- `proof` (`ProgramProof`)
