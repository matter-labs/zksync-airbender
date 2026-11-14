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
- `trusted-params`
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

## Soundness Mode

`prove`, `prove-batch`, `continue-proof` and `verify` take
`--soundness-mode pessimistic-conjecture|ethproofs-soundcalc` (default
`pessimistic-conjecture`). Artifacts record their mode; `continue-proof` and `verify`
refuse an artifact recorded in another mode and use that mode's own verifier guests.
The L1 compression/wrap/EVM profile exists only in `pessimistic-conjecture`.

## L1 Compression Checkpoint

`--target compression` continues a `recursion-unified` proof with a compression chain.
The pipeline uses the fixed compression schedule in `prover_pipeline`.

Artifacts use schema 5. The optional `l1` bundle is serialized only when present;
artifacts without it retain the existing schema-5 encoding. The `compression`
artifact is the input of the L1 wrap.

Producer commands and fixture inputs are in the
[fixture README](../../fixtures/README.md).

```bash
cargo run --release -p cli -- continue-proof \
  --proof output/recursion_unified.json \
  --bin examples/basic_fibonacci/app.bin \
  --target compression \
  --output-dir output \
  --output-file compression.json

cargo run --release -p cli -- verify \
  --proof output/compression.json \
  --bin examples/basic_fibonacci/app.bin
```

## L1 Proof

`--target l1` continues a `compression` checkpoint (or runs through it) and
proves the compression verifier's execution as one Proth120 packed unified proof
with Keccak commitments, the proof shape the EVM verifier consumes. The
artifact (schema 5) keeps the BabyBear compression sidecar and adds the `l1` bundle
(proof and operation-mode data).

```bash
cargo run --release -p cli -- continue-proof \
  --proof output/compression.json \
  --bin examples/basic_fibonacci/app.bin \
  --target l1 \
  --backend cpu \
  --output-dir output \
  --output-file l1.json

# The GPU backend produces the same bundle.
cargo run --release -p cli --features gpu -- continue-proof \
  --proof output/compression.json \
  --bin examples/basic_fibonacci/app.bin \
  --target l1 \
  --backend gpu \
  --output-dir output \
  --output-file l1.json

cargo run --release -p cli -- verify \
  --proof output/l1.json \
  --bin examples/basic_fibonacci/app.bin
```

There is no native verifier for the Proth120 proof: `verify` on an L1 artifact
checks the compression sidecar, the recursion chain and the bundle's operation mode,
and says that the Proth proof was not verified.

## Trusted Params

`trusted-params` writes the trusted verification parameters of one program and soundness
mode through `--target` (default `recursion-unified`); `--backend cpu|gpu` selects
how setup caps are computed. Compression records are available in pessimistic mode;
the L1 wrap has no trusted record. `verify --trusted-params <file>` uses these
records instead of recomputing setups.

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

`prove`, `prove-batch` and `continue-proof` write a schema 5 artifact as compact JSON without a
trailing newline. An output filename ending in `.zlib` uses zlib-compressed JSON;
`verify` and `continue-proof` select the decoder by the input filename's extension.
A malformed compressed artifact fails decoding without a JSON fallback.

The stored fields include:

- `schema_version`
- `security_level`
- `soundness_mode`
- `target`
- `batch_id`
- `cycles`
- `program_cycles` (cycles of the base layer, the program's own count)
- `program_bin_keccak`
- `program_text_keccak`
- `proof_counts`
- `proof` (`ProgramProof`)

Proving timings remain available in logs and the batch summary; they are not
stored in proof artifacts.

`RECURSION_UNROLLED_LAYERS=N` makes a recursion invocation prove exactly `N`
additional unrolled layers, bypassing the cost model, switch threshold and
monotonic-decrease check. A present value must parse as a `usize`. When unset,
the existing threshold policy applies. Bridge and final rounds are unchanged.
