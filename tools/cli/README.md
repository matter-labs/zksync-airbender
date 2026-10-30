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

## Soundness Mode

`prove`, `prove-batch`, `continue-proof` and `verify` take
`--soundness-mode pessimistic-conjecture|ethproofs-soundcalc`; the default is
`pessimistic-conjecture`, so existing invocations keep their meaning.

- `prove`, `prove-batch`: the soundness accounting of every proof layer and of
  its verifier. Each artifact records it (`soundness_mode`), and so does the
  batch summary. A mode the backend cannot prove is rejected before any input
  is read.
- `continue-proof`: the expected mode of the input artifact, also used for the
  new layers. An artifact in another mode is rejected before proving; there is
  no conversion. Continue an `ethproofs-soundcalc` artifact with
  `--soundness-mode ethproofs-soundcalc`.
- `verify`: the expected mode. The artifact's recorded mode must equal it, and
  the proof is checked with this mode's native verifier and this mode's pinned
  verifier guests. The artifact's `blake_*` tags only select among those
  guests, and the recursion chain binds that choice; no tag can select a guest
  of another mode. Artifacts from before the mode was recorded verify only as
  `pessimistic-conjecture`.
- `run`: no proof, no mode.

Status: CPU proving in `ethproofs-soundcalc` is enabled; its end-to-end
validation is still pending. The GPU backend rejects `ethproofs-soundcalc`
before reading inputs, because it does not yet implement that mode's folding
and OOD proof of work. The standalone L1 compression program
(`cargo run --release -p program_prover --features l1 --bin l1_compression`)
takes the same flag and rejects `ethproofs-soundcalc` before reading its input:
the L1 feeder/wrap/EVM profile is deferred and exists only in
`pessimistic-conjecture`.

In `ethproofs-soundcalc`, recursion chooses between unrolled and unified layers
from the measured cycle count of the selected verifier guest, not from the
pessimistic census, and requires the guest's output to equal the native
verifier's. Set `FSV_EXECUTION_LEDGER=<path>` to append one JSON line per such
guest execution: unrolled cost probes (`batch-<id>-unrolled-<chain length>`,
the number of chain layers so far), bridge inputs (`batch-<id>-bridge`) and
final rounds (`batch-<id>-unified-<round>`, from 0).
Each row records the guest's descriptor, its pinned ROM digest, the input
stream's digest and length, and the cycles and returned words or the failure.
A row records the execution only: a cost probe below the switch threshold is
not followed by a proof. `pessimistic-conjecture` uses the calibrated census and
writes no rows.

```bash
cargo run --release -p cli -- verify \
  --proof output/proof.json \
  --bin examples/basic_fibonacci/app.bin \
  --soundness-mode pessimistic-conjecture
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
- `soundness_mode`
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
