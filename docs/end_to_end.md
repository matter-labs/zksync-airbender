# Running prover end to end

This document focuses on the Airbender side of the flow: starting from a RISC-V binary, confirming the program output, generating a proof artifact, and validating that artifact locally.

## 1. Prepare the binary and input

If you want to prove a custom program, start by checking that it runs and returns the expected output:

```shell
cargo run --release -p cli -- run --bin examples/hashed_fibonacci/app.bin --input-file examples/hashed_fibonacci/input.txt
```

Keep the final register outputs handy so you can compare them with the verified proof output later.

## 2. Generate a proof artifact

### CPU backend

```shell
cargo run --release -p cli -- prove \
  --bin examples/hashed_fibonacci/app.bin \
  --input-file examples/hashed_fibonacci/input.txt \
  --output-dir /tmp \
  --output-file proof.json
```

### GPU backend

```shell
cargo run --release -p cli --features gpu -- prove \
  --bin examples/hashed_fibonacci/app.bin \
  --input-file examples/hashed_fibonacci/input.txt \
  --output-dir /tmp \
  --output-file proof.json \
  --backend gpu
```

Notes:

- `prove` defaults to the `recursion-unified` target, so the artifact already contains the full active recursion pipeline.
- If your `.text` section is not the default sibling file, pass it explicitly with `--text`.
- If you need to tighten resource limits, use `--cpu-cycles-bound` and `--cpu-ram-bound`.

## 3. Verify the artifact

```shell
cargo run --release -p cli -- verify \
  --proof /tmp/proof.json \
  --bin examples/hashed_fibonacci/app.bin \
  --security-level 80 \
  --target recursion-unified
```

The verifier prints the public output on success. It should match the output from step 1.

## 4. Optional staged proving

If you want to keep the base proof and continue later, split the work into two steps:

```shell
cargo run --release -p cli -- prove \
  --bin examples/hashed_fibonacci/app.bin \
  --input-file examples/hashed_fibonacci/input.txt \
  --target base \
  --output-dir /tmp \
  --output-file base.json

cargo run --release -p cli -- continue-proof \
  --proof /tmp/base.json \
  --bin examples/hashed_fibonacci/app.bin \
  --security-level 80 \
  --target recursion-unified \
  --output-dir /tmp \
  --output-file proof.json
```

`continue-proof` currently supports only CPU-produced artifacts.

## 5. Optional: combine multiple proofs into one

Multiple `recursion-unified` artifacts of the same program (e.g. proofs of several
batches) can be combined into a single proof before SNARK wrapping:

```shell
cargo run --release -p cli -- combine \
  --proofs /tmp/proof_batch_1.json /tmp/proof_batch_2.json \
  --bin examples/hashed_fibonacci/app.bin \
  --security-level 80 \
  --output-dir /tmp \
  --output-file combined.json

cargo run --release -p cli -- verify \
  --proof /tmp/combined.json \
  --bin examples/hashed_fibonacci/app.bin \
  --security-level 80 \
  --target recursion-combined
```

The combined artifact proves that every input proof was verified and that all of
them belong to the same recursion chain. Words 0..8 of its public output are the
keccak rolling hash of the input proofs' outputs — `keccak(out_1[0..8]>>32 || ... ||
out_n[0..8]>>32)`, each output shifted one word right with a zero prepended, exactly
as in the pre-unrolled `CombinedMultipleRecursionLayers` flow — and words 8..16 carry
the shared recursion chain through unchanged, so the combined proof binds to the same
program as its inputs.

## 6. SNARK wrapping status

The current flow in this repository ends at a verified Airbender proof artifact.

Wrapping that artifact into a SNARK is not implemented yet, but it is expected to be supported soon. Once that lands, this document should be extended with the concrete wrapping and verification steps.
