# `circuit_prover` Profiling

The generic kernel-profiling methodology lives at the cluster level:

- [`../../docs/profiling.md`](../../docs/profiling.md) — overview + parameters
- [`../../docs/profiling_ncu.md`](../../docs/profiling_ncu.md) — `ncu` per-kernel profiling
- [`../../docs/profiling_nsys.md`](../../docs/profiling_nsys.md) — `nsys` timeline / NVTX capture

This doc supplies the prover-specific values to plug into those guides. Apply the
generic GPU workflow from [`../../../.agents/gpu_work.md`](../../../.agents/gpu_work.md) first.

## Parameters for the generic guides

| Parameter | Prover value |
|---|---|
| `$TEST_BINARY` | the `run_add_sub_profile_test` binary (built below) |
| `$NVTX_RANGE` | `test.gpu.prove.profiled_call@gpu_circuit_prover.tests` |
| `$SOURCE_FOLDERS` | `gpu/trace/native gpu/gkr/native gpu/whir/native` (the apex has no native tree of its own) |
| lineinfo env | `GPU_TRACE_ENABLE_LINEINFO` / `GPU_GKR_ENABLE_LINEINFO` / `GPU_WHIR_ENABLE_LINEINFO` |
| build-diag env | `GPU_TRACE_ENABLE_BUILD_DIAG` / `GPU_GKR_ENABLE_BUILD_DIAG` / `GPU_WHIR_ENABLE_BUILD_DIAG` |
| test-selection args | `--exact tests::proof_matrix::run_add_sub_profile_test --nocapture` |

## Profiling Test

- Exact libtest name: `tests::proof_matrix::run_add_sub_profile_test`
- The profile tests (e.g. `run_add_sub_profile_test`) are `#[ignore]`d; you MUST pass `--ignored` to run them. (The binary self-serializes via the pre-main `gpu_core::force_serial_libtest!()` guard — no `#[serial]` annotations exist anymore — and profiling runs a single test via `--exact` anyway.)
- When using `--exact`, do not pass a suffix such as `run_add_sub_profile_test` or `tests::run_add_sub_profile_test`. Use the full libtest name above.
- The current registered NVTX capture range in [`../src/tests/proof_matrix.rs`](../src/tests/proof_matrix.rs) (`run_profile`) uses:
  - domain `gpu_circuit_prover.tests`
  - message `test.gpu.prove.profiled_call`
- That range is intended to capture only the profiled `prove()` call after warmup.
- `prove()` is enqueue-only, so a CPU NVTX range measures enqueue time — use
  `nsys stats --report nvtx_gpu_proj_sum` for GPU-projected phase cost (see the
  generic `nsys` guide).

## Build The Test Binary

Build unlocked and capture the test binary path for profiler wrappers:

```bash
TEST_BINARY="$(
  cargo test -p gpu_circuit_prover run_add_sub_profile_test --release --no-run --message-format=json \
    | python3 .agents/bin/cargo_test_executables.py
)"
```

If you want the helper to validate the full test name and print the locked direct-run command, use:

```bash
cargo test -p gpu_circuit_prover run_add_sub_profile_test --release --no-run --message-format=json \
  | python3 .agents/bin/cargo_test_executables.py \
      --print-run-command \
      --test-name tests::proof_matrix::run_add_sub_profile_test
```

## Optional MAIN R0 Diagnostics

The non-default `r0_diagnostics` feature adds an experimental kernel bank and
test hooks. Default builds exclude these kernels and hooks. Build before taking
the GPU lock:

```bash
cargo nextest run -p gpu_circuit_prover --release --features r0_diagnostics --no-run
```

For a resident-input comparison of the current add/sub L0 production entry
with the other universal launch bound:

```bash
mkdir -p target/profiling/r0
AB_R0_DIAG_PAIR=corpus AB_R0_DIAG_NATIVE=3f7 AB_R0_DIAG_LAYER=0 \
AB_R0_DIAG_SAMPLES=20 AB_R0_DIAG_SESSION=0 \
AB_R0_DIAG_OUTPUT="$PWD/target/profiling/r0/add-sub-L0.csv" \
  .agents/bin/with_gpu_lock.sh cargo nextest run -p gpu_circuit_prover \
    --release --features r0_diagnostics \
    -E 'test(=tests::proof_matrix::run_add_sub_profile_test)' \
    --run-ignored only --no-capture
```

The harness checks the native mask, deduplicates identical bank entries, poisons
and compares every output limb, and injects a mismatch to check the comparison
path. After five warmups per arm it rotates arm order and records kernel CUDA
events. The CSV includes the actual mask/bound, tensor size, and descriptor
fingerprint; a companion `.descriptor.txt` contains the program. The production
launch restores partials before the rest of the proof, so these timings are
resident-kernel diagnostics, not candidate-fed proof timings.

`AB_R0_DIAG_GRID_DIVISOR` accepts powers of two for prefix-grid diagnostics;
these do not represent smaller complete circuits. `AB_R0_DIAG_EXTRA` accepts
comma-separated `compiled_mask:bound` entries from the compiled diagnostic bank.
Masks use hexadecimal without a `0x` prefix.

For candidate-fed full-proof comparisons, use `AB_R0_BANK_TABLE` instead of
`AB_R0_DIAG_PAIR`. It accepts a complete comma-separated
`native_mask:compiled_mask:bound` table covering the production dispatch map,
or `program` to reevaluate the current program selector. Set
`AB_R0_BANK_OUTPUT`, optionally `AB_R0_BANK_PAIRS` (default 20) and
`AB_R0_BANK_SESSION` (default 0), and run the same profile test. This mode records
proof CUDA-event intervals after input transfers and checks every proof against
the baseline proof. The existing CPU proof-parity tests also accept the table.
The two modes are mutually exclusive; unset the other mode's environment
variables before running. Retain device identity, launch coverage, raw samples,
and matching controls when using either mode for a performance claim.
