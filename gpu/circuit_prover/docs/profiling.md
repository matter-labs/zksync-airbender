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
| `$TEST_BINARY` | the `gpu_circuit_prover` libtest binary (built below) |
| `$NVTX_RANGE` (nsys) | `test.gpu.prove.profiled_call@gpu_circuit_prover.tests` |
| `$NCU_NVTX_RANGE` (ncu) | `gpu_circuit_prover.tests@test.gpu.prove.profiled_call` |
| `$SOURCE_FOLDERS` | `gpu/trace/native gpu/gkr/native gpu/whir/native` (the apex has no native tree of its own) |
| lineinfo env | `GPU_TRACE_ENABLE_LINEINFO` / `GPU_GKR_ENABLE_LINEINFO` / `GPU_WHIR_ENABLE_LINEINFO` |
| build-diag env | `GPU_TRACE_ENABLE_BUILD_DIAG` / `GPU_GKR_ENABLE_BUILD_DIAG` / `GPU_WHIR_ENABLE_BUILD_DIAG` |
| test-selection args | `--exact baby_bear::tests::proof_matrix::profile_add_sub_lui_auipc_mop --ignored --nocapture` |

## Profiling Test

- The `canonical_matrix!` list registers one `profile_*` test per circuit. The two compression cases have no `profile_*` tests. The AddSub example uses `baby_bear::tests::proof_matrix::profile_add_sub_lui_auipc_mop`.
- The profile tests (e.g. `profile_add_sub_lui_auipc_mop`) are `#[ignore]`d; you MUST pass `--ignored` to run them. (The binary self-serializes via the pre-main `gpu_core::force_serial_libtest!()` guard — no `#[serial]` annotations exist anymore — and profiling runs a single test via `--exact` anyway.)
- Pass the full libtest name to `--exact`.
- The current registered NVTX capture range in [`../src/baby_bear/tests/proof_matrix.rs`](../src/baby_bear/tests/proof_matrix.rs) (`run_profile`) uses:
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
  cargo test -p gpu_circuit_prover profile_add_sub_lui_auipc_mop --release --no-run --message-format=json \
    | python3 .agents/bin/cargo_test_executables.py
)"
```

If you want the helper to validate the full test name and print the locked direct-run command, use:

```bash
cargo test -p gpu_circuit_prover profile_add_sub_lui_auipc_mop --release --no-run --message-format=json \
  | python3 .agents/bin/cargo_test_executables.py \
      --print-run-command \
      --test-arg=--ignored --test-name baby_bear::tests::proof_matrix::profile_add_sub_lui_auipc_mop
```
