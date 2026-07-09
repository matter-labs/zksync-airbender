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
| `$TEST_BINARY` | the `run_basic_unrolled_proof_job_profile_test` binary (built below) |
| `$NVTX_RANGE` | `test.gpu.prove.profiled_call@circuit_prover.tests` |
| `$SOURCE_FOLDERS` | `gpu/circuit_prover/native` |
| lineinfo env | `GPU_PROVER_ENABLE_LINEINFO` |
| test-selection args | `--exact prover::tests::smoke::run_basic_unrolled_proof_job_profile_test --nocapture` |

## Profiling Test

- Exact libtest name: `prover::tests::smoke::run_basic_unrolled_proof_job_profile_test`
- The test runs by default (`#[test]` + `#[serial]`, not `#[ignore]`); do not pass `--ignored` — it matches zero tests.
- When using `--exact`, do not pass a suffix such as `run_basic_unrolled_proof_job_profile_test` or `tests::run_basic_unrolled_proof_job_profile_test`. Use the full libtest name above.
- The current top-level registered NVTX capture range in [`../src/prover/tests/smoke.rs`](../src/prover/tests/smoke.rs) uses:
  - domain `circuit_prover.tests`
  - message `test.gpu.prove.profiled_call`
- That range is intended to capture only the profiled `prove()` call after warmup.
- `prove()` is enqueue-only, so a CPU NVTX range measures enqueue time — use
  `nsys stats --report nvtx_gpu_proj_sum` for GPU-projected phase cost (see the
  generic `nsys` guide).

## Build The Test Binary

Build unlocked and capture the test binary path for profiler wrappers:

```bash
TEST_BINARY="$(
  cargo test -p circuit_prover run_basic_unrolled_proof_job_profile_test --release --no-run --message-format=json \
    | python3 .agents/bin/cargo_test_executables.py
)"
```

If you want the helper to validate the full test name and print the locked direct-run command, use:

```bash
cargo test -p circuit_prover run_basic_unrolled_proof_job_profile_test --release --no-run --message-format=json \
  | python3 .agents/bin/cargo_test_executables.py \
      --print-run-command \
      --test-name prover::tests::smoke::run_basic_unrolled_proof_job_profile_test
```
