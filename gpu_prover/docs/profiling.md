# `gpu_prover` Profiling

Apply the generic GPU workflow from [`../../.agents/gpu_work.md`](../../.agents/gpu_work.md) first.

Tool-specific guides:

- [`profiling_nsys.md`](./profiling_nsys.md): `nsys` capture around the existing top-level NVTX range.
- [`profiling_ncu.md`](./profiling_ncu.md): `ncu` quick kernel profiling, full-picture/source-correlated profiling, and dependency-sensitive range replay.

## Profiling Test

- Exact libtest name: `prover::tests::smoke::run_basic_unrolled_proof_job_profile_test`
- The test is `#[ignore]`; pass `--ignored` when running it.
- When using `--exact`, do not pass a suffix such as `run_basic_unrolled_proof_job_profile_test` or `tests::run_basic_unrolled_proof_job_profile_test`. Use the full libtest name above.
- The current top-level registered NVTX capture range in [`src/prover/tests/smoke.rs`](../src/prover/tests/smoke.rs) uses:
  - domain `gpu_prover.tests`
  - message `test.gpu.prove.profiled_call`
- That range is intended to capture only the profiled `prove()` call after warmup.

## Build The Test Binary

Build unlocked and capture the test binary path for profiler wrappers:

```bash
TEST_BINARY="$(
  cargo test -p gpu_prover run_basic_unrolled_proof_job_profile_test --release --no-run --message-format=json \
    | python3 .agents/bin/cargo_test_executables.py
)"
```

If you want the helper to validate the full test name and print the locked direct-run command, use:

```bash
cargo test -p gpu_prover run_basic_unrolled_proof_job_profile_test --release --no-run --message-format=json \
  | python3 .agents/bin/cargo_test_executables.py \
      --print-run-command \
      --test-name prover::tests::smoke::run_basic_unrolled_proof_job_profile_test \
      --test-arg=--ignored
```
