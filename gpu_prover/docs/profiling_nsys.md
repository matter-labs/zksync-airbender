# `gpu_prover` Profiling with `nsys`

Start from [`profiling.md`](./profiling.md) for the shared profiling test details and the `TEST_BINARY` setup.

Prefer the existing top-level NVTX range instead of profiling the whole process:

- domain `gpu_prover.tests`
- message `test.gpu.prove.profiled_call`

```bash
.agents/bin/with_gpu_lock.sh nsys profile \
  --trace=cuda,nvtx,osrt \
  --capture-range=nvtx \
  --nvtx-capture='test.gpu.prove.profiled_call@gpu_prover.tests' \
  --capture-range-end=stop-shutdown \
  --output target/profiling/nsys/gpu_prover_profile \
  "$TEST_BINARY" \
  --exact prover::tests::run_basic_unrolled_proof_job_profile_test \
  --ignored \
  --nocapture
```
