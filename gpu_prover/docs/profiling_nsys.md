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
  --output "target/profiling/nsys/$(date +%Y%m%d_%H%M%S)_gpu_prover_profile" \
  "$TEST_BINARY" \
  --exact prover::tests::run_basic_unrolled_proof_job_profile_test \
  --ignored \
  --nocapture
```

For phase attribution, prefer GPU-projected NVTX stats over the default CPU
NVTX range timing:

```bash
nsys stats --report nvtx_gpu_proj_sum target/profiling/nsys/<report>.nsys-rep
```

A CPU NVTX range in this prover usually measures *enqueue* time: the host
opens the range, schedules kernels / copies / callbacks, and closes it before
the GPU has necessarily started — let alone finished — that work.
`nvtx_gpu_proj_sum` projects each CUDA op back onto the NVTX range that
enqueued it, which is the correct view for comparing GPU cost across phases.
