# Profiling GPU kernels with `nsys`

Generic Nsight Systems methodology for any `gpu/` crate. Start from
[`profiling.md`](./profiling.md) for the parameter conventions; supply
`$TEST_BINARY` and `$NVTX_RANGE` from your crate's profiling doc, and invoke
`$TEST_BINARY` with the libtest args that select + run the work to profile.

Prefer capturing an existing NVTX range instead of profiling the whole process:

```bash
.agents/bin/with_gpu_lock.sh nsys profile \
  --trace=cuda,nvtx,osrt \
  --capture-range=nvtx \
  --nvtx-capture="$NVTX_RANGE" \
  --capture-range-end=stop-shutdown \
  --output "target/profiling/nsys/$(date +%Y%m%d_%H%M%S)_profile" \
  "$TEST_BINARY" --exact <test> --nocapture
```

For phase attribution, prefer GPU-projected NVTX stats over the default CPU
NVTX range timing:

```bash
nsys stats --report nvtx_gpu_proj_sum target/profiling/nsys/<report>.nsys-rep
```

A CPU NVTX range over async GPU work usually measures *enqueue* time: the host
opens the range, schedules kernels / copies / callbacks, and closes it before
the GPU has necessarily started — let alone finished — that work.
`nvtx_gpu_proj_sum` projects each CUDA op back onto the NVTX range that enqueued
it, which is the correct view for comparing GPU cost across phases. (This matters
especially for the enqueue-only prover `prove()` path — see
[`../circuit_prover/docs/profiling.md`](../circuit_prover/docs/profiling.md).)
