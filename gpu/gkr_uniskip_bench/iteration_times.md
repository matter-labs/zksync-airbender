# gpu_gkr_uniskip_bench — measurements

## Register gate (Task 4)

Build with the crate's nvcc diagnostic path — `gpu_native_build` turns the env var
into `-D GPU_GKR_UNISKIP_BENCH_ENABLE_BUILD_DIAG=ON`, which
`gpu/native_build/cmake/ab_cuda_target.cmake` lowers to `--ptxas-options=-v --keep`:

```
GPU_GKR_UNISKIP_BENCH_ENABLE_BUILD_DIAG=1 cargo build --release -p gpu_gkr_uniskip_bench -vv
CUDAARCHS="80;89;90" GPU_GKR_UNISKIP_BENCH_ENABLE_BUILD_DIAG=1 cargo build --release -p gpu_gkr_uniskip_bench -vv
```

Gate: ZERO spills on the eval kernel. **PASS** — no spill stores, no spill loads and
no stack frame on any kernel of any architecture, so the shared-memory accumulator
fallback (4 × 256 × 16 B) was not needed and no `__maxnreg__` was added.

| kernel | sm_120 (local) | sm_80 | sm_89 | sm_90 | stack / spill st / spill ld |
| --- | --- | --- | --- | --- | --- |
| `ab_gkr_uniskip_eval_kernel` | 54 | 55 | 48 | 48 | 0 / 0 / 0 |
| `ab_gkr_uniskip_finalize_kernel` | 32 | 29 | 28 | 32 | 0 / 0 / 0 (128 B smem) |
| `ab_gkr_uniskip_lde_e4_kernel` | 42 | 35 | 42 | 34 | 0 / 0 / 0 |
| `ab_gkr_uniskip_lde_bf_kernel` | 36 | 32 | 38 | 32 | 0 / 0 / 0 |
| `ab_gkr_uniskip_init_e4_kernel` | 32 | 32 | 29 | 30 | 0 / 0 / 0 |
| `ab_gkr_uniskip_init_bf_kernel` | 16 | 14 | 16 | 16 | 0 / 0 / 0 |

Registers are per thread. The eval kernel holds four `e4` accumulators (16 registers)
plus the operand temporaries; the accumulators are only ever indexed by
`#pragma unroll` loops, so they stay in registers. At 55 registers a 256-thread block
still reaches full occupancy on every listed architecture.

The eval kernel's descriptor is a `__grid_constant__` by-value parameter:
2864 B cmem[0] on sm_80/sm_89 (2512 B of `uniskip_vm_desc` plus the driver's
per-launch prefix), 16 B cmem[2].
