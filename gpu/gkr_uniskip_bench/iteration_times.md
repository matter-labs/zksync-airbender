# gpu_gkr_uniskip_bench — measurements

## Register gate (Task 4, refreshed in Task 5 for the fold kernels)

Build with the crate's nvcc diagnostic path — `gpu_native_build` turns the env var
into `-D GPU_GKR_UNISKIP_BENCH_ENABLE_BUILD_DIAG=ON`, which
`gpu/native_build/cmake/ab_cuda_target.cmake` lowers to `--ptxas-options=-v --keep`:

```
GPU_GKR_UNISKIP_BENCH_ENABLE_BUILD_DIAG=1 cargo build --release -p gpu_gkr_uniskip_bench -vv
CUDAARCHS="80;89;90" GPU_GKR_UNISKIP_BENCH_ENABLE_BUILD_DIAG=1 cargo build --release -p gpu_gkr_uniskip_bench -vv
```

`CUDAARCHS` is NOT part of the cargo fingerprint: after a multi-arch diagnostic
build, `touch native/uniskip.cu` and rebuild with it unset before running on the
local device.

Gate: ZERO spills on the eval kernel. **PASS** — no spill stores, no spill loads and
no stack frame on any kernel of any architecture, so the shared-memory accumulator
fallback (4 × 256 × 16 B) was not needed and no `__maxnreg__` was added.

| kernel | sm_120 (local) | sm_80 | sm_89 | sm_90 | stack / spill st / spill ld |
| --- | --- | --- | --- | --- | --- |
| `ab_gkr_uniskip_eval_kernel` | 54 | 55 | 48 | 48 | 0 / 0 / 0 |
| `ab_gkr_uniskip_fold_e4_kernel` | 89 | 40 | 44 | 87 | 0 / 0 / 0 |
| `ab_gkr_uniskip_fold_bf_kernel` | 36 | 30 | 30 | 30 | 0 / 0 / 0 |
| `ab_gkr_uniskip_finalize_kernel` | 32 | 29 | 28 | 32 | 0 / 0 / 0 (128 B smem) |
| `ab_gkr_uniskip_lde_e4_kernel` | 42 | 35 | 42 | 34 | 0 / 0 / 0 |
| `ab_gkr_uniskip_lde_bf_kernel` | 36 | 32 | 38 | 32 | 0 / 0 / 0 |
| `ab_gkr_uniskip_init_e4_kernel` | 32 | 32 | 29 | 30 | 0 / 0 / 0 |
| `ab_gkr_uniskip_init_bf_kernel` | 16 | 14 | 14 | 16 | 0 / 0 / 0 |

Registers are per thread. The eval kernel holds four `e4` accumulators (16 registers)
plus the operand temporaries; the accumulators are only ever indexed by
`#pragma unroll` loops, so they stay in registers.

### Occupancy (corrects the Task 4 entry)

The Task 4 text claimed 55 registers "still reaches full occupancy on every listed
architecture". That is **wrong**. Blocks are 256 threads, so a block costs
`256 × regs` of the SM's 65536-register file, and full occupancy needs
`regs <= 32` on sm_80/sm_90 (2048 threads/SM) — no kernel of this bench that
matters is there.

| kernel | sm_80 | sm_89 | sm_90 | sm_120 |
| --- | --- | --- | --- | --- |
| `eval` | 4 blk, ~50% | 5 blk, ~83% | 5 blk, ~62.5% | 4 blk, ~67% |
| `fold_e4` | 6 blk, ~75% | 5 blk, ~83% | **2 blk, ~25%** | **2 blk, ~33%** |
| `fold_bf` | ~100% | ~100% | ~100% | ~100% |

(Blocks/SM = `floor(65536 / (256 × regs))`, capped by the 2048-thread limit on
sm_80/sm_90 and the 1536-thread limit on sm_89/sm_120; register allocation
granularity can only lower these, never raise them.)

`fold_e4` is the outlier: on sm_90/sm_120 ptxas hoists the whole fully unrolled
16-tap `e4` load block before the FMA chain (16 × 4 = 64 registers of loaded
operands alone), buying memory-level parallelism at the cost of occupancy. It
measures at essentially peak bandwidth anyway (see below), so this is recorded, not
a defect.

The eval kernel's descriptor is a `__grid_constant__` by-value parameter:
2864 B cmem[0] on sm_80/sm_89 (2512 B of `uniskip_vm_desc` plus the driver's
per-launch prefix), 16 B cmem[2].

## Baseline (Task 5)

```
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench \
    --log-trace 24 --warmup 10 --iterations 100
```

Device: **NVIDIA RTX PRO 6000 Blackwell Server Edition** (sm_120, 97887 MiB).
Default census (59 sources / 59 columns, 175 records, 103 coefficient
applications). `log_rows = 20`, 1048576 logical rows, 32768 eval blocks.
Tap backing 5.75 GiB (the coset backing matches); compulsory traffic
31893488128 B (29.70 GiB) per pass.

| stage | median ms | mean ms | min ms | max ms | compulsory GB/s |
| --- | --- | --- | --- | --- | --- |
| lde | 71.063 | 71.063 | 71.026 | 71.111 | 173.8 |
| eval | 19.366 | 19.367 | 19.356 | 19.384 | 638.5 |
| finalize | 0.033 | 0.033 | 0.031 | 0.035 | 512.5 |
| fold | 4.743 | 4.744 | 4.739 | 4.747 | 1510.4 |
| **total** | **95.207** | 95.206 | 95.167 | 95.248 | 335.0 |

Spread over 100 iterations is under 0.1% on every stage.

"Compulsory GB/s" divides each stage's *floor* traffic — every distinct byte it must
touch at least once, per `Harness::pass_bytes` — by its median time. It is an upper
bound on the achieved bandwidth, not a measurement of it: a stage that re-reads its
input moves more than the floor.

### Reading the numbers

- **`fold` calibrates the machine.** It reads the tap backing once and writes one
  `e4` per (source, row); floor and issued traffic are the same 7.16 GB, so its
  1510 GB/s **is** the achieved bandwidth. Treat ~1.5 TB/s as this device's
  practical streaming ceiling for the rest of the table.
- **`lde` is bandwidth-bound at 16× the floor**, not slow at the floor. Each thread
  produces one coset cell from all 16 taps of its (column, row), and the 16 threads
  that share those taps are `2^log_rows` apart in the grid-stride index — different
  blocks, scheduled far apart, with a 5.75 GiB backing between them, so nothing is
  reused in L2. Issued traffic is therefore `16 × 5.75 GiB` read + `5.75 GiB`
  written ≈ 105 GB, which over 71.06 ms is **~1477 GB/s** — the same ceiling `fold`
  hits. The stage is at the hardware limit for the traffic it generates; the lever
  is generating less of it (one thread emitting all 16 coset cells from one tap
  load), which is a v2 kernel change and explicitly out of scope here.
- **`lde` is 74.6% of the pass**, so the global coset materialization the v1 design
  deliberately measures is the whole story of this baseline. `eval` (20.3%) and
  `fold` (5.0%) are the rest.
- **`eval` is not DRAM-bound.** 12.36 GB of floor traffic in 19.37 ms is 638 GB/s,
  well under the ceiling; with ~3.8 operand references per source the issued load
  volume is several times the floor and is being served by L1/L2.
- **The eval/finalize split is not anomalous.** Task 4 flagged the eval partials
  store as one active lane per warp writing 4 scattered 16-B values; at this
  geometry that whole output is 32768 blocks × 32 cells × 16 B = 16.8 MB, i.e.
  0.14% of eval's floor traffic, and `finalize` consumes it in 0.033 ms. The store
  shape is real but amortized to nothing at benchmark size — it would only matter at
  a geometry with far more blocks per unit of work.
