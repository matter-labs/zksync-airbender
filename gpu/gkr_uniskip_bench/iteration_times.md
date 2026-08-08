# gpu_gkr_uniskip_bench — measurements

## Register gate (Task 4; refreshed in Task 5 for fold, in v2 Task 0 for row-shape LDE, in v2 Task 1 for the fused eval, in v2 Task 2 for the cached eval)

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

**Run the diagnostic build with the sccache launcher out of the way** — point
`CMAKE_TOOLCHAIN_FILE` at an empty file. `--keep` does not survive sccache: the
cache key ignores it, the front-end leg's `*.cudafe1.stub.c` is not carried in the
cached artifacts, and the resulting entry then breaks *ordinary* builds of the same
translation unit with `fatal error: <tu>.cudafe1.stub.c: No such file or directory`
until it is overwritten (`SCCACHE_RECACHE=1 cargo build …`, client-side env, is the
recovery). Without the launcher the single-arch diagnostic build succeeds outright;
the multi-arch one still exits non-zero after emitting every arch's `ptxas info`
(the per-arch `--keep` intermediates collide on one filename), which is enough for
this table.

Gate: ZERO spills on the eval kernel. **PASS** — no spill stores, no spill loads and
no stack frame on any kernel of any architecture, so the shared-memory accumulator
fallback (4 × 256 × 16 B) was not needed and no `__maxnreg__` was added.

| kernel | sm_120 (local) | sm_80 | sm_89 | sm_90 | stack / spill st / spill ld |
| --- | --- | --- | --- | --- | --- |
| `ab_gkr_uniskip_eval_kernel` | 54 | 55 | 48 | 48 | 0 / 0 / 0 |
| `ab_gkr_uniskip_eval_fused_kernel` | 64 | 68 | 67 | 64 | 0 / 0 / 0 |
| `ab_gkr_uniskip_eval_fused_interleave_kernel` | 125 | 141 | 138 | 135 | 0 / 0 / 0 |
| `ab_gkr_uniskip_eval_fused_cached_kernel` | **66** | 79 | 69 | 60 | 0 / 0 / 0 (32768 B smem) |
| `ab_gkr_uniskip_eval_fused_cached_interleave_kernel` | **66** | 75 | 63 | 62 | 0 / 0 / 0 (32768 B smem) |
| `ab_gkr_uniskip_fold_e4_kernel` | 89 | 40 | 44 | 87 | 0 / 0 / 0 |
| `ab_gkr_uniskip_fold_bf_kernel` | 36 | 30 | 30 | 30 | 0 / 0 / 0 |
| `ab_gkr_uniskip_finalize_kernel` | 32 | 29 | 28 | 32 | 0 / 0 / 0 (128 B smem) |
| `ab_gkr_uniskip_lde_e4_kernel` | 42 | 35 | 42 | 34 | 0 / 0 / 0 |
| `ab_gkr_uniskip_lde_bf_kernel` | 36 | 32 | 38 | 32 | 0 / 0 / 0 |
| `ab_gkr_uniskip_lde_e4_row_kernel` | 40 | 32 | 40 | 40 | 0 / 0 / 0 |
| `ab_gkr_uniskip_lde_bf_row_kernel` | 64 | 64 | 64 | 64 | 0 / 0 / 0 |
| `ab_gkr_uniskip_init_e4_kernel` | 32 | 32 | 29 | 30 | 0 / 0 / 0 |
| `ab_gkr_uniskip_init_bf_kernel` | 16 | 14 | 14 | 16 | 0 / 0 / 0 |

Registers are per thread. The eval kernel holds four `e4` accumulators (16 registers)
plus the operand temporaries; the accumulators are only ever indexed by
`#pragma unroll` loops, so they stay in registers.

The `smem` figures are the STATIC shared bytes, from `cuobjdump -res-usage` on the
device-linked archive and confirmed by `ncu` ("Static Shared Memory Per Block" 32768,
"Driver Shared Memory Per Block" 1024). `ptxas info` does not print a `bytes smem`
line for these two kernels even though it prints one for `finalize`; the two
independent readings above are what the occupancy table below uses.

**The three non-local arches moved for the fused pair in this build** — `eval_fused`
sm_89 64 → 67, `eval_fused_interleave` sm_80 202 → 141, sm_89 134 → 138, sm_90
134 → 135 — while sm_120 is unchanged at 64/125. The only edit between the two builds
is the v2 Task 2 refactor that split the fused accessor into the
`uniskip_tap_read` / `uniskip_coset_recompute` pair the cached accessor reuses; it is
inline and semantically identical (the `q` oracle passes 32/32 in both fused arms and
the measured `eval` times are unchanged to 0.001 ms — see rung 2b). Static SASS is
*near* identical rather than identical: sm_120 `LDG` is unchanged exactly (681 for
`eval_fused`, 517 for `eval_fused_interleave`, 41 for `eval_kernel`) and `eval_kernel`'s
`IMAD` is unchanged exactly at 903, but the two fused kernels' `IMAD` moved by +32
and +19, i.e. under 1 %. Recorded as scheduling noise from the refactor, not
attributed further. (Deltas only: these were counted in their own pass over the two
builds and are not term-by-term comparable with the absolute `IMAD` totals in the
rung-2a SASS table, which come from a separate recount.)

### Occupancy (corrects the Task 4 entry)

The Task 4 text claimed 55 registers "still reaches full occupancy on every listed
architecture". That is **wrong**. Blocks are 256 threads, so a block costs
`256 × regs` of the SM's 65536-register file, and full occupancy needs
`regs <= 32` on sm_80/sm_90 (2048 threads/SM) — no kernel of this bench that
matters is there.

| kernel | sm_80 | sm_89 | sm_90 | sm_120 |
| --- | --- | --- | --- | --- |
| `eval` | 4 blk, ~50% | 5 blk, ~83% | 5 blk, ~62.5% | 4 blk, ~67% |
| `eval_fused` | 3 blk, ~37.5% | 3 blk, ~50% | 4 blk, ~50% | 4 blk, ~67% |
| `eval_fused_interleave` | **1 blk, ~12.5%** | **1 blk, ~17%** | **1 blk, ~12.5%** | **2 blk, ~33%** |
| `eval_fused_cached` | 3 blk, ~37.5% | 3 blk, ~50% | 4 blk, ~50% | **3 blk, ~50%** |
| `eval_fused_cached_interleave` | 3 blk, ~37.5% | 3 blk, ~50% | 4 blk, ~50% | **3 blk, ~50%** |
| `fold_e4` | 6 blk, ~75% | 5 blk, ~83% | **2 blk, ~25%** | **2 blk, ~33%** |
| `fold_bf` | ~100% | ~100% | ~100% | ~100% |
| `lde_e4_row` | 8 blk, ~100% | 6 blk, ~100% | 6 blk, ~75% | 6 blk, ~100% |
| `lde_bf_row` | 4 blk, ~50% | 4 blk, ~67% | 4 blk, ~50% | 4 blk, ~67% |

(Blocks/SM = `floor(65536 / (256 × regs))`, capped by the 2048-thread limit on
sm_80/sm_90 and the 1536-thread limit on sm_89/sm_120; register allocation
granularity can only lower these, never raise them. The two cached kernels take a
second cap, `floor(smem_per_SM / 33792)`: 4 on sm_80's 164 KB, **3** on the 100 KB of
sm_89 and sm_120, 6 on sm_90's 228 KB — so on sm_89/sm_120 registers and shared memory
both land on 3 and neither is slack.)

The sm_120 row of the two cached kernels is **measured, not computed**: `ncu` reports
`Block Limit Registers` 3, `Block Limit Shared Mem` 3, theoretical occupancy 50 %,
achieved 49.89 %, `Shared Memory Configuration Size` 102400 B. The cached kernels
therefore run at **1.5× the winning fused kernel's block count** despite adding 32 KB
of shared memory — the extra branch in the accessor stops ptxas hoisting four 16-tap
load blocks at once, and 125 registers fall to 66.

`fold_e4` is the outlier: on sm_90/sm_120 ptxas hoists the whole fully unrolled
16-tap `e4` load block before the FMA chain (16 × 4 = 64 registers of loaded
operands alone), buying memory-level parallelism at the cost of occupancy. It
measures at essentially peak bandwidth anyway (see below), so this is recorded, not
a defect.

The eval kernel's descriptor is a `__grid_constant__` by-value parameter:
2864 B cmem[0] on sm_80/sm_89 (2512 B of `uniskip_vm_desc` plus the driver's
per-launch prefix), 16 B cmem[2]. The fused kernels take `uniskip_fused_desc`,
which is that same struct (an empty derived class), so their cmem is unchanged.

`eval_fused_interleave` is the second outlier, at 2 blocks/SM against the block
map's 4. Under the block map the four cells a warp owns are `4w..4w+3`, so
`cell >= UNISKIP_TAPS` reduces to `w >= 4` for all four and ptxas emits ONE recompute
region; under the interleaved map the cells are `w, w+8, w+16, w+24` and `w < 8` is
not provable from `threadIdx.x`, so each of the four unrolled slots gets its own test
and its own 16-tap load block. That is the codegen difference; the register counts
are the measurement, and no separate experiment isolates the two causes from each
other. It is nonetheless the **faster** arm — see the rung-2a timings.

**`__launch_bounds__` was tried on the fused pair and rejected** — it is the obvious
way to make the cell-map A/B occupancy-neutral, and it cannot be had spill-free.
Measured on the FIRST dot form (16 × `T::fma`, before the chunking below), sm_120:

| `__launch_bounds__(256, N)` | `eval_fused` | `eval_fused_interleave` |
| --- | --- | --- |
| none | 61 regs, 0 spill | 168 regs, 0 spill |
| N = 4 | 64 regs, 0 spill | 64 regs, **664 B stack / 1336 B spill st / 1356 B spill ld** |
| N = 2 | 94 regs, 0 spill | 128 regs, **168 B stack / 168 B spill st / 168 B spill ld** |

The zero-spill gate wins, so both fused kernels ship unconstrained. The chunked dot
later brought the interleaved kernel to 125 registers on its own; the cap was not
re-tried against it.

## Baseline (Task 5)

```
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench \
    --log-trace 24 --warmup 10 --iterations 100 --lde-shape cell
```

(`--lde-shape cell` is the v1 LDE, which was the only shape when this was recorded
and is no longer the default — see the rung-1 section below. Reconfirmed on the
rung-1 build: `lde` 71.053 ms, total 95.196 ms.)

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

"Compulsory GB/s" — the column the binary prints as `min GB/s` — divides each stage's
*floor* traffic — every distinct byte it must
touch at least once, per `Harness::pass_bytes` — by its median time. It is a **lower
bound** on the achieved bandwidth, not a measurement of it: real DRAM traffic is
never below the floor and is usually above it, so a stage that re-reads its input
(the LDE does, once per coset cell) is moving several times the number shown. Read
the column as "this stage is achieving *at least* this much".

### Reading the numbers

- **`fold` calibrates the machine.** It reads the tap backing once and writes one
  `e4` per (source, row); floor and issued traffic are the same 7.16 GB, so its
  1510 GB/s **is** the achieved bandwidth — 84% of the card's ~1.8 TB/s peak. Treat
  ~1.5 TB/s as the *practical streaming ceiling* and ~1.8 TB/s as the hard one; the
  gap between them is why the derived bounds below are given as ranges.
- **`lde` is bandwidth-bound at ~16× re-read = 8.5× floor traffic**, not slow at the
  floor. Each thread produces one coset cell from all 16 taps of its (column, row),
  so the taps are *read* 16×; against the floor — which counts the coset write too —
  total traffic is `(16 read + 1 write) / (1 read + 1 write)` = **8.5×**. The two
  multipliers are not interchangeable: the printed compulsory rate is the issued
  rate *divided* by 8.5, so it is the 8.5× that **multiplies** the compulsory column
  back up to the rate the kernel actually issues (173.8 → ~1477 GB/s), not the 16×.

  *Mechanism — a residency hypothesis, not a settled fact.* The launch is
  grid-strided and clamped to `MAX_BLOCKS = 65536` blocks × 256 threads = exactly
  `2^24` threads, so the stride
  equals the grid: a thread's index advances by `2^24` per iteration, and since the
  decomposition is `job = (i >> log_rows) / 16`, `cell = (i >> log_rows) % 16`,
  `row = i mod 2^log_rows`, **each thread's `(cell, row)` is fixed for the whole
  kernel — only `job` advances**. The 16 threads that share a row's taps are
  therefore always `2^log_rows` threads = **`2^(log_rows - 8)` blocks** apart in
  dispatch order. Both LDE kernels get 6 blocks/SM (256 threads, 36/42 registers,
  1536-thread SM cap), so the device retires only **~1128 blocks concurrently**
  (188 SMs × 6).

  That dispatch geometry is exact. The step from it to "reuse ends at the residency
  boundary" is **not measured**: block residency says when a *producer block* is
  still running, and an L2 line outlives the block that filled it, so co-residency
  bounds nothing about line lifetime — it is a correlate of reuse, not a limit on
  it. Read the rest of this section as the story the sweep is consistent with, not
  as a named mechanism. **The settling measurement is per-kernel
  `ncu --metrics dram__bytes.sum` on `lde_bf` and `lde_e4` across the same sweep**:
  the residency reading predicts per-kernel DRAM volume rising toward ~16× the floor
  between `log_rows` 17 and 18 for *both* classes, a capacity reading predicts
  `lde_e4` moving first and alone. It was not run here.

  *Measured sweep* (same kernel, `--log-trace` 20…24):

  The `bf` and `e4` reuse distances are listed separately — an `e4` column is 4×
  the bytes of a `bf` one, and conflating them is what makes a capacity story look
  plausible. Both kernels see the same block spacing. Compulsory GB/s is the
  aggregate over both, which is what the bench prints.

  | log_rows | sharer spacing | `bf` reuse dist. (tap + coset) | `e4` reuse dist. | compulsory GB/s |
  | --- | --- | --- | --- | --- |
  | 16 | 256 blk | 8 MiB | 32 MiB | 805.8 |
  | 17 | 512 blk | 16 MiB | 64 MiB | 725.2 |
  | 18 | 1024 blk | 32 MiB | **128 MiB** | **183.5** ← collapse |
  | 19 | 2048 blk | 64 MiB | 256 MiB | 173.2 |
  | 20 | 4096 blk | 128 MiB | 512 MiB | 173.8 |

  The collapse lands between 512 and 1024 blocks of spacing, against the
  ~1128-block resident window — the correlation the residency reading rests on. The
  `bf` half of that row is also nowhere near a capacity boundary, but the `e4`
  column is why that needs one more step of arithmetic rather than an eyeball. This
  device's L2 is 128 MiB (`cudaDevAttrL2CacheSize` = 134217728), and at
  `log_rows 18` the `e4` reuse distance is 128 MiB *to the byte*: taken alone, the
  `e4` half of the collapse row is exactly the coincidence a capacity story wants.

  The aggregate rate argues against a *pure-`e4`* capacity story — but only under a
  premise the sweep does not measure. At `log_rows 18` the two classes carry
  52% / 48% of the **backing** bytes (768 MiB `bf`, 704 MiB `e4`; counting the write
  as well as the read leaves the split unchanged), and the kernels run back to back
  on one stream, so the aggregate is the harmonic combination
  `1 / (0.52/r_bf + 0.48/r_e4)`. That is one equation in two unknowns: the bench
  prints only the aggregate, never a per-class rate, so inverting it needs an
  assumption about `r_e4`.

  **Premise (unmeasured, monotonicity): `r_e4` at the collapse row is no better than
  the ~174 GB/s the aggregate settles to once both classes are past the cliff** —
  i.e. the collapsed `e4` rate does not improve as `log_rows` grows over 18…20.
  Under it, `1 / (0.52/725 + 0.48/174)` ≈ **288 GB/s** would be the reading if only
  `e4` had collapsed (and even perfect `bf` reuse at 1477 GB/s only reaches
  322 GB/s), whereas measured is **183.5** — which forces `r_bf` ≈ **193 GB/s**, so
  the `bf` kernel, whose reuse distance is 32 MiB (**a quarter of L2**), collapsed
  in the same step and capacity is context rather than the constraint.

  Drop the premise and the arithmetic no longer forces it: the same measured
  183.5 GB/s is equally consistent with `bf` holding the 725 GB/s it showed one step
  earlier and `r_e4` ≈ **101 GB/s**, which is exactly the pure-`e4` capacity story.
  Aggregate stage timing cannot separate the two; the per-kernel `dram__bytes.sum`
  run above can.

  *What the timing says.* At the plateau the stage moves `16 × 5.75 GiB` read +
  `5.75 GiB` written ≈ 105 GB, i.e. **~1477 GB/s over 71.06 ms** — 82% of card peak
  and the same rate `fold` reaches. Reading the whole sweep at that one constant
  rate is self-consistent: the traffic multiplier over the floor falls from 8.5× at
  the plateau to ~1.8× at `log_rows 16`, and nothing else about the kernel changes.
  Self-consistency is not confirmation; the same `ncu --metrics dram__bytes.sum` run
  measures the multiplier directly.

  *The v2 lever does not depend on which reading is right.* Under either the
  residency or the capacity story the fix is the same change to the **grid
  decomposition**: have one thread emit all 16 coset cells from a single tap load,
  which makes the reuse register-local and collapses the 16× read to 1× regardless
  of what L2 was doing, or map threads cell-major so the sharers land in the same or
  neighbouring blocks. Either way it is a v2 kernel change and explicitly out of
  scope here.
- **`lde` is 74.6% of the pass**, so the global coset materialization the v1 design
  deliberately measures is the whole story of this baseline. `eval` (20.3%) and
  `fold` (5.0%) are the rest.
- **`eval`: at least a quarter of its loads are cache-served; the table does not say
  whether DRAM is the binding constraint.** Floor over time (12.36 GB / 19.37 ms =
  638 GB/s) only establishes that eval's DRAM rate is *at least* 638 GB/s — it
  cannot show the stage is off the DRAM limit. The argument that does carry: with
  224 operand references over 59 sources, eval issues roughly 3.8× the floor in
  loads (~47 GB), while 19.37 ms of DRAM buys only ~29 GB at the 1.51 TB/s `fold`
  actually reaches, or ~35 GB even at the card's ~1.8 TB/s peak. Against the hard
  peak that is unconditional: **at least ~12 GB of the issued volume — a quarter —
  is cache-served**. Adding the further assumption that eval cannot beat the
  1.51 TB/s `fold` demonstrates raises the floor to ~18 GB (two fifths), but that
  one is conditional. Neither figure is an *upper* bound: the cache-served share
  could be anything from a quarter up to nearly all of the ~47 GB, since the
  argument only ever bounds it from below. DRAM traffic therefore sits somewhere in
  [12.4, ~35] GB, and naming the actual limiter (DRAM, L2, or issue) needs `ncu`.
- **The eval/finalize split is not anomalous.** Task 4 flagged the eval partials
  store as one active lane per warp writing 4 scattered 16-B values; at this
  geometry that whole output is 32768 blocks × 32 cells × 16 B = 16.8 MB, i.e.
  0.14% of eval's floor traffic, and `finalize` consumes it in 0.033 ms. The store
  shape is real but amortized to nothing at benchmark size — it would only matter at
  a geometry with far more blocks per unit of work.

## Rung 1 — intra-thread LDE, `--lde-shape row` (v2 Task 0)

```
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench \
    --log-trace 24 --warmup 10 --iterations 100 --lde-shape row
```

Same device, census and geometry as the Task 5 baseline. `row` is the default;
`cell` selects the v1 kernels, which are untouched and serve as the control arm.
Both shapes write the same bytes, so `--validate` and `--validate-flat-eq` at
`--log-trace 10` pin the reshape with no oracle change — both pass (LDE OK,
q 32/32, fold OK) for both shapes.

| stage | median ms | mean ms | min ms | max ms | compulsory GB/s |
| --- | --- | --- | --- | --- | --- |
| lde | **8.635** | 8.634 | 8.609 | 8.654 | 1430.1 |
| eval | 19.410 | 19.411 | 19.400 | 19.428 | 637.0 |
| finalize | 0.033 | 0.032 | 0.031 | 0.035 | 512.0 |
| fold | 4.743 | 4.743 | 4.739 | 4.747 | 1510.4 |
| **total** | **32.820** | 32.821 | 32.792 | 32.842 | 971.8 |

Against the same build's `cell` arm (`lde` 71.053 ms, total 95.196 ms): **8.23× on
the stage, 2.90× on the pass**, and `lde` drops from 74.6% of the pass to 26.3%.

The row shape reads every tap exactly once and writes every coset cell exactly
once — the 16 threads that shared a row's taps in the cell shape are one thread
(`bf`) or four adjacent lanes (`e4`), so the reuse is register-local. Issued
traffic is therefore the compulsory floor, and unlike the cell shape's column the
1430 GB/s **is** the achieved rate: 95% of the 1510 GB/s `fold` demonstrates as
this device's practical streaming ceiling, so the stage is at the streaming limit
and there is no further headroom in this kernel without cutting bytes.

**That 8.23× A/B moves two variables, not one.** Besides the grid reshape, the row
kernels load their taps with `ld_modifier::cs` where the cell kernels use
`ld_modifier::ca` (`native/uniskip.cu`: `ca` in `lde_bf`/`lde_e4`, `cs` in
`lde_bf_row`/`lde_e4_row`). Streaming is the correct operator once each tap is read
exactly once — evict-first is right for a line that is never revisited — but it is
not the reshape, and no build here isolates the two, so **8.23× is their joint
effect**. The conclusion above does not rest on the split: the row kernel's issued
traffic equals its compulsory floor by construction, and 1430 of 1510 GB/s leaves
under 5 % in the stage whatever share the operator contributed.

### Output-shape A/B (which intra-thread form to ship)

Three builds, otherwise identical; only the per-thread output form of the named
kernel changes. "16 live" = all 16 cells accumulated, then 16 stores; "serial" =
one accumulator, each cell stored as it is produced. Registers are sm_120.

| `bf` form | `e4` form | `bf` regs | `e4` regs | `lde` median ms |
| --- | --- | --- | --- | --- |
| 16 live | 16 live | 72 | 48 | 9.194 |
| serial | 16 live | 64 | 48 | 8.622 |
| serial | serial (shipped) | 64 | 40 | 8.635 |

Zero spills and no stack frame in every cell. Serializing `bf` is worth 0.572 ms
(the runs' min–max spans do not overlap); serializing `e4` costs 0.013 ms, which is
inside a single run's spread, so the two `e4` forms are a tie and the shipped build
takes the one with 8 fewer registers. The register/time correlation is **not**
attributed to occupancy — that would need `ncu`; only the counts and the times are
measured here.

## Rung 2a — fused pass, LDE on read, `--mode fused-recompute` (v2 Task 1)

```
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench \
    --log-trace 24 --warmup 10 --iterations 100 --mode fused-recompute --cell-map block
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench \
    --log-trace 24 --warmup 10 --iterations 100 --mode fused-recompute --cell-map interleave
```

Same device, census and geometry as the Task 5 baseline. The coset is never
materialized: there is no LDE launch and no coset backing, so the `lde` stage row is
the (empty) interval between two events and the resident backings drop from
**11.50 GiB to 5.75 GiB** — the mode's whole memory claim, printed as
`resident backings` at startup. `--validate` and `--validate-flat-eq` at
`--log-trace 10` pass for both cell maps (q 32/32, fold OK; the LDE check reports
`n/a` because there is no coset buffer to compare — the `q` oracle addresses all 32
cells and covers the recomputed ones).

| stage | block: median | mean | min | max | interleave: median | mean | min | max |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| lde | 0.000 | 0.001 | 0.000 | 0.002 | 0.000 | 0.001 | 0.000 | 0.002 |
| eval | **34.414** | 34.415 | 34.333 | 34.488 | **28.068** | 28.069 | 28.055 | 28.085 |
| finalize | 0.033 | 0.033 | 0.033 | 0.035 | 0.033 | 0.033 | 0.032 | 0.035 |
| fold | 4.743 | 4.742 | 4.739 | 4.747 | 4.743 | 4.743 | 4.737 | 4.749 |
| **total** | **39.190** | 39.191 | 39.114 | 39.266 | **32.845** | 32.845 | 32.828 | 32.862 |

Control arm, same build and session (`--mode unfused --lde-shape row`): `lde` 8.643,
`eval` 19.412, `finalize` 0.033, `fold` 4.743, total 32.830 ms.

**The comparison that matters is what the mode replaces**, `lde + eval + finalize`;
`fold` is identical work in both arms and is excluded from both sides.

| arm | replaces-the-LDE sum | vs the unfused 28.088 ms | resident backings |
| --- | --- | --- | --- |
| unfused, `--lde-shape row` | 8.643 + 19.412 + 0.033 = **28.088** | — | 11.50 GiB |
| fused, `--cell-map block` | 34.414 + 0.033 = **34.447** | +22.6 % | 5.75 GiB |
| fused, `--cell-map interleave` | 28.068 + 0.033 = **28.101** | **+0.05 %** | 5.75 GiB |

`interleave` is a **tie**, not a win: +0.013 ms of median is far inside the arms'
spreads (the unfused sum spans 28.044–28.139 over its 100 iterations, the fused one
28.087–28.120), so the two are indistinguishable at this geometry. What is not
inside the noise is the memory — the fused arm reaches the same time on **half the
backing**.

### Chunked wide accumulation in the coset dot (the change that moved these)

The first shipped form of the fused accessor ran the 16-tap dot as 16 `T::fma`
calls, i.e. **16 Montgomery reductions where 4 suffice**. `bf::red_wide` is
documented for inputs up to ~4p², and `4·(p−1)² = 1.62e19 < 2^64`, so four taps can
be accumulated in one `u64` with `ptx::mad_wide` before a single reduction.
Montgomery reduction is linear mod p — `red(Σ aᵢbᵢ) = Σ red(aᵢbᵢ)` — so the chunked
form is **bit-identical**, which the unchanged `q` oracle (32/32, both maps, both eq
modes) confirms rather than assumes. `e4` sources chunk the same way per limb.

Two builds, otherwise identical; only the dot form changes.

| dot form | `eval` block | `eval` interleave | fused regs sm_120 (block / interleave) |
| --- | --- | --- | --- |
| 16 × `T::fma` (first form) | 52.403 | 62.016 | 61 / 168 |
| 4 chunks of 4 + `red_wide` (shipped) | **34.414** | **28.068** | 64 / 125 |

−34.3 % and −54.7 % on the stage. The **static SASS of the two builds isolates the
mechanism** (`cuobjdump -sass` on `uniskip.cu.o`, sm_120; counts are instructions
inside each kernel's body):

| kernel | instructions | `IMAD` (mul pipe) | all-register `IMAD.WIDE` (the wide multiplies) | `LDG` |
| --- | --- | --- | --- | --- |
| `eval_fused` before | 19872 | 5928 | 1836 | 681 |
| `eval_fused` after | 11816 | **3686 (−37.8 %)** | **1836 (unchanged)** | 681 (unchanged) |
| `eval_fused_interleave` before | 18512 | 5596 | — | 517 |
| `eval_fused_interleave` after | 10760 | **3496 (−37.5 %)** | — | 517 (unchanged) |
| `eval_kernel` (unfused) | 2861 | 903 | — | 41 |

(The `eval_fused` `IMAD` totals above were independently recounted; the
`eval_fused_interleave` row was not, so read its absolutes as the original counting
pass's. The relative change is what the claim uses and it survives either way.)

The unfused kernel's SASS is **byte-identical** across the two builds, so the change
is confined to the fused accessor. The wide-multiply count is unchanged and the load
count is unchanged: the −37.8 % is the reduction chain and nothing else, which is what
"chunking removes reductions, not multiplies" predicts (the prediction going in was
≥ 30 %).

**F9, checked while in the SASS: ptxas does NOT strength-reduce the per-tap address
chain.** Each tap load still recomputes `((plane + t) << log_rows) + row` in full —
`IADD` (plane+t), `SHF.L` (<< log_rows), `IADD` (+row), `IMAD.WIDE.U32` (×4, + base)
— instead of hoisting a base and stepping by the runtime stride `1 << log_rows`.
Measured in the shipped `eval_fused` body: **739 immediate-operand `IMAD.WIDE`** —
the `× 4` element-index scale, separable from the 1836 all-register `IMAD.WIDE` that
are the dot's wide multiplies — and 695 `SHF.L`, against 3686 total `IMAD`. The scale
count is *not* one per load (739 against 681 `LDG`); the two are counted
independently and nothing here pairs them. So **739 / 3686 = 20.0 % of the remaining
mul-pipe instructions in the fused kernel are address arithmetic**, not field
arithmetic. Recorded, not acted on.

### Profile of the fused kernels

```
.agents/bin/with_gpu_lock.sh ncu --set full --metrics dram__bytes.sum \
    --kernel-name-base demangled --kernel-name 'regex:ab_gkr_uniskip_eval_fused_kernel' \
    --launch-count 1 --target-processes all -o target/profiling/ncu/<ts>_fused_block_full \
    target/release/gpu_gkr_uniskip_bench --log-trace 24 --warmup 1 --iterations 1 \
    --mode fused-recompute --cell-map block

.agents/bin/with_gpu_lock.sh ncu --set basic \
    --metrics dram__bytes.sum,sm__pipe_fmaheavy_cycles_active.avg.pct_of_peak_sustained_active \
    --kernel-name-base demangled \
    --kernel-name 'regex:ab_gkr_uniskip_eval_fused_interleave_kernel' \
    --launch-count 1 --target-processes all -o target/profiling/ncu/<ts>_fused_interleave \
    target/release/gpu_gkr_uniskip_bench --log-trace 24 --warmup 1 --iterations 1 \
    --mode fused-recompute --cell-map interleave
```

Reports under `target/profiling/ncu/` (gitignored). The interleave arm gets the
cheaper pass so the winning arm's headlines are on record too; the pipe breakdown
below is from the `--set full` pass on the block arm. Both at 32768 blocks × 256
threads.

| metric | fused block | fused interleave |
| --- | --- | --- |
| duration under the profiler | 34.97 ms | 28.92 ms |
| `dram__bytes.sum` | **13.26 GB** | **6.20 GB** |
| against the 6.19 GB floor (tap backing 5.75 GiB + partials) | **2.14×** | **1.00×** |
| Compute (SM) throughput | **68.79 %** | **72.05 %** |
| `sm__issue_active` | **50.85 %** | **51.51 %** |
| DRAM / L2 / L1TEX throughput | 23.75 / 34.47 / 26.36 % | 13.43 / 8.17 / 18.53 % |
| registers, blocks/SM | 64, 4 | 125, 2 |
| theoretical / achieved occupancy | 66.67 % / 56.58 % | 33.3 % / 33.23 % |

**Pipe breakdown** (block arm, `--set full`). The SM throughput figure is one pipe:

| pipe | % of peak sustained active |
| --- | --- |
| `sm__pipe_fmaheavy_cycles_active` | **69.01** ← equals the 68.79 % SM SOL |
| `sm__inst_executed_pipe_lsu` | 26.36 |
| `sm__inst_executed_pipe_alu` | 25.65 |
| `sm__inst_executed_pipe_adu` | 25.35 |
| `sm__inst_executed_pipe_fma` | 13.79 |

What this settles:

- **The fused kernel is mul-pipe bound — not load-bound and not DRAM-bound.** The
  fma-heavy (32-bit integer multiply) pipe accounts for the whole SM SOL at 69 %,
  against LSU 26 %, L1TEX 26 % and DRAM 24 %. The interleave arm reads the same way
  (fma-heavy 72.26 % against its 72.05 % SM SOL).
- **The within-warp tap reload is a load redundancy only, and loads are the pipe
  with headroom.** Under the block map a coset warp calls the accessor once per cell
  it owns and the four calls reload the same 16 taps — but the four cells are four
  distinct matrix rows, so **no MAC is duplicated**. Direct evidence that this is not
  what costs the time: `LDG` is unchanged by the chunking (681 static, both builds)
  while the stage fell 34 %.
- **The interleaved map reaches the compulsory DRAM floor exactly** (6.20 GB
  measured against a 6.19 GB floor, 1.00×) where the block map is at 2.14×. It runs
  at half the block map's occupancy and is still faster, which is consistent with a
  mul-pipe-bound kernel. Nothing here isolates *why* its DRAM lands on the floor, so
  that stays an observation.
- **Instruction-cache pressure is the highest counter in the whole `--set full`
  sweep**: `gcc__cache_requests_type_instruction` 84.45 % and `sm__icc_requests`
  76.63 %, both above the fma-heavy pipe. Noted, not attributed — no experiment here
  varies code footprint.

## Rung 2b — fused pass, shared-memory source cache, `--mode fused-cached` (v2 Task 2)

```
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench \
    --log-trace 24 --warmup 10 --iterations 100 --mode fused-cached \
    --cell-map {block,interleave} --term-order {census,locality}
```

Same device, census and geometry as the Task 5 baseline. The mode keeps rung 2a's
1× backing (5.75 GiB, no coset allocation) and adds a **32 KB per-block shared pool**
holding the planned sources' coset slabs for the block's 32-row tile, filled once at
tile start and read thereafter; sources with no slot keep the rung 2a recompute.

`--validate` and `--validate-flat-eq` at `--log-trace 10` pass (q 32/32, fold OK) for
all **eight** combinations of {block, interleave} × {census, locality} × {eq, flat-eq};
the LDE check reports `n/a` as in rung 2a.

### The cache plan at the default census

The binary prints this at startup in every mode (it is a property of the program):

```
cache plan
  pool                32768 B = 16 units of 2048 B
  cached sources      10 (8 bf / 2 e4), 16 of 16 units
  C  cached width     16
  Ru uncached refs    189
  C + Ru              205 (uncached baseline 326, 0.629x)
  mul-pipe ops / row  fill 7424 + uncached 133056 = 140480 (baseline 229504, 0.612x)
  slots               [(0,0,13,1), (1,1,13,1), (2,2,13,1), (3,3,12,1), (4,4,12,1),
                       (5,5,12,1), (6,48,7,4), (10,49,7,4), (14,6,3,1), (15,7,3,1)]
```

`(unit, source, refs, width)`. A unit is one `bf` plane of a slab — `UNISKIP_TAPS`
coset cells × `UNISKIP_ROWS_PER_BLOCK` rows = 2 KB — so a `bf` source costs one unit
and an `e4` source four. The plan takes the six hot `bf` columns (12–13 references
each), both hot `e4` columns (7 each, 4 units each), then two 3-reference `bf`
columns to fill the last two units. It confirms the hot-8 prior rather than assuming
it: the eight hot sources are exactly the eight highest-ranked entries.

**The cross-class key collapses to the within-class one.** Caching source `s` removes
`(refs − 1) · width` of its `refs · width` resolution dots — the fill still costs one
production per cell — and takes `width · 2048` bytes, so the *saving per byte* is
`(refs − 1) / 2048` with the width cancelled. Ranking by net BF-MAC saving per shared
byte and ranking by `refs − 1` inside a class are therefore the same order; the code
implements the per-byte form and `cpu_cache_plan_ranking` pins the equivalence.

`C`, `Ru` and the op split are the numbers the rung-3 gate — recorded in full under
*Rung 3* below — asks for:

- `C  = Σ component_width(source)` over CACHED sources = **16**
- `Ru = Σ ref_count(source) · component_width(source)` over UNCACHED sources = **189**
  (`ref_count` = lowered accessor invocations; `component_width` BF 1, E4 4)
- baseline `Σ ref_count · width` over ALL sources = 326, so `C + Ru` is **0.629×** it

The op split uses the shipped chunked dot: one 16-tap `bf`-limb dot is 16 `mad_wide`
plus 4 `red_wide` at 3 mul-pipe ops each (`mul_lo` + `mad_lo_cc` + `madc_hi_cc`) =
**28 mul-pipe ops**, and a resolution that loads its taps from global adds one
`IMAD.WIDE` element-index scale per load (F9: ptxas does not strength-reduce that
chain) = **16 more**. Per logical row:

```
fill      = C  · (UNISKIP_TAPS · 28 + 16)   [row-shaped: 16 taps loaded once per slab,
                                             all 16 cells emitted from registers]
uncached  = Ru · UNISKIP_TAPS · (28 + 16)   [every reference reloads its taps per cell]
baseline  = 326 · UNISKIP_TAPS · (28 + 16)
```

= 7 424 + 133 056 = **140 480 against 229 504**, i.e. **0.612×**. The fill is
**5.3 %** of what is left.

### Locked 2^24 timings

| arm | eval | finalize | **eval + finalize** | vs rung 2a interleave |
| --- | --- | --- | --- | --- |
| rung 2a `fused-recompute --cell-map interleave` (control) | 28.060 | 0.033 | **28.093** | — |
| `fused-cached --cell-map block --term-order census` | 26.349 | 0.033 | **26.382** | −6.1 % |
| `fused-cached --cell-map block --term-order locality` | 26.637 | 0.033 | **26.670** | −5.1 % |
| `fused-cached --cell-map interleave --term-order census` | 23.239 | 0.033 | **23.272** | −17.2 % |
| `fused-cached --cell-map interleave --term-order locality` | **23.045** | 0.033 | **23.078** | **−17.9 %** |

Medians over 100 iterations, all from one session on one build; the winner was
re-measured on the final binary at 23.052 / 0.034 (a host-side assertion is the only
difference, and 0.007 ms is 0.03 %). `fold` is 4.743 ms in every arm (identical work)
and is excluded from the comparison. Full pass including fold: **27.822 ms** for the winner
against 32.837 ms for the rung 2a control and 32.835 ms for the v1 `--lde-shape row`
pass. The unfused control in the same session: `lde` 8.643, `eval` 19.414,
`finalize` 0.033, `fold` 4.743.

**Against the task's ≤ 10 ms bar on eval + finalize this is a MISS** — 23.078 ms, a
factor 2.3 short, with the 6 ms stretch marker a factor 3.8 away. The evidence for why
is in the next two subsections: the cache removes 37 % of the resolver *dots*, the
resolver is only about 45 % of the stage, and the pool cannot grow past 16 units
without losing a block per SM.

**Interleave still wins, and now by more.** It was a tie against the unfused pass in
rung 2a; here it beats the block map by 3.3 ms (12.5 %). Both cached kernels sit at 66
registers and 3 blocks/SM, so — unlike rung 2a, where the maps differed 64 vs 125
registers — this gap is **not** an occupancy difference. Not attributed further; the
map is a compile-time template argument and both arms are measured.

**`--term-order locality` is a small win under interleave and a small loss under
block.** Interleave: 23.239 → 23.045 (−0.8 %), and the runs' spans do not overlap
(census 23.220–23.271, locality 23.032–23.067). Block: 26.349 → 26.637 (+1.1 %), spans
26.261–26.505 vs 26.577–26.705, also non-overlapping. Both effects are real at this
geometry and both are an order of magnitude smaller than the cache itself. The
ordering only moves the *uncached* sources' L1/L2 behaviour — it cannot change the
number of dots — so a sub-percent effect is the expected size; the sign flip between
maps is recorded, not explained.

### Pool-size sweep (the mechanism, and why the pool is 16 units)

Three builds, otherwise identical; only `UNISKIP_CACHE_UNITS` changes. All
`--cell-map interleave --term-order locality`, all `q` 32/32 at `--log-trace 10`.

The constant sits on **both** sides of the wire and the two must move together, so a
sweep point is an edit plus the two runs below:

```bash
# 1. set the same value in both places (8, 16 and 24 are the three built rows below;
#    the `0` row is the rung-2a fused-recompute arm, not a UNITS = 0 build):
#      src/abi.rs:              pub const UNISKIP_CACHE_UNITS: usize = 16;
#      native/uniskip_abi.cuh:  constexpr u32 UNISKIP_CACHE_UNITS = 16;
#    a legal value keeps (UNITS * UNISKIP_ROWS_PER_BLOCK) % UNISKIP_THREADS_PER_BLOCK == 0,
#    which the `static_assert` beside the constant enforces at compile time.
# 2. rebuild — the build script emits `rerun-if-changed` over all of `native/`,
#    so editing the header is enough to re-run nvcc; no `touch` needed.
cargo build --release -p gpu_gkr_uniskip_bench

# 3. re-validate before timing (a timing number for an unvalidated pool is worthless)
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench --log-trace 10 \
    --validate --mode fused-cached --cell-map interleave --term-order locality

# 4. time
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench \
    --log-trace 24 --warmup 10 --iterations 100 \
    --mode fused-cached --cell-map interleave --term-order locality
```

The `regs` / `blocks/SM` columns come from the register-gate build at the top of this
file; `C`, `Ru` and the op split are printed by the binary itself at startup.

| units | pool B | static smem/block | regs | blocks/SM | C | Ru | C + Ru | mul-pipe ops/row | `eval` median ms |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0 (rung 2a) | 0 | 0 | 125 | 2 | 0 | 326 | 326 (1.000×) | 229 504 (1.000×) | 28.060 |
| 8 | 16384 | 17408 | 68 | 3 | 8 | 245 | 253 (0.776×) | 176 192 (0.768×) | 25.698 |
| **16 (shipped)** | 32768 | 33792 | 66 | **3** | 16 | 189 | 205 (0.629×) | 140 480 (0.612×) | **23.045** |
| 24 | 49152 | 50176 | 66 | **2** | 24 | 165 | 189 (0.580×) | 127 296 (0.555×) | 25.397 |

This is the sweep the mechanism claim rests on, and it says two things.

- **At constant occupancy, time tracks the modelled resolver work.** 8 → 16 units
  removes 35 712 mul-pipe ops per row (20.3 % of the 8-unit arm's) and 2.653 ms
  (10.3 %). A two-point linear fit `T = A + B · W` over those two arms gives
  `B = 7.43e-5 ms` per op-unit and `A = 12.61 ms`, i.e. the **resolver is ≈ 45 % of
  the winning `eval` stage** and the other ≈ 12.6 ms is term arithmetic, the `H`-cell
  loads, `eq`, the warp reduction and the program walk. Consistency check, not part of
  the fit: extrapolating the same line to 0 units predicts 29.7 ms against the
  measured 28.1 ms — 5.7 % high, in the direction the rung 2a arm's missing cache-read
  overhead and different register allocation would put it.
- **16 units is the ceiling, and the cliff is measured, not assumed.** 24 units has
  strictly less modelled work than 16 and is 2.35 ms **slower**, because
  49152 + 1024 B of shared memory per block only fits twice into sm_120's 102400 B
  while 33792 fits three times. 17 units would already be 34816 + 1024 = 35840 B and
  drop to 2 blocks — so 16 is the largest pool that keeps 3 blocks/SM, and the brief's
  "8 BF slabs + 2 E4 slabs = 32 KB" target lands exactly on it. (The static shared
  limit, 48 KB without an opt-in, is the *second* ceiling and is never reached first.)

### Profile of the winning mode

```
.agents/bin/with_gpu_lock.sh ncu --set full --metrics dram__bytes.sum \
    --kernel-name-base demangled \
    --kernel-name 'regex:ab_gkr_uniskip_eval_fused_cached_interleave_kernel' \
    --launch-count 1 --target-processes all \
    -o target/profiling/ncu/<ts>_cached_il_locality_full \
    target/release/gpu_gkr_uniskip_bench --log-trace 24 --warmup 1 --iterations 1 \
    --mode fused-cached --cell-map interleave --term-order locality
```

| metric | rung 2a fused interleave | **rung 2b fused-cached interleave** |
| --- | --- | --- |
| duration under the profiler | 28.92 ms | **23.79 ms** |
| `dram__bytes.sum` | 6.20 GB | **6.24 GB** |
| against the 6.19 GB compulsory floor | 1.00× | **1.008×** |
| Compute (SM) throughput | 72.05 % | **74.92 %** |
| `sm__pipe_fmaheavy_cycles_active` | 72.26 % | **75.26 %** |
| `smsp__issue_active` | 51.51 % | **58.47 %** |
| DRAM / L2 / L1TEX throughput | 13.43 / 8.17 / 18.53 % | **16.43 / 14.62 / 27.53 %** |
| L1 / L2 hit rate | — | 88.69 % / 78.47 % |
| registers, blocks/SM | 125, 2 | **66, 3** |
| theoretical / achieved occupancy | 33.3 % / 33.23 % | **50 % / 49.89 %** |

Warp-stall shares (PC sampling, `selected` excluded so these are stalls only):

| stall reason | share |
| --- | --- |
| `wait` (fixed-latency dependency) | 24.8 % |
| `not_selected` | 19.2 % |
| `long_scoreboard` (global load latency) | 17.5 % |
| `math_pipe_throttle` | 17.5 % |
| `dispatch_stall` | 9.7 % |
| `short_scoreboard` | 4.9 % |
| `no_instructions` | 4.4 % |
| `mio_throttle` | 1.0 % |
| `branch_resolving` | 1.0 % |

What this settles:

- **The mode is still mul-pipe bound and still nowhere near DRAM.** `fmaheavy`
  75.26 % is the whole 74.92 % SM SOL, exactly as in rung 2a, while DRAM throughput is
  16.43 % and the issued volume is 1.008× the compulsory floor. `math_pipe_throttle` +
  `dispatch_stall` + `wait` is 52 % of stalls. Removing resolution MACs is still the
  lever; the cache just cannot remove enough of them under the byte budget.
- **The shared reads are conflict-free where it matters.** 71.8 M shared load
  wavefronts carry 14 741 bank conflicts (0.02 %); the 11 % conflict rate is on the
  9.5 M *store* wavefronts, i.e. inside the fill, and 9.5 M is 12 % of the shared
  traffic. Lane = row inside the tile is what buys this.
- **Instruction fetch is not the wall.** `no_instructions` is 4.4 % of stalls and the
  ICC hit rate is 94.9 %, against rung 2a's 84.45 % instruction-request reading that
  was flagged as a warning. The cached kernel is larger in static SASS (13 568 vs
  10 816 instructions for the interleave pair) and still does not pay for it here.
- **`long_scoreboard` at 17.5 % is the remaining memory-side term** and it is the
  `H`-cell loads, which the cache does not touch: an `H` cell is a direct tap load in
  every fused mode. Caching taps as well as coset cells would need a second unit per
  source — the budget is already spent (see the sweep) — so this is recorded, not
  acted on.

## Rung 3 — NTT-form producer: SKIPPED against a quantitative gate

Rung 3 of the ladder was to replace the 16 × 16 matrix apply that produces coset cells
with an NTT-form producer (a length-16 transform per column, reusing the twiddle
structure of the extension). **No such kernel was built.** It was not dropped
silently: the ladder gated it on a measured materiality bound and the bound failed.
The gate, the numbers and the arithmetic are recorded here so the decision can be
re-run rather than re-litigated.

**The gate.** An NTT producer can only replace resolution work that produces *all 16*
coset cells of a source together, so its reach is the CACHED share of resolution —
the fill — and not the uncached recompute, which resolves one cell at a time. The
whole-stage bound is therefore

```
saving ≤ stage_share_resolver · s · C / (C + Ru)      of eval + finalize (fold excluded)
```

with the three factors as follows, all on the winning
`fused-cached --cell-map interleave --term-order locality` arm:

| factor | value | where it comes from |
| --- | --- | --- |
| `C / (C + Ru)` | 16 / 205 = **7.8 %** | the shipped `cache::plan()` at the default census — printed by the binary, tabulated in rung 2b |
| `stage_share_resolver` | **0.45** | the pool sweep's two-point fit above (8 → 16 units), not a single-point estimate |
| `s` (fraction of a producer's work an NTT form removes) | **0.37–0.6** cycle-aware; **0.805** at the most optimistic reading | see below |

`s` is the one soft factor. On a *multiply count* an NTT form looks like 0.805: a
length-16 radix-2 transform is 17 + 16 + 17 = 50 non-trivial multiplies over 16
elements = 3.125/element against the matrix apply's 16/element, so `1 − 3.125/16` =
103/128 ≈ **0.805** removed — and only with explicit unity elimination, since the
twiddles are `__constant__` data the compiler cannot fold. But **multiply count is not
cycle count here**: the shipped matrix resolution uses the chunked wide dot (4
`mad_wide` + one `red_wide` per 4 taps), which rung 2b's own op accounting prices at
**28** mul-pipe ops per element with the taps already in registers — the row-shaped
fill, which is the NTT-eligible half — and **44** when each cell reloads its taps from
global (the extra 16 are F9's `IMAD.WIDE` address chain), while NTT butterflies are full
Montgomery multiplies at ≈ 12.5–20. The gate addendum
(`.agents/audits/2026-08-07-gkr-uniskip-bench-v2-task3-gate.md`) took **≈ 32** as a round
mid-estimate inside that 28–44 band and read `1 − 20/32` … `1 − 12.5/32` = **0.37–0.6**;
that is the `s` range carried below. Which point in the band is taken does not change the
outcome: the `s`-free ceiling derived at the end of this section (an infinitely fast fill
saves at most ≈ 0.55 ms) misses the 1 ms bar on its own, for every admissible `s`.

**The bar** (set before the measurement, to keep it a gate and not a rationalization):
build rung 3 only if the optimistic whole-stage saving is **≥ 5 % of eval + finalize
AND ≥ 1 ms absolute**.

**The answer.** `0.45 · s · 0.078` of the winner's 23.078 ms:

| `s` | bound, % of eval + finalize | bound, ms | short of the 5 % bar by | short of the 1 ms bar by |
| --- | --- | --- | --- | --- |
| 0.37 (cycle-aware, pessimistic) | 1.30 % | **0.30** | 3.8× | 3.3× |
| 0.805 (multiply-count, optimistic) | 2.83 % | **0.65** | 1.8× | 1.5× |

So the bound misses **by ≈ 1.5–3.8×**, depending on which bar and which end of the
admissible `s` range is taken — it is not a uniform factor of two or more, and the
1 ms bar at `s = 0.805` is the closest call at 1.5×. It stays under both bars for any
`stage_share_resolver` up to ~0.6 even at the optimistic `s`.

An independent and tighter statement of the same thing, which needs no `s` at all:
the fill is 7 424 of the 140 480 resolver mul-pipe ops per row = **5.3 %** of
resolution = 2.4 % of the `eval` stage at the measured 45 % resolver share, so **an
infinitely fast fill saves at most ≈ 0.55 ms of 23.08 ms**. The fused-cached leg
cannot clear a 1 ms bar even if the producer were free. Note also that the `C/(C+Ru)`
form is the *more generous* of the two — 7.8 % in dot units against 5.3 % in
op-consistent units — so the skip is recorded on the arithmetic that favours building
it.

**The second leg — an NTT-form row-shape LDE (`--lde-shape row`) — is skipped for a
different reason:** that kernel is already at its traffic floor. Rung 1 measures
8.635 ms against a 12.35 GB compulsory floor, which is 8.18 ms at the 1510 GB/s `fold`
demonstrates as this device's practical streaming ceiling (6.86 ms at the ~1.8 TB/s
hard peak). That is under 0.5 ms of headroom against the practical ceiling, and a
cheaper producer moves no bytes — it cannot help a stage whose cost is bytes. The
row-shape LDE is also not on the winning fused path at all, which has no LDE stage.

**Prerequisites.** The gate had two. Prerequisite 1 — the winning mode is compute-bound
with DRAM unsaturated — is **met** (`fmaheavy` 75.26 % ≈ the 74.92 % SM SOL, DRAM
throughput 16.43 %, issued volume 1.008× the compulsory floor). Prerequisite 2 — the
all-cell fill is a material contributor — is what **fails**. Occupancy, spill and
instruction-fetch behaviour were explicitly *not* prerequisites; they are unknowable
before a kernel exists and an end-to-end A/B dominates them as proxies.

**When to re-run this gate.** If the census ever shifts the cached share materially — a
real circuit program with a heavier hot set, or more shared memory per block on a
future part — recompute `C` and `Ru` with the shipped `cache::plan()` (the binary
prints them at startup in every mode), re-fit `stage_share_resolver` with a two-point
pool sweep as above, and re-evaluate. The formula and the fit method are the reusable
pieces; the 7.8 % and the 0.45 are properties of *this* census on *this* part.

## The v2 ladder — closing A/B

Every arm of the ladder, one table. Device: **NVIDIA RTX PRO 6000 Blackwell Server
Edition** (sm_120), default census (59 sources / 175 records / 103 coefficient
applications), `--log-trace 24` = `log_rows 20` = 1048576 logical rows, medians over
`--warmup 10 --iterations 100`. **All 12 legal arms pass `--validate` and
`--validate-flat-eq` at `--log-trace 10`** (q 32/32, fold OK) — the full 24-cell matrix
is tabulated in the next subsection, run rather than inferred; the fused arms report the
LDE check as `n/a` because they allocate no coset buffer.

### Validation matrix — all 24 cells

The legal flag matrix is 3 modes × 2 grid knobs × 2 term orders = 12 arms (a grid knob
only applies to the mode that runs that grid, which `main.rs` rejects otherwise), each
run under both eq modes. Every cell below was executed at `--log-trace 10` on the device
above; `pass` = `q validate: OK (32/32)` and `fold validate: OK`.

| # | mode | shape / cell map | `--term-order` | `--validate` | `--validate-flat-eq` | LDE leg | recorded in |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | `unfused` | `--lde-shape cell` | `census` | pass | pass | OK | rung 1 |
| 2 | `unfused` | `--lde-shape cell` | `locality` | pass | pass | OK | below |
| 3 | `unfused` | `--lde-shape row` | `census` | pass | pass | OK | rung 1 |
| 4 | `unfused` | `--lde-shape row` | `locality` | pass | pass | OK | below |
| 5 | `fused-recompute` | `--cell-map block` | `census` | pass | pass | `n/a` | rung 2a |
| 6 | `fused-recompute` | `--cell-map block` | `locality` | pass | pass | `n/a` | below |
| 7 | `fused-recompute` | `--cell-map interleave` | `census` | pass | pass | `n/a` | rung 2a |
| 8 | `fused-recompute` | `--cell-map interleave` | `locality` | pass | pass | `n/a` | below |
| 9 | `fused-cached` | `--cell-map block` | `census` | pass | pass | `n/a` | rung 2b |
| 10 | `fused-cached` | `--cell-map block` | `locality` | pass | pass | `n/a` | rung 2b |
| 11 | `fused-cached` | `--cell-map interleave` | `census` | pass | pass | `n/a` | rung 2b |
| 12 | `fused-cached` | `--cell-map interleave` | `locality` | pass | pass | `n/a` | rung 2b |

The eight `locality` cells of rows 2, 4, 6 and 8 were the matrix's gap — `--term-order
locality` had only ever been validated on the `fused-cached` mode (rung 2b's eight
combinations). They were run as:

```
cargo build --release -p gpu_gkr_uniskip_bench

for eq in --validate --validate-flat-eq; do
  for arm in "--mode unfused --lde-shape cell" \
             "--mode unfused --lde-shape row" \
             "--mode fused-recompute --cell-map block" \
             "--mode fused-recompute --cell-map interleave"; do
    .agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench \
        --log-trace 10 --term-order locality $arm $eq
  done
done
```

All eight report `q validate: OK (32/32)` and `fold validate: OK`; the two `unfused`
shapes additionally report `LDE validate: OK` and the two `fused-recompute` maps
`LDE validate: n/a (no coset backing)`. Every run prints the same plan census
(`C 16 Ru 189`), which is a program property and therefore mode-independent.

### Every arm at `--log-trace 24`

| # | arm (flags beyond `--log-trace 24 --warmup 10 --iterations 100`) | `lde` | `eval` | `finalize` | **pass − fold** | `fold` | pass total |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | v1 baseline: `--mode unfused --lde-shape cell` | 71.063 | 19.366 | 0.033 | **90.462** | 4.743 | 95.207 |
| 2 | rung 1: `--mode unfused --lde-shape row` | 8.635 | 19.410 | 0.033 | **28.078** | 4.743 | 32.820 |
| 3 | rung 2a: `--mode fused-recompute --cell-map block` | — | 34.414 | 0.033 | **34.447** | 4.743 | 39.190 |
| 4 | rung 2a: `--mode fused-recompute --cell-map interleave` | — | 28.068 | 0.033 | **28.101** | 4.743 | 32.845 |
| 5 | rung 2b: `--mode fused-cached --cell-map block --term-order census` | — | 26.349 | 0.033 | **26.382** | 4.743 | 31.125 † |
| 6 | rung 2b: `--mode fused-cached --cell-map block --term-order locality` | — | 26.637 | 0.033 | **26.670** | 4.743 | 31.413 † |
| 7 | rung 2b: `--mode fused-cached --cell-map interleave --term-order census` | — | 23.239 | 0.033 | **23.272** | 4.743 | 28.015 † |
| 8 | **rung 2b: `--mode fused-cached --cell-map interleave --term-order locality`** | — | **23.045** | 0.033 | **23.078** | 4.743 | **27.822** |
| — | rung 3: NTT-form producer | not built — skipped against the measured gate above | | | | | |

All figures in ms. `lde` is `—` in a fused mode because there is no LDE launch: the
stage row the binary prints is the (empty) interval between two events.

**`pass − fold` is the column that compares the arms.** `fold` is identical work in
every mode and cannot be fused into `eval` — its challenge depends on `q` through the
transcript — so it is excluded from both sides of every comparison here. It is also
already at its floor (below).

† Rows 5–7's pass totals are arithmetic (`pass − fold` + 4.743); the rung-2b session
recorded `eval`/`finalize` per arm and confirmed `fold` at 4.743 ms in all of them.
Rows 1–4 and 8 are measured pass medians. Row 8's measured 27.822 against the
arithmetic 27.821 is the usual artefact of taking each stage's median independently —
stage medians need not sum to the total's median.

**Cross-session comparability.** Rows 5–8 come from one session; rows 1–2 and 3–4 from
two others. The rung-2b session re-measured row 4 as its control and read 28.093 ms
against the 28.101 ms in the table (0.03 %), and re-measured row 2's unfused control at
`lde` 8.643 / `eval` 19.414 / `finalize` 0.033 against 8.635 / 19.410 / 0.033. The three
sessions are directly comparable at that level; nothing in the table turns on a
difference smaller than 0.1 ms.

### What each rung bought

| # | arm | pass − fold | × row 1 (v1) | × row 2 (rung 1) | resident backings | `dram__bytes.sum` (`ncu`) | × the fused 6.19 GB floor |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | unfused, cell LDE | 90.462 | 1.00× | 0.31× | 11.50 GiB | not profiled | — |
| 2 | unfused, row LDE | 28.078 | 3.22× | 1.00× | 11.50 GiB | not profiled | — |
| 3 | fused-recompute, block | 34.447 | 2.63× | 0.82× | **5.75 GiB** | **13.26 GB** | 2.14× |
| 4 | fused-recompute, interleave | 28.101 | 3.22× | 1.00× | **5.75 GiB** | **6.20 GB** | **1.00×** |
| 5 | fused-cached, block, census | 26.382 | 3.43× | 1.06× | **5.75 GiB** | not profiled | — |
| 6 | fused-cached, block, locality | 26.670 | 3.39× | 1.05× | **5.75 GiB** | not profiled | — |
| 7 | fused-cached, interleave, census | 23.272 | 3.89× | 1.21× | **5.75 GiB** | not profiled | — |
| 8 | **fused-cached, interleave, locality** | **23.078** | **3.92×** | **1.22×** | **5.75 GiB** | **6.24 GB** | **1.008×** |

DRAM bytes are `ncu --metrics dram__bytes.sum` on the eval kernel of a
`--warmup 1 --iterations 1` run (commands in the rung 2a / 2b sections); the floor is
the fused `eval`'s compulsory traffic, 6.19 GB = the 5.75 GiB tap backing plus the
block partials. The unfused arms were not profiled: their `lde` + `eval` compulsory
floor is 12.35 + 12.36 = 24.7 GB, and for the row shape the issued traffic is argued —
not measured — to equal it, since each tap is read once and each coset cell written
once by construction.

Reading the two tables together, in order:

- **Rung 1 (8.23× on the stage) is a re-decomposition, not a faster kernel.** The v1
  cell shape re-reads a row's 16 taps once per coset cell; the row shape reads them
  once and emits all 16 from registers. Measured, not inferred: the row kernel's
  1430 GB/s is 95 % of the 1510 GB/s `fold` demonstrates as this device's practical
  streaming ceiling. Caveat carried from rung 1: that A/B also changed the tap load's
  cache operator (`ca` → `cs`), so the 8.23× is the joint effect of two variables.
- **Rung 2a is not a time win — it is the same time on half the memory.** Row 4 against
  row 2 is +0.023 ms (+0.08 %), far inside both arms' 100-iteration spreads
  (28.044–28.139 unfused, 28.087–28.120 fused), on 5.75 GiB instead of 11.50 GiB. The
  cell map is what decides the arm: `block` (row 3) is +22.6 %, a 6.35 ms gap. What is
  *measured* about that gap is traffic — the block map issues 13.26 GB against the
  interleaved map's 6.20 GB, and the extra 7.06 GB is ~4.7 ms at the 1510 GB/s `fold`
  demonstrates, i.e. about three quarters of it. The structural difference between the
  maps is also a fact (`block` gives warp `w` cells `4w..4w+3`, so warps 4–7 own every
  coset cell and carry every recompute; `interleave` gives each warp two `H` and two
  coset cells), but **that this is what costs the time is a hypothesis** — the rung-2a
  profile section records the register and occupancy difference and explicitly declines
  to attribute the map difference, and nothing in this crate isolates the two.
- **Rung 2b is the only rung that buys time on the fused path**, −5.02 ms (−17.9 %)
  from row 4 to row 8. The mechanism is the pool sweep, not a single point: at constant
  occupancy (8 → 16 units) time tracks modelled resolver work, and 24 units has strictly
  less modelled work yet runs 2.35 ms slower because 49152 + 1024 B fits an sm_120 SM
  only twice. `--term-order locality` is a genuine but sub-percent effect on top
  (−0.8 % under `interleave`, +1.1 % under `block`, non-overlapping spans both ways).
- **The whole ladder is 3.92× on `pass − fold` and 3.42× on the full pass**
  (95.207 → 27.822), at half the resident device memory.

### Against the floors

Two floors matter here. `fold`'s is binding and always was; the fused pass's is now
reached and has stopped being the constraint.

- **`fold` is the calibration and is at its own floor in every mode.** It reads the tap
  backing once and writes one `e4` per (source, row); issued traffic equals the 7.16 GB
  floor, so its 1510 GB/s **is** the achieved bandwidth — 84 % of the card's ~1.8 TB/s
  peak. 4.743 ms is what that work costs on this part. Nothing in the ladder touches it
  and nothing could: fusing it is impossible, not deferred.
- **The DRAM floor of a fused pass is reached and is no longer the constraint.** The
  fused `eval` floor is 6.19 GB, i.e. **4.10 ms at the 1510 GB/s `fold` demonstrates**
  and **3.44 ms at the ~1.8 TB/s hard peak** — the ladder's headline "~3.9 ms floor"
  sits inside that bracket. Row 8 measures 6.24 GB issued, **1.008× the floor**: the
  traffic gap is closed to eight parts in a thousand. What remains is not traffic. Row 8
  is 5.6× the practical-ceiling floor time and the `ncu` profile says why: `fmaheavy`
  75.26 % accounts for the whole 74.92 % SM SOL, DRAM throughput is 16.43 %, and
  `math_pipe_throttle` + `dispatch_stall` + `wait` is 52 % of stalls. **The remaining
  5.6× is arithmetic, and a bandwidth floor is the wrong bar for it.**
- A floor comparison on the unfused `eval` was never the right bar either: `eval` was
  not DRAM-bound in v1, and at least a quarter of its issued load volume is
  cache-served (that bound is unconditional against the card's hard peak; see the
  baseline section).

The summary of where the time went: v1 spent 74.6 % of its pass in the LDE stage, most
of it on a 16× tap re-read rather than on the coset write itself. Rung 1 removed the
re-read, rung 2a removed the write and the buffer, rung 2b removed a third of the
resolver's dots — and what is left is a multiply-pipe benchmark sitting on top of a
memory system that is no longer being asked for anything it cannot supply.

### Per-variable, against the windowed reference point

**The reference number is external.** ~14 ms for 3 rounds, fold excluded, is the repo
owner's quoted figure for the separate *windowed*-sumcheck bench on the same device
class. It was **not** measured by this crate, it runs a different program, and no
controlled A/B exists between the two. Treat it as a scale marker, not as a result.

**CORRECTED BASIS (2026-08-08).** An earlier revision of this section divided each pass
by the number of bits it peels — 4 for uniskip k = 4, 3 for the windowed reference — and
reported 5.77 vs 4.67 ms/bit, 1.24x. **That form overcredits multi-bit passes and the
numbers it produced are withdrawn.** Peeling is sequential and each peeled bit halves the
instance, so a k-bit pass at size `N` replaces single-bit work of
`N * (2 - 2^(1-k))` halving-adjusted **units**, not `k * N`: the later bits a bigger pass
claims credit for are the nearly-free ones. w = 3 buys **1.75** units, k = 4 buys
**1.875** — not 3 and 4. Equivalently, multiply a pass by the tail factor
`1 / (1 - 2^-k)` for a run-to-completion total. Raw pass times below are untouched; only
the derived comparison changes.

The reference is therefore 14 / 1.75 = **8.00 ms per unit** (tail-total 16.0 ms), and
each uniskip arm is its `pass − fold` divided by 1.875. Fold is excluded on both sides —
the quoted windowed figure excludes it, and uniskip's `fold` is a separate stage; note
that k = 4 crosses a pass boundary every 4 bits against w = 3's every 3, so its
fold/boundary amortization is a small **uncounted credit to uniskip** in what follows.

| # | arm | pass − fold | ms per **unit** (÷ 1.875) | × the 8.00 ms/unit reference | tail-total (× 16/15) |
| --- | --- | --- | --- | --- | --- |
| 1 | unfused, cell LDE (v1) | 90.462 | 48.25 | 6.03× | 96.49 |
| 2 | unfused, row LDE | 28.078 | 14.97 | 1.87× | 29.95 |
| 3 | fused-recompute, block | 34.447 | 18.37 | 2.30× | 36.74 |
| 4 | fused-recompute, interleave | 28.101 | 14.99 | 1.87× | 29.98 |
| 5 | fused-cached, block, census | 26.382 | 14.07 | 1.76× | 28.14 |
| 6 | fused-cached, block, locality | 26.670 | 14.22 | 1.78× | 28.45 |
| 7 | fused-cached, interleave, census | 23.272 | 12.41 | 1.55× | 24.82 |
| 8 | **fused-cached, interleave, locality** | **23.078** | **12.31** | **1.54×** | **24.62** |

Windowed parity for a k = 4 pass is therefore **15.0 ms** of `eval + finalize`
(`8.00 x 1.875`), not the 18.7 the per-bit form implied. The gate-eval framing corrects
the same way: uniskip runs the gate program 2x per element and windowed 3.375x, which per
unit is 1.067 against 1.929 — uniskip does **1.81x** fewer gate evaluations per unit, not
the 2.25x the per-bit form gave.

**Verdict: the ladder narrowed the gap from 6.03× to 1.54× — and did not close it.** On
this synthetic program, at this geometry, on this part, uniskip k = 4 still costs about
a half more per halving-adjusted unit than the windowed reference point. Four caveats,
all of which have to travel with that number:

- **Stage inclusion.** Uniskip's side is `lde + eval + finalize`; the windowed side is
  its round work as quoted. Both exclude fold. If uniskip's fold is put back it is
  (23.078 + 4.743) / 1.875 = **14.84 ms/unit**, i.e. 1.85x the reference — but the
  windowed side's fold-equivalent is unknown, so that pairing is not fair either.
  Nothing here lets the two be compared fold-inclusive.
- **Different programs.** This bench runs a deterministic synthetic program pinned to
  the *census* of the round-0/layer-0 add/sub circuit, with a synthetic group-type mix,
  a synthetic `eq` and a synthetic operand-reuse pattern. The windowed number is from a
  different harness on different work.
- **Different objects.** A uniskip pass evaluates 32 cells per logical row; that
  32-cell evaluation set is precisely what buys the 4 variables. The two are not the
  same unit of work scaled — the per-variable division is the fairest single number
  available, not an equivalence.
- **One geometry.** Everything above is `--log-trace 24`. The `lde` sweep in the
  baseline section shows this device's behaviour changes qualitatively below
  `log_rows 18`; no per-variable comparison was run at another size.

What the number does support: **uniskip's remaining disadvantage is arithmetic, not
traffic** — that part is `ncu`-backed (previous subsection). *Which* arithmetic lever
would move it is not measured anywhere here. The 16 × 16 apply is the standing MMA
candidate on shape alone; the one producer change that was in scope, rung 3's NTT
form, was priced and skipped. Read "reduce mul-pipe work" as the direction, not as a
plan with a number on it.

### Recommended mode

**`--mode fused-cached --cell-map interleave --term-order locality`** — row 8. It is
the fastest arm measured (23.078 ms `pass − fold`, 3.92× v1 on that column, 1.22× the
best unfused arm), on the smallest resident footprint (5.75 GiB, half the unfused
arms), with issued DRAM traffic at 1.008× the compulsory floor. Within the interleaved
pair it is also the better register/occupancy point — 66 registers, 3 blocks/SM, zero
spills against `fused-recompute --cell-map interleave`'s 125 / 2.

**It does not win on every axis, and the exception is worth stating.** The block-map
`eval_fused` kernel is 64 registers and 4 blocks/SM (~67 % theoretical occupancy on
sm_120) against the cached kernel's 66 / 3 / ~50 % — better on both counts — and is
11.37 ms slower. Occupancy is not what orders these arms — rung 2a already had the
lower-occupancy map winning, which its profile section records as consistent with a
mul-pipe-bound kernel. Row 8's strict win is **time**; on resident footprint it ties
the other fused arms (the shared 5.75 GiB), and on issued DRAM traffic it sits at
1.008× the floor against the recompute-interleave arm's 1.00× — and that is the claim.

The other modes keep their reasons to exist:

- **`--mode fused-recompute --cell-map interleave`** — the no-shared-memory fallback.
  Same 5.75 GiB and the same DRAM floor behaviour (1.00×), +5.02 ms (+21.8 %), but it
  allocates no shared pool. The pool sweep is the reason to keep it reachable: the
  cached kernels need 33792 B/block to fit 3 blocks on an SM, and 17 units would already
  drop that to 2. A census or a part that pushes the pool over the local cliff makes
  this the fused arm to run.
- **`--mode unfused`** — the only mode that materializes the coset, so the only one
  where `--validate`'s LDE leg is live (the fused modes report it `n/a` and rely on the
  `q` oracle to cover recomputed and cached cells). Both `--lde-shape` arms carry that
  leg; **`row`** is the recommended shape (8.635 ms `lde` against `cell`'s 71.063) and
  is also the ladder's control arm. `--mode unfused --lde-shape row` remains the
  binary's CLI default for both reasons: a bare run should report the reference pass and
  exercise the full validation surface, not the winner.
- **`--lde-shape cell`** and **`--cell-map block`** are v1 control arms, kept unaltered
  so the A/Bs above stay reproducible. Neither is a recommendation.

Scope, unchanged by any of this: the program, the `eq` tables and the operand-reuse
pattern are synthetic (see the README's limitations), so "fastest arm" is a statement
about these kernels on this census — not a production estimate.

## v3 R0 — LSB lane-striped uniskip, W = 0 (`--mode lsb-recompute`)

The first rung of the v3 LSB lane-striped design (spec dated 2026-08-08; not committed,
so every number it is measured against is restated here), built to its R0
scope: **2-group lane = tap, W = 0** (recompute every reference, no window, no cache),
full eval + finalize. No fold, no multi-round, no binding-order oracle — those are R4.
Every v1/v2 kernel is untouched; the mode is a new `.cu`
(`native/uniskip_lsb.{cu,cuh}`) and a fourth empty derived descriptor class.

What changes against v2, in one paragraph: a column's element offset becomes
`(logical_row << 4) | tap`, so the 16 taps of one logical row are 16 **adjacent**
elements — a *group*. A 16-lane half-warp owns one group with **lane = tap**, so a warp
owns two groups and a block covers 16 rows (grid `rows / 16`, 65536 blocks at
`--log-trace 24`). Lane `t` owns **two** cells: `H` cell `t` — the tap it loaded, free —
and coset cell `16 + t`, produced by a **shuffle-NTT** across the half-warp
(iDIF with `omega^-1` → folded normalize+twist → DIT with `omega`; 8 `shfl_xor` stages
and 7 generic multiplies per component pass, the two distance-1 stages being unity).
`e4` sources run the identical path limb-sequentially off one `v4.u32` load. Both
accumulators are `e4`; `eq` is applied per group at the epilogue, one `shfl_xor(16)`
merges the warp's two groups per cell-slot, and eight warps meet in a 4 KB shared plane
that writes v2's unchanged `partials[block][32]`, so `finalize` is untouched.

### Commands

```bash
cargo build --release -p gpu_gkr_uniskip_bench

# validation (both eq modes x both term orders; all four report q 32/32)
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench --log-trace 10 \
    --mode lsb-recompute --term-order {census,locality} {--validate,--validate-flat-eq}

# the locked R0 measurement
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench \
    --log-trace 24 --warmup 10 --iterations 100 \
    --mode lsb-recompute --term-order {census,locality}
```

### The R0 gate — PASS on both matched comparisons

Same device (**NVIDIA RTX PRO 6000 Blackwell Server Edition**, sm_120), same default
census, `--log-trace 24`, medians over `--warmup 10 --iterations 100`. The v2 arms were
**re-measured in the same session** rather than quoted, and they reproduce their recorded
values to 0.06 %, so the comparison is not a cross-session one.

| `--term-order` | v3 R0 `eval` | `finalize` | **eval + finalize** | v2 `fused-cached --cell-map interleave` (this session) | recorded v2 bar | verdict |
| --- | --- | --- | --- | --- | --- | --- |
| `census` | 20.652 | 0.061 | **20.713** | 23.252 + 0.033 = 23.285 | 23.272 | **PASS, −11.0 %** |
| `locality` | **20.535** | 0.061 | **20.596** | 23.056 + 0.034 = 23.090 | 23.078 | **PASS, −10.8 %** |

`fold` is excluded on both sides, as everywhere in this file — and in this mode it is
excluded because it does not exist: the LSB fold is R4 work, and the design pins it as
a separate-buffer write, since a low-bit fold reads 16 adjacent inputs and writes one —
folding in place would be a race across blocks.
The mode therefore also drops v2's ~0.92 GiB fold-output buffer; resident backings are
5.75 GiB, the same 1x as the fused modes.

`--term-order locality` is again a small, real win (−0.6 %, spans 20.32–20.62 against
20.36–20.73). It is the same sub-percent size as under v2's interleave map.

Both rows were reconfirmed on the review fix-up binary (`census` 20.655 / 0.061,
`locality` 20.536 / 0.061 — 0.02 %); that round changed host code, a comment and the
docs only, and the sm_120 kernel SASS is unchanged at 3216 instructions.

Against the external windowed reference point on the corrected **unit** basis (see the
withdrawn per-bit form in *Per-variable* above; all its other caveats still apply):
20.596 / 1.875 = **10.99 ms/unit**, **1.37x** the 8.00 ms/unit reference, down from v2's
12.31 / 1.54x. Windowed parity for this pass is **15.0 ms** of `eval + finalize`. The
earlier per-bit figure for this arm (5.15 ms/variable, 1.10x) is **withdrawn** — it
overcredited the pass for the cheap tail bits.

### Hard gates

- **Bit-exact `q`.** 32/32 for all **eight** cells of {`census`, `locality`} x
  {`--validate`, `--validate-flat-eq`} x {`--self-products 0`, `--self-products 12`} at
  `--log-trace 10`. The oracle addresses the taps through the LSB host mirror
  (`abi::lsb_source_offset` via `Layout::source_offset`, cell -> tap through
  `abi::tap_for_cell`) and re-extends them with the dense `domain::lde_matrix()`, so the
  device's factorized producer is checked against the matrix on real data, not against
  itself. `LDE validate` and `fold validate` report `n/a` (no coset buffer, no fold
  stage). The `--self-products` cells are what exercise the W = 0 duplicate rule — the
  default census emits no self-product, so a bare run never reaches that branch. The knob
  rewrites `program` only — the census and the cache plan are measured once at generation
  and go **stale** under it rather than tracking it, which is why a run with it on labels
  both `STALE`; see the README's mode contract for that and for why the knob also makes
  the v2/v3 A/B non-work-matched.
- **ptxas stack/spill 0 on all four architectures**, and **zero `LDL`/`STL` in SASS on
  all four**.

| kernel | sm_120 | sm_80 | sm_89 | sm_90 | stack / spill st / spill ld |
| --- | --- | --- | --- | --- | --- |
| `ab_gkr_uniskip_eval_lsb_w0_kernel` | **40** | 96 | 96 | 56 | 0 / 0 / 0 (4096 B smem) |

  In the same diagnostic build every v1/v2 kernel is at its recorded count
  (`eval` 54, `eval_fused` 64, `eval_fused_interleave` 125, both cached kernels 66 on
  sm_120), which is the evidence that this rung left them alone.

  The register table is the diagnostic build at the top of this file (which carries the
  `--keep` / sccache hazard documented there — the recovery is
  `touch native/*.cu*` + `SCCACHE_RECACHE=1 cargo build`; note that pointing
  `CMAKE_TOOLCHAIN_FILE` at an empty file does **not** displace the launcher for this
  crate, because `CMAKE_CUDA_COMPILER_LAUNCHER` is already in its CMake cache). The SASS
  check needs no diagnostic flags at all and therefore poisons nothing:

```bash
# CUDAARCHS is not in the cargo fingerprint AND is cached by CMake, so clear both.
rm -rf target/release/build/gpu_gkr_uniskip_bench-*/out/build
touch gpu/gkr_uniskip_bench/native/*.cu gpu/gkr_uniskip_bench/native/*.cuh
CUDAARCHS="80;89;90;120" cargo build --release -p gpu_gkr_uniskip_bench
cuobjdump -sass .../gpu_gkr_uniskip_bench_native.dir/uniskip_lsb.cu.o   # all four in one object
# then clear + rebuild with CUDAARCHS unset so the shipped binary is native-only,
# and re-run the validation set on it.
```

  The kernel body on every architecture:

| arch | instructions | `LDL` | `STL` | `SHFL` | `LDG` | `LDS` / `STS` |
| --- | --- | --- | --- | --- | --- | --- |
| sm_80 | 4096 | **0** | **0** | 184 | 11 | 8 / 2 |
| sm_89 | 4096 | **0** | **0** | 184 | 11 | 8 / 2 |
| sm_90 | 3240 | **0** | **0** | 184 | 11 | 8 / 2 |
| sm_120 | 3216 | **0** | **0** | 184 | 11 | 8 / 2 |

  For scale, v2's cached interleave kernel is 13 568 instructions on sm_120 — the LSB
  body is 4.2x smaller because the 16-tap dot is gone and the term loop is not unrolled
  over four cells. `SHFL`/`LDG`/`LDS`/`STS` are identical across architectures; only the
  scalar integer scheduling differs.

- **Occupancy.** 40 registers puts the register block limit at **6 blocks/SM** against
  v2's 3, and 4096 + 1024 B of shared memory at 12 — so registers still bind, but now at
  the warp ceiling: `ncu` reports **theoretical occupancy 100 %, achieved 99.28 %**
  (v2's winner: 50 % / 49.89 %).

### Profile of the winning order

```bash
mkdir -p target/profiling/ncu
.agents/bin/with_gpu_lock.sh ncu --set full \
    --metrics dram__bytes.sum,l1tex__t_sectors_pipe_lsu_mem_global_op_ld.sum,smsp__inst_executed.sum \
    --kernel-name-base demangled --kernel-name 'regex:ab_gkr_uniskip_eval_lsb_w0_kernel' \
    --launch-count 1 --target-processes all -o target/profiling/ncu/v3r0_lsb_locality_full \
    target/release/gpu_gkr_uniskip_bench --log-trace 24 --warmup 1 --iterations 1 \
    --mode lsb-recompute --term-order locality
```

| metric | v2 `fused-cached` interleave/locality | **v3 R0 `lsb-recompute` locality** |
| --- | --- | --- |
| duration under the profiler | 23.79 ms | **21.14 ms** |
| `dram__bytes.sum` | 6.24 GB | **6.21 GB** |
| against the mode's compulsory floor | 1.008x (6.19 GB) | **1.000x (6.208 GB)** |
| Compute (SM) throughput | 74.92 % | **81.43 %** |
| `sm__pipe_fmaheavy_cycles_active` | 75.26 % | **81.51 %** |
| DRAM / L2 / L1TEX throughput | 16.43 / 14.62 / 27.53 % | 18.42 / 8.07 / 32.20 % |
| L1 / L2 hit rate | 88.69 % / 78.47 % | 35.81 % / 55.89 % |
| registers, blocks/SM | 66, 3 | **40, 6** |
| theoretical / achieved occupancy | 50 % / 49.89 % | **100 % / 99.28 %** |
| executed instructions | — | 24 388 763 648 |

**DRAM floor arithmetic for this mode.** The eval kernel must touch the tap backing once
and write the block partials: `48 bf columns x 16 planes x 2^20 rows x 4 B`
= 3 221 225 472 B, plus `11 e4 columns x 16 x 2^20 x 16 B` = 2 952 790 016 B, giving the
5.75 GiB backing = 6 174 015 488 B; partials are `32 cells x 65 536 blocks x 16 B`
= 33 554 432 B. Floor = **6 207 569 920 B = 6.208 GB**, measured 6.21 GB, **1.000x**. (The
binary's printed whole-pass compulsory traffic, 6 241 124 864 B, additionally counts
`finalize` re-reading the partials and writing `q`.)

**Issued source-load sectors: 1.000x the compulsory MINIMUM FOR THE ISSUED REQUESTS —
a coalescing ratio, not a traffic ratio.** `ncu` reports
117 964 800 global load *requests* and 684 195 840 *sectors*. Both are exact:
524 288 warps x 225 requests (190 `bf` references + 34 `e4` references + 1 `eq_low`) and
524 288 x 1305 sectors (`190 x 4 + 34 x 16 + 1`). A warp's two `bf` groups are 128 B
contiguous = 4 sectors and its two `e4` groups 512 B = 16 sectors, which are the *minima*
for those byte counts — so the LSB layout costs **zero** coalescing overhead and the R0
requirement (≤ 1.05x) passes at 1.000x. **This is not an issued-vs-distinct-bytes
measure.** Against a distinct-bytes-once floor the W = 0 recompute re-reads the backing
**3.54x** (`190/48` on `bf`, `34/11` on `e4`) — the mode's structural re-read, since
nothing is retained across references. L1 and L2 absorb all of it, which is why DRAM
lands on the floor at 1.000x; that DRAM figure *is* a distinct-bytes measure and the two
must not be quoted as if they were the same claim.

**Pipes and stalls.**

| pipe | % of peak sustained active | | stall reason (`selected` excluded) | share |
| --- | --- | --- | --- | --- |
| `sm__pipe_fmaheavy_cycles_active` | **81.51** ← equals the 81.43 % SM SOL | | `math_pipe_throttle` | **28.4 %** |
| `sm__inst_executed_pipe_adu` | 57.95 | | `not_selected` | 27.1 % |
| `sm__inst_executed_pipe_alu` | 35.00 | | `wait` | 15.3 % |
| `sm__inst_executed_pipe_lsu` | 32.20 | | `short_scoreboard` | 9.9 % |
| `sm__inst_executed_pipe_fma` | 17.32 | | `long_scoreboard` | 9.1 % |
| `sm__inst_executed_pipe_xu` / `cbu` | 0 / 0.006 | | `dispatch_stall` | 7.5 % |
| | | | `no_instruction` / `barrier` / `mio_throttle` | 1.1 / 0.9 / **0.6 %** |

What this settles:

- **The rung is still mul-pipe bound, and now harder.** `fmaheavy` 81.51 % *is* the
  81.43 % SM SOL, up from v2's 75.26 %, and `math_pipe_throttle` is the single largest
  stall at 28.4 %. **It did not get there by doing fewer multiplies** — the cost model
  below shows the producer's multiply work is a wash per output cell (28 mul-pipe ops
  either way) and that this arm carries 1.065x the modelled resolver work of v2's cached
  winner. The 11 % is instruction-stream economy: one coalesced group load per reference
  serves all 16 coset cells *and* the `H` cell, so 17x fewer load instructions and their
  address chains issue per (record, row); registers fall 66 -> 40, doubling blocks/SM to
  the warp ceiling; and the static body shrinks 4.2x. What rose to 81.5 % is the *share*
  of the stream that is multiplies, because everything around them was removed.
- **Shuffles are ~5.6 % of the instruction stream, not the 1–2 % the design predicted.**
  The op-level shuffle counter is `n/a` on this chip, so the dynamic count is derived
  from the program structure and cross-checked against static SASS: 8 exchange stages per
  component pass gives `190 x 8 + 34 x 32 + 8 = 2616` `SHFL` per warp-program-pass,
  against `24 388 763 648 / 524 288 = 46 516` executed instructions per warp — **5.62 %**,
  in line with the 5.72 % static share. The 1–2 % prediction was computed for the
  perfect-window case (92 component passes); at W = 0 there are 326.

  **Blocked radix-4: PARKED — first disjunct MET, micro-A/B OWED.** The escalation gate
  is "SHFL/MIO ≥ 5 % wall-equivalent **or** material MIO stalls, **plus** a micro-A/B
  predicting ≥ 3 % pass win". The first disjunct is **met** at 5.62 % (`mio_throttle` is
  only 0.6 % of stalls, so the *other* disjunct is not); the micro-A/B has **not** been
  run, so the gate does not advance — and it must not be recorded as declined on the
  shuffle evidence alone, because the shuffle count is only half of what radix-4 changes.

  The other half is on the pipe that is actually saturated. Under the blocked
  4-strided-taps/lane map (4 lanes per group, 8 groups per warp) `lane = t & 3` and
  `slot k = t >> 2`, so the **d = 4 and d = 8 stages become intra-lane** — and the slot
  index is a compile-time constant under `#pragma unroll`, so a unity twiddle there is
  eliminated outright instead of issuing.

  **Only the SLOT-determined unity entries are removable**, which is fewer than the raw
  unity count. A multiply at slot `k` is removable only if its twiddle is unity for all
  four lanes of that slot:

| stage (table) | unity entries | slot-determined (removable) | lane-determined (not) |
| --- | --- | --- | --- |
| iDIF d = 8 (0) | 9 | **8** — `k ∈ {0,1}`, i.e. bit 3 of `t` clear | 1 — `t = 8`, exponent 0 on lane 0 |
| iDIF d = 4 (1) | 10 | **8** — `k ∈ {0,2}`, i.e. bit 2 of `t` clear | 2 — `t = 4, 12` |
| DIT d = 4 (5) | 10 | **8** — same mask | 2 — `t = 4, 12` |
| DIT d = 8 (6) | 9 | **8** — same mask as iDIF d = 8 | 1 — `t = 8` |
| | 38 | **32** | 6 |

  So the cut is **32 of the 112 issued per group = 28.6 %**, not 38 / 34 %. The 6
  leftovers are exponent-zero twiddles that land on lane 0 of a *non*-unity slot — the
  same lane-divergent class the cost model above proves unskippable, and the blocked map
  does not touch it.

  Where that would land the resolver model, **as the A/B's hypothesis and nothing more**:
  a blocked arm issuing 112 − 32 = **80** full `bf::mul` per group, with the address
  `IMAD.WIDE` term unchanged, models at `326 x (80 x 4) + 224 x 16` = **107 904** ops/row against this
  arm's 149 632 (−27.9 %) and v2's winner 140 480 (−23.2 %). That is a resolver-model
  number, not a wall projection — it prices none of the costs below.

  What the owed micro-A/B has to price against that 28.6 %: the two cross-lane transposes
  that replace the 8 exchange stages; the **4x register map** (8 regs/lane per BF-eq
  resident against the default's 2, on a kernel currently at 40 registers and exactly at
  the 6-blocks/SM warp ceiling); and the `e4` axis complication (a transpose in and out,
  or limb-major loads). None of those is priced here.

  **SUPERSEDED BY R1, and the verdict hardens to parked.** The v3 R1 rung took the
  *superset* of this prize — all 62 unity multiplies, not radix-4's 32 — by dissolving the
  lane = tap binding in shared memory. It delivered the arithmetic exactly
  (`fmaheavy` 81.5 % -> 68.7 %) and **still lost 14–15 %** of wall time to the enabling
  mechanism. Radix-4's distinguishing property is therefore no longer the 28.6 % — it is
  that it pays no staging cost — but it captures roughly half the arithmetic that R1
  proved insufficient, for its own unpriced costs. The micro-A/B is still owed and the
  gate still does not advance; it is now a smaller prize against measured evidence that
  this class of trade does not clear on this part.
- **Constant-load serialization was designed out, and the profile does not contradict
  it.** The twiddle tables are lane-indexed, so a hot-path `__constant__` read would be a
  16-way divergent access on every stage of every reference; the kernel instead hoists all
  seven into per-lane registers once at entry (7 of its 40 registers). The remaining
  constant traffic is 57 `LDC`/`LDCU` in a 3216-instruction body, and `no_instruction` is
  1.1 % of stalls with `sm__icc_requests` at 63.8 % of peak — below v2's 76.6 %.
- **`not_selected` at 27.1 % is the new shape of the profile**, and it is the direct
  consequence of running 48 warps per SM instead of 24 on a saturated pipe. It is not a
  defect: it is what 100 % occupancy on a throughput-bound kernel looks like.

### The producer cost model: executed, not algebraic

The v3 ladder priced this rung at **326 x 50 = 16 300** field multiplies per row, which
it called 5.1x v2's per-read 83 456 (`326 references x 16 FMA x 16 cells`). **The kernel
issues 326 x 112 = 36 512** — a 2.24x gap, and 2.29x rather than 5.1x against v2. It is a
property of the lane map, not a defect:

`uniskip_lsb_coset` runs **7 unconditional `bf::mul` per lane** = **112 full multiplies
per 16-output group**. The twiddle census proves only **50** of those are non-unity
(17 iDIF + 16 twist + 17 DIT); the other **62 are unity multiplies that still issue**,
because under lane = tap the unity entries are *lane-divergent* — lane 0 and lane 15 of
one stage want different twiddles and the same warp instruction has to serve both, so a
unity slot cannot be skipped. Only the two distance-1 stages, whose twiddle is unity on
**every** lane, are compile-time removable, and they already are (7 tables, not 9).

Like-for-like against v2, **per output cell**, in this file's mul-pipe-op unit
(`mad_wide` 1, `red_wide`/`red` 3, so `bf::mul` = 4):

| | producer multiplies per coset cell | + address `IMAD.WIDE` | total |
| --- | --- | --- | --- |
| v2 chunked dot (16 `mad_wide` + 4 `red_wide`, per cell) | 16 + 12 = **28** | 16 (one per tap load) | **44** |
| v3 shuffle-NTT (7 `bf::mul` per lane, lane = one cell) | 7 x 4 = **28** | 1 (one load per lane) | **29** |

**The producer's multiply work is a wash — 28 against 28.** The 1.52x that appears when
addressing is included is the address chain, not the transform. Per row over the
width-weighted reference count 326, and against this file's own resolver model:

| arm | modelled mul-pipe ops / row | vs v2 uncached | vs v2 winner |
| --- | --- | --- | --- |
| v2 rung 2a, no cache | 229 504 | 1.000x | 1.634x |
| v2 winner, 16 cache units | 140 480 | 0.612x | 1.000x |
| **v3 R0, W = 0** | 326 x 448 + 224 x 16 = **149 632** | 0.652x | **1.065x** |

So v3 R0 does **more** modelled resolver work than v2's cached winner and is still
10.8 % faster. **The measured win is therefore not producer multiply count.** What it is,
in decreasing order of confidence:

- **17x fewer load instructions per (record, row).** v2's block issues 8 warps x
  (2 `H` + 32 coset-dot taps) = 272 load instructions per record per 32 rows = 8.5 per
  (record, row); v3's issues 8 warps x 1 = 8 per record per 16 rows = **0.5**. One
  coalesced group load per reference serves all 16 coset cells *and* the `H` cell, so
  the second load and its address chain disappear together. This is what the ladder's
  op model never counted.
- **Registers 66 -> 40**, so blocks/SM 3 -> 6 and occupancy 50 % -> 100 %, on a kernel
  that is throughput-bound rather than latency-bound.
- **Static code 13 568 -> 3216 instructions**, with `sm__icc_requests` 76.6 % -> 63.8 %.

### What R0 does and does not establish

Established: the LSB lane-striped architecture with **no scheduler at all** beats v2's
best scheduled arm under both term orders, at 1.000x the DRAM floor (a distinct-bytes
measure), perfectly coalesced loads (1.000x the sector minimum for the requests it
issues — the W = 0 stream itself re-reads the backing 3.54x, absorbed by L1/L2), zero
spills and 100 % occupancy. The R0 stop condition ("if W = 0 cannot beat v2 … stop
before any scheduler work") is **not** triggered — scheduler work is authorized on the
evidence.

Not established, and deliberately out of scope at this rung: the fold, multi-round
telescoping, the low-bit binding-order differential oracle, the window/residence
realizations (A vs B), the lane-map A/B, and the real-circuit census.

**Why the projection missed.** The design's landing zone for W = 0 was 18.6 ms against a
16–19 ms first zone; 20.6 ms is outside it on the high side while still clearing the
gate. The **dominant** term is the executed-vs-algebraic gap of the previous subsection —
the projection priced 50 multiplies per 16 outputs (3.1 per element) and the lane = tap
map issues 112 (7 per element), so `326 x 50 = 16 300` becomes `326 x 112 = 36 512` lane
multiplies per row, 2.24x the priced figure. Against v2's 83 456 that is a **2.29x**
reduction **in the ladder's own unit — a count of field multiplies**, not the ladder
table's 5.1x. That unit is not mul-pipe time: v2's per-tap `mad_wide` is one pipe op and
this chain's `bf::mul` is four, so in the op-unit of the table above both arms sit at
146 048 ops/row and the arithmetic is a wash. The 2.29x is the honest correction to the
5.1x claim, not a claim of 2.29x less work. The fitted intercept being an artifact
of the v2 kernel is a real second-order effect, and the design flagged it, but it is not
what carries the miss.

Standing levers, from this profile, in the order the evidence supports them:

1. **Mul-pipe work is the whole wall** (`fmaheavy` = SM SOL = 81.5 %), and it has two
   independent reductions left. (a) **The unity multiplies — MEASURED at R1, and the
   lever is closed on the mul-pipe side.** 7 per lane is the minimum for **radix-2 under
   lane = tap**, not for the transform: 62 of the 112 issued multiplies per group are
   unity and survive only because lane = tap makes them lane-divergent. The v3 R1 rung
   removed **all 62** by staging in shared memory and packing the real 50 across lanes
   (`--mode lsb-compact`), delivering the predicted arithmetic — `fmaheavy` 81.5 % ->
   68.7 %, chain multiplies per row −43 % at G = 4 and −50 % at G = 8 — and **lost 14–15 % of
   wall time**, because the staging moved the work onto the narrower LSU pipe. See the
   v3 R1 section. Blocked radix-4 recovers 32 of the 62 (28.6 %) without staging, and
   stays parked against that measurement. (b) **The window** (R2/R3), which
   removes whole productions rather than multiplies inside one.
2. **`sm__inst_executed_pipe_adu` at 58 %** says address arithmetic is the second-busiest
   pipe. v2's F9 finding (ptxas does not strength-reduce the per-tap address chain)
   applies here with only one load per reference instead of 16, so the absolute cost is
   far lower — but it is now a larger *share*.
3. **The block covers 16 rows, not 32**, so the per-record VM decode is amortized over
   half as many rows as v2's. Two groups per lane (a 32-row tile at 4 `e4` accumulators)
   is the obvious cheap experiment and belongs to R1's lane/layout A/B.

## v3 R1 — SMEM-staged compacted producer (`--mode lsb-compact`): MISS, and why

RR's observation that opened this rung: R0's "unity multiplies are unskippable" is an
artifact of the **lane = tap shuffle binding**, not of the problem. Bind lane to tap and a
stage's twiddle is a per-lane constant, so one warp instruction has to serve unity and
non-unity lanes at once and 62 of a group's 112 issued multiplies do nothing. Stage the
group vectors in shared memory and the binding dissolves: an element is an address, any
lane can own any element, and a **static schedule packs only the 50 real multiplies** into
`ceil(G * m_s / 32)` rounds per stage — no branches, no predication, no divergence.

**The mechanism works exactly as designed and the pass is slower anyway.** The
multiply cut is real, proven in SASS and visible in the profile (`fmaheavy` 81.5 % ->
68.8 %); it buys nothing because the staging that enables it moves the work onto a
**narrower pipe**. That is the finding.

### What was built

`--mode lsb-compact --compact-groups {4,8}`. Same LSB backing, same W = 0
recompute-everything semantics, same `eq`/`finalize` path, no fold — R0 with a
restructured producer and warp geometry. New native and schedule files
(`native/uniskip_lsb_compact.{cu,cuh}`, `src/compact.rs`) plus wiring in
`CMakeLists.txt`, `abi.rs`, `harness.rs`, `kernels.rs`, `lib.rs` and `main.rs`;
`uniskip.cu`, `uniskip_abi.cuh` and `uniskip_lsb.{cu,cuh}` are byte-untouched.

- **Geometry.** A warp owns `G` groups; lane `l` holds `G / 2` elements, all at tap
  `l & 15` — element `k` is group `(l >> 4) + 2k`. The lane keeps its R0 cell identity
  (cell `t` on H, `16 + t` on the coset, per row) and one program walk serves `G` rows, so
  decode amortizes `G / 2`x better than R0. A block is 8 warps x `G` rows.
- **Producer.** Per reference the warp loads its `G` groups coalesced, keeps H in
  registers (so the transform may run in place and destroy the buffer), stages H, runs the
  chain as fused butterfly+multiply rounds, and reads the coset back. `e4` runs the
  identical chain limb-sequentially through the one buffer.
- **Schedule.** Host-built (`src/compact.rs`), uploaded to `__constant__`, copied to
  shared memory once per block — nothing reads it lane-indexed from `__constant__` in the
  hot path. Multiplying slots occupy a dense prefix of each phase, and `mul_rounds` is
  compile-time, so a round past it emits **no multiply code at all** rather than a
  predicated one.
- **Accumulation.** One `(H, coset)` `e4` pair per row through the walk (rows cannot mix
  before `eq`), then eq-weight, collapse the lane's rows, and R0's `xor 16` merge and
  partials path unchanged.

### Gates — all pass

- **Cross-mode oracle (new, and stronger than R0's self-oracle).** `lsb-compact`
  preserves `lsb-recompute`'s element ordering, init generator and `eq` composition, so
  its `q` must be bit-exact equal. Dumped device-side and compared without going through
  the host oracle at all:

```bash
for order in census locality; do
  B=target/release/gpu_gkr_uniskip_bench
  $B --log-trace 12 --iterations 0 --dump-q --mode lsb-recompute  --term-order $order | grep '^q\[' > /tmp/q_r0_$order.txt
  for g in 4 8; do
    $B --log-trace 12 --iterations 0 --dump-q --mode lsb-compact --compact-groups $g --term-order $order | grep '^q\[' > /tmp/q_c${g}_$order.txt
    diff -q /tmp/q_r0_$order.txt /tmp/q_c${g}_$order.txt      # -> identical
  done
done
```

  All six dumps (R0, G = 4, G = 8, each under both term orders) are 32 cells and hash to
  the same value, `sha256[0:16] = ed3bead0bce8833d`; `diff` reports **IDENTICAL** for all
  four comparisons. (The two term orders agree with each other as well, which is the
  order-invariance R0's record already established.)
- **Standard cells.** 16/16 pass `q validate: OK (32/32)` — {G = 4, G = 8} x
  {`census`, `locality`} x {`--validate`, `--validate-flat-eq`} x
  {`--self-products 0`, `--self-products 12`}. One representative cell per G, in full:

```
$ … --log-trace 10 --validate --mode lsb-compact --compact-groups 4 --term-order locality
LDE validate: n/a (no coset backing)
q validate: OK (32/32)
fold validate: n/a (no fold stage in this mode)
$ … --log-trace 10 --validate --mode lsb-compact --compact-groups 8 --term-order locality
LDE validate: n/a (no coset backing)
q validate: OK (32/32)
fold validate: n/a (no fold stage in this mode)
```
- **Schedule proof (CPU, GPU-free).** `cpu_compact_schedule_covers_every_element_once`
  checks against `domain::ntt_twiddles`, not a device twin: every `(phase, group, slot)`
  exactly once, the twiddle equal to the census entry, **no unity element scheduled**, and
  the multiplying entries a dense prefix. `cpu_compact_mul_census` pins
  `[2,2,1,0,4,0,1,2,2]` mul rounds at G = 8 (14 total, 56 lane-multiplies per group) and
  8 / 64 at G = 4, against R0's 112.
- **ptxas 0 stack / 0 spill and zero `LDL`/`STL` in SASS on sm_80/89/90/120**, both G.

| kernel | sm_80 | sm_89 | sm_90 | sm_120 | blocks/SM (sm_120) | stack / spill |
| --- | --- | --- | --- | --- | --- | --- |
| `…_lsb_w0_kernel` (R0) | 96 | 96 | 56 | **40** | **6** | 0 / 0 / 0 |
| `…_lsb_compact_g4_kernel` | 127 | 127 | 73 | **67** | 3 | 0 / 0 / 0 |
| `…_lsb_compact_g8_kernel` | 231 | 232 | 138 | **128** | 2 | 0 / 0 / 0 |

  The register growth is the `G / 2` elements per lane multiplying every operand and
  accumulator array: G = 8 needs 4 `(H, coset)` `e4` accumulator pairs (32 registers) plus
  two `e4` operands x 4 elements x 4 limbs. It never spills, but it costs half (G = 4) to
  two thirds (G = 8) of R0's occupancy.

### SASS mechanism proof — the compaction is real

The chain is inlined at 22 sites per kernel (6 `bf` operand sites + 4 `e4` sites x 4 limb
passes), so its multiply count is separable from the rest of the `IMAD.WIDE` total:

| kernel | total `IMAD.WIDE` (sm_120) | of which chain | rows served per walk | **chain multiplies / row** | lane-muls / group |
| --- | --- | --- | --- | --- | --- |
| R0 `lsb-recompute` | 423 | 22 x 7 = 154 | 2 | **77.0** | 112 |
| compact G = 4 | 704 | 22 x 8 = 176 | 4 | **44.0** (−43 %) | 64 |
| compact G = 8 | 1354 | 22 x 14 = 308 | 8 | **38.5** (−50 %) | 56 |

The non-chain remainder scales ≈ with the element count — 269 / 528 / 1046 for
1 / 2 / 4 elements per lane, i.e. 1.96x and 3.89x rather than exactly 2x and 4x — which is what makes the split above a measurement rather
than an attribution. The designed ratios (112 -> 64 -> 56 lane-multiplies per group) and
the measured per-row ratios (77 -> 44 -> 38.5) agree to three digits.

The staging cost is equally visible: static `LDS`/`STS` go from R0's **8 / 2** to
**712 / 443** (G = 4) and **1416 / 883** (G = 8).

### Timings — MISS on every arm

Locked, `--log-trace 24`, `--warmup 10 --iterations 100`, medians. R0 re-measured in the
same session as the control.

All six rows below are from **one session on one build**, `--bank-perm linear` (the
default) throughout:

```bash
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench \
    --log-trace 24 --warmup 10 --iterations 100 \
    --mode lsb-compact --compact-groups {4,8} --term-order {census,locality}
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench \
    --log-trace 24 --warmup 10 --iterations 100 --mode lsb-recompute --term-order {census,locality}
```

| arm | `--bank-perm` | `eval` | `finalize` | **eval + finalize** | vs recorded bar | vs same-session control | spread (`eval` min–max) |
| --- | --- | --- | --- | --- | --- | --- | --- |
| R0 `lsb-recompute` census (bar 20.713) | n/a | 20.835 | 0.061 | **20.896** (control) | +0.88 % | — | 20.350–20.898 |
| R0 `lsb-recompute` locality (bar 20.596) | n/a | 20.714 | 0.061 | **20.775** (control) | +0.87 % | — | 20.326–20.781 |
| compact G = 4 census | linear | 23.816 | 0.033 | **23.849** | +15.1 % | **+14.1 %** | 23.460–23.862 |
| compact G = 4 locality | linear | **23.682** | 0.033 | **23.715** | +15.1 % | **+14.2 %** | 23.134–23.740 |
| compact G = 8 census | linear | 42.189 | 0.018 | 42.207 | +104 % | +102 % | 42.180–42.198 |
| compact G = 8 locality | linear | 41.242 | 0.018 | 41.260 | +100 % | +98.6 % | 41.206–41.287 |

**Correction to the first two versions of this table.** The R1 commit's rows and the
review-round-1 rows were not all from the session their header claimed. In round 1 the
`--bank-perm` A/B's *G = 4 locality* numbers were pasted into **both** G = 4 rows, making
census and locality byte-identical in median, sum and both spread endpoints — which is not
a measurement, it is a copy/paste error — and the G = 8 census row was left at its
pre-fix value under a header claiming re-measurement. **The table above replaces both**;
it was produced by re-running all six cells rather than by editing numbers.

Census does **not** equal locality at G = 4. Two independent runs, same build:

| run | G = 4 census | G = 4 locality | locality win |
| --- | --- | --- | --- |
| 1 (the table above) | 23.816 | 23.682 | **−0.56 %** |
| 2 (independent) | 24.076 | 23.930 | **−0.61 %** |

— the same sign and size as `locality`'s effect in every other mode. Those two runs also
show the run-to-run drift directly: **+1.1 % on the same arm, same binary**, which is the
scale the control-drift note below is about.

**Which denominator, and the drift.** The percentages above are given against **both** the
recorded R0 bars (20.713 / 20.596) and the R0 control re-measured in this session
(20.896 / 20.775). The control runs **+0.88 %** above its own recorded figure — roughly
**50x** the ~0.02 % reproducibility the R0 record demonstrated across rebuilds, so it is
worth accounting for rather than passing over. It is **not codegen**: this rung adds a
translation unit and a ~5 KB `__constant__` to the same device link
(`CUDA_SEPARABLE_COMPILATION`), which could plausibly perturb existing kernels, so the
`lsb-recompute` kernel's sm_120 SASS was recounted in this build — **3216 instructions,
identical to the R1 commit's and to the R0 record's**. The drift is therefore session /
measurement, not code. The miss stands on either denominator: **+13.8 % to +15.6 %**.

**Modes unperturbed, this build.** R0's record set the precedent of showing the v1/v2
kernels at their recorded register counts in the same diagnostic build. Repeated here:

| kernel | sm_120 regs, R1 build | recorded |
| --- | --- | --- |
| `ab_gkr_uniskip_eval_kernel` | 54 | 54 |
| `ab_gkr_uniskip_eval_fused_kernel` | 64 | 64 |
| `ab_gkr_uniskip_eval_fused_interleave_kernel` | 125 | 125 |
| `ab_gkr_uniskip_eval_fused_cached{,_interleave}_kernel` | 66 / 66 | 66 / 66 |
| `ab_gkr_uniskip_eval_lsb_w0_kernel` | 40 (3216 SASS instructions) | 40 (3216) |

G = 4 is the better arm and is the mode default. **Both miss R0 on either denominator, and R1's own
resolver-model hypothesis (76 608 ops/row at G = 8, −48.8 %; 87 040 at G = 4, −41.8 %)
is falsified as a predictor of wall time** — the model counts multiplies and the wall is
not paying for multiplies any more.

The G = 8 row carries a caveat, but **not the one the first version of this record gave**.
That version blamed the bank permutation for G = 8's regression from the first build's
28.618 — an inference across two builds that differed in two ways at once, exactly the
error the `--bank-perm` A/B was built to retire. The A/B says the opposite: at G = 8
`identity` is **42.642** and `linear` **41.274**, so the permutation is a **3.2 % win**
there, not the cause. (And the store/readback is 4-way conflicted under *either*
permutation — `perm[t] * 8 + g` takes 8 distinct values mod 32 whatever `perm` is — so it
was never the discriminator.) What actually separates 28.6 from 41.2 is the **layout**:
the deleted first build stored group-major with an odd stride (`g * 17 + t`), the shipped
one stores group-minor (`perm[t] * G + g`), and at G = 8 the latter is worse for the
lane = tap store/readback path while being better for the round path. No G = 8 layout
comes within 35 % of the bar, so the conclusion does not turn on which is fairest, and no
third layout was built.

### The optimization attempt, and what it settled

The first profile — of the now-deleted stride-17 group-major build — showed **3.94 billion
shared bank conflicts**, 8.89 G actual against 4.96 G ideal wavefronts, **79 % excess**.
(The shipped layout's own `identity` arm is less bad at **60 %** excess, 7.95 G against the
same 4.97 G ideal; 79 % is the deleted build's figure and belongs to it.) The cause is a
stride argument that was necessary but not sufficient: the slots of a distance-`d` phase are the taps with bit `log2 d` clear,
and the identity map collides pairwise mod 8 on `{0,1,2,3,8,9,10,11}`. The fix
(optimization attempt 1 of the 2 allowed) permutes the tap by the GF(2)-linear map with
column images `[1, 2, 5, 14]` — **a** permutation found by enumeration, not a unique or
canonical one. Of the 20 160 invertible GF(2) 4x4 maps, **1 344** keep the low 3 bits
bijective on all four tap hyperplanes and **768** are additionally conflict-free under
`ordered_slots`' greedy at both group counts; `[1, 2, 6, 13]` works equally well and
`[1, 2, 4, 15]` has the hyperplane property yet still conflicts at G = 8. **The
hyperplane condition is necessary but not the operative acceptance test** — the operative
one is measured: `cpu_compact_schedule_is_bank_conflict_free` histograms the real
schedule's banks and asserts degree 1, rather than arguing from a stride or a structural
property.

The permutation is a **runnable arm**, not a one-off edit: `--bank-perm {identity,linear}`
keeps the pre-permutation layout reachable so the A/B is single-variable and re-runnable.

```bash
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench \
    --log-trace 24 --warmup 10 --iterations 100 \
    --mode lsb-compact --compact-groups 4 --term-order locality --bank-perm {identity,linear}
```

| G = 4, locality, one build, one session | `--bank-perm identity` | `--bank-perm linear` |
| --- | --- | --- |
| shared bank conflicts | 2 978 900 658 | **927 561 850** (−69 %) |
| shared wavefronts | 7 946 201 402 | **5 894 862 594** (−26 %) |
| `sm__inst_executed_pipe_lsu` | 86.64 % | **86.85 %** (+0.21) |
| SM speed-of-light | 86.38 % | 86.59 % |
| `fmaheavy` | 68.60 % | 68.74 % |
| `eval` median | **23.747** | **23.766** (+0.08 %) |

**That is the decisive measurement of this rung.** Removing 69 % of the bank conflicts and
26 % of the shared wavefronts moved the LSU pipe **up** 0.21 points and the wall by
+0.08 % — inside the noise, and certainly not a win. The bound is
`sm__inst_executed_pipe_lsu`, the **count of LSU instructions**, not the wavefronts they
expand into; no amount of bank tuning can reach it. The second optimization attempt was
therefore not spent: the structural minimum of this design is ~2 shared accesses per
element per stage, and the measured gap to R0 is 14–15 %.

**A correction to the first version of this record.** It reported this A/B as
23.755 -> 23.574 (−0.8 %), which compared two *different builds* whose layouts differed in
two ways at once (group-major with an odd stride, then group-minor with a permuted tap).
The single-variable numbers above supersede it: the honest figure is **+0.08 %, not
−0.8 %**, which strengthens the conclusion rather than weakening it. The three layouts
measured, for the record: stride-17 group-major (first build, now deleted) G = 4 23.755 /
G = 8 28.618; `identity` G = 4 23.747 / G = 8 42.642; `linear` (shipped) G = 4 23.766 /
G = 8 41.274. **At G = 8 the permutation is worth 3.2 %**, because its store/readback path
is the one that suffers most without it — but no G = 8 layout comes within 35 % of the bar.

### ncu — G = 4 locality against R0

`ncu --set full`, same recipe and location as R0's
(`target/profiling/ncu/v3r1_compact_g4_locality_full.ncu-rep`). **Re-profiled on the
current build** (`--bank-perm linear`, the shipped default) so every figure here comes
from one report; the R1 commit's version of this table mixed the pre-permutation build's
rows with the A/B's and is replaced.

| metric | R0 `lsb-recompute` | **R1 compact G = 4, linear** |
| --- | --- | --- |
| duration under the profiler | 21.14 ms | 23.84 ms |
| **bounding pipe** | `fmaheavy` **81.51 %** = SM SOL 81.43 % | **`lsu` 86.85 %** = SM SOL 86.58 % |
| `sm__pipe_fmaheavy_cycles_active` | 81.51 % | **68.74 %** ← the multiply cut, delivered |
| `sm__inst_executed_pipe_lsu` | 32.20 % | **86.85 %** ← where it went |
| `sm__inst_executed_pipe_alu` / `adu` | 35.00 / 57.95 % | 28.19 / **9.06 %** |
| executed instructions | 24 388 763 648 | 25 475 055 616 (+4.5 %) |
| shared instructions (`smsp__sass_inst_executed_op_shared`) | ~0 | **4 444 979 200** |
| shared wavefronts / bank conflicts | ~0 | 5 894 834 628 / 927 533 884 |
| `dram__bytes.sum` vs floor | 6.21 GB, 1.000× | 6.22 GB, **1.000×** |
| global load sectors | 684 195 840 | **684 195 840** (identical) |
| registers, blocks/SM | 40, **6** | 67, **3** |
| achieved occupancy | 99.28 % | **49.74 %** |
| stalls: `short_scoreboard` | 9.9 % | **33.9 %** |
| stalls: `math_pipe_throttle` | 28.4 % | 8.6 % |
| stalls: `mio_throttle` | 0.6 % | 3.1 % |
| stalls: `wait` / `not_selected` | 15.3 / 27.1 % | 22.6 / 13.6 % |

Read together:

- **The compaction did what it promised.** `fmaheavy` fell 12.7 points and
  `math_pipe_throttle` fell from the largest stall (28.4 %) to 8.6 %. The multiply pipe is
  no longer the constraint.
- **It moved the work onto a narrower pipe.** `lsu` went 32.2 % -> 87.19 % and is now the
  whole SM speed-of-light. Total executed instructions barely changed (+4.3 %) — this is
  not "more work", it is **the same amount of work on a pipe with less throughput**.
  `short_scoreboard` (the shared-memory dependency stall) tripled to 33.9 % and is the
  largest stall.
- **Occupancy halved as a second, independent cost.** `G / 2` elements per lane multiply
  every operand and accumulator array; 40 -> 67 registers takes blocks/SM from 6 to 3.
- **Memory behaviour is untouched and still perfect**: identical global load sectors and
  1.000× the DRAM floor. Nothing about this rung is a traffic story.
- **`adu` falling from 57.95 % to 9.06 % is OPEN, not explained.** (The R1 commit reported
  0.85 % here; that was the pre-permutation build, and the shipped layout's own address
  arithmetic puts it at 9.06 % — a smaller drop, same open question.) The obvious reading
  — "the schedule carries precomputed offsets" — does not survive contact with the table:
  those are *shared* offsets and R0 has no shared memory at all, while the **global**
  element-index arithmetic is unchanged between the two modes (identical issued load
  sectors, the same expression per reference). So either R0's original 58 % ADU
  attribution was wrong, or this moved for a reason none of the three profiles isolates. Recorded as
  a contradiction to resolve, not as a win to claim.

### Verdict, and what it does to the radix-4 arm

**R1 is a MISS and the mechanism is falsified as a wall-time lever, not as arithmetic.**
Packing the real multiplies is achievable, exact, and worth 43–50 % of the producer's
multiplies per row; it cannot pay for itself through shared memory on this part, because
the staging costs more LSU instructions than the multiplies it saves cost mul-pipe
instructions, and the LSU pipe is narrower. R0 (`--mode lsb-recompute`) remains the
recommended v3 arm.

What this does **not** falsify: the multiply cut itself. Any mechanism that removes those
62 unity multiplies **without** a per-element shared-memory round trip is still live — the
cost was never the packing, it was the medium.

**Blocked radix-4 stays PARKED, now doubly so.** It recovers 32 of the 62 unity multiplies
(28.6 % of the 112 issued, per the gate record above) while *keeping* the shuffle binding,
so it pays no staging cost at all — which is now the interesting property, not the 28.6 %.
But R1 has measured the prize: the whole 62 (compaction's 43–50 % per-row cut, a superset
of radix-4's) bought −12.7 points of `fmaheavy` and **still lost 15 %** once the enabling
mechanism was priced. Radix-4 would capture roughly half that arithmetic for a different
cost — two cross-lane transposes, a 4x register map on a kernel already at 3 blocks/SM,
and an `e4` axis transpose. The micro-A/B it owes is now a *smaller* prize against
*measured* evidence that this class of trade does not clear on this part, so it does not
advance.
