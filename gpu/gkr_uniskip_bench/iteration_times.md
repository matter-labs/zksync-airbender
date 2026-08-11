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

The `-o` above omitted the profiling doc's `$(date +%Y%m%d_%H%M%S)_` prefix; the report
was renamed post-capture to
`target/profiling/ncu/20260808_153705_v3r0_lsb_locality_full.ncu-rep` (prefix = its
session creation time; the report's internal command line still shows the original
`-o`). Future captures should use the prefixed form — the commands carry `-f`, so a
stable name silently overwrites the report a recorded table cites.

**Capture deviation (applies to every report in this directory to date, v2's first
capture onward).** The doc's Full Picture recipe (`gpu/docs/profiling_ncu.md`) does not
use `--set full` — it prescribes an explicit 17-section list precisely to exclude what
`full` adds on this ncu (2026.2.1): `NumaAffinity`, `Nvlink_Tables`, `Nvlink_Topology`,
`PmSampling`, `Tile`. It also prescribes `--nvtx --nvtx-include` (this crate's
`--profile` flag emits the `gkr_uniskip_pass0` range for exactly that) and
`--import-source yes` + `--source-folders` under lineinfo. The as-run commands used
none of these. Every counter the tables here cite lives in sections common to both
recipes (SpeedOfLight, InstructionStats, SchedulerStats/WarpStateStats,
MemoryWorkloadAnalysis*, Occupancy, LaunchStats), so the recorded values are
unaffected; the cost was capture-side only — unrequested sections, PM sampling,
250–360 MB reports, extra replay passes. Future captures: use the doc's Full Picture
block verbatim.

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

  **CLOSED BY R2 (see the v3 R2 section); the R1 note below is kept for the lineage.**
  Pair-residency reaches **64 issued multiplies per group — the same count any co-located
  packing achieves — at the smallest register bill of the family** (2 elements per lane
  against radix-4's 4), with no transposes and no `e4` axis complication, and it measured
  **−20.9 %** of wall. Radix-4's remaining distinguishing property was only ever part of
  the residual 14 exponent-zero pairs, at double the accumulators on a kernel already at
  3 blocks/SM. The gate does not advance and the arm should not be built without a new
  argument.

  **Superseded by R1 first, which is how it got here.** The v3 R1 rung took the
  *superset* of this prize — all 62 unity multiplies, not radix-4's 32 — by dissolving the
  lane = tap binding in shared memory. It delivered the arithmetic exactly
  (`fmaheavy` 81.5 % -> 68.7 %) and **still lost 14–15 %** of wall time to the enabling
  mechanism. Radix-4's distinguishing property is therefore no longer the 28.6 % — it is
  that it pays no staging cost — but it captures roughly half the arithmetic that R1
  proved insufficient, for its own unpriced costs. The micro-A/B is still owed and the
  gate still does not advance; it is now a smaller prize against measured evidence that
  this class of trade does not clear on this part.
- **Constant-load serialization was designed out in source — but not in the emitted
  SASS** *(corrected 2026-08-09; this bullet originally claimed the profile did not
  contradict the design)*. The twiddle tables are lane-indexed, so a hot-path
  `__constant__` read is a 16-way divergent access; the source hoists all seven into
  per-lane registers once at entry, but ptxas rematerializes the lane-indexed `LDC`s
  inside the record loop under register pressure (1.79 `LDC`/record here), and that
  remat is exactly the ADU-pipe signal (57.95 %) the table above left unexplained —
  see the 2026-08-09 audit round at the end of this file. Static constant traffic is
  57 `LDC`/`LDCU` in a 3216-instruction body, and `no_instruction` is 1.1 % of stalls
  with `sm__icc_requests` at 63.8 % of peak — below v2's 76.6 %. Not binding in any arm.
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
   v3 R1 section. **v3 R2 then removed them in registers** — pair-resident radix-2,
   `lo = u + v; hi = (u - v) * w`, where the unity multiply is never written — for
   −20.9 % of wall, which closes this lever and with it blocked radix-4 (32 of the 62, at
   double the accumulators). (b) **The window** (R2/R3), which
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
68.7 %); it buys nothing because the staging that enables it moves the work onto a
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
**44x** the ~0.02 % reproducibility the R0 record demonstrated across rebuilds, so it is
worth accounting for rather than passing over. It is **not codegen**: this rung adds a
translation unit and a ~5 KB `__constant__` to the same device link
(`CUDA_SEPARABLE_COMPILATION`), which could plausibly perturb existing kernels, so the
`lsb-recompute` kernel's sm_120 SASS was recounted in this build — **3216 instructions,
identical to the R1 commit's and to the R0 record's**. The drift is therefore session /
measurement, not code. The miss stands on either denominator: **+14.1 % to +15.1 %**.

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
(`target/profiling/ncu/20260808_181923_v3r1_compact_g4_locality_full.ncu-rep`, date
prefix added post-capture as for R0's report). **Re-profiled on the
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
- **It moved the work onto a narrower pipe.** `lsu` went 32.2 % -> 86.85 % and is now the
  whole SM speed-of-light. Total executed instructions barely changed (+4.5 %) — this is
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
of radix-4's) bought −12.7 points of `fmaheavy` and **still lost 14–15 %** once the enabling
mechanism was priced. Radix-4 would capture roughly half that arithmetic for a different
cost — two cross-lane transposes, a 4x register map on a kernel already at 3 blocks/SM,
and an `e4` axis transpose. The micro-A/B it owes is now a *smaller* prize against
*measured* evidence that this class of trade does not clear on this part, so it does not
advance.

## v3 R2 — pair-resident radix-2 (`--mode lsb-pair`): WIN, −20.9 %

RR's insight, and it is a source-text argument rather than a scheduling one: a
divergence-free radix-2 butterfly needs **both halves of the pair in the same lane**. R0
binds lane = tap, so the halves are lane-divergent and a stage must read as a select plus
an *unconditional* multiply — unity on half the lanes, unskippable. Put the pair in one
lane and the stage becomes

```
lo = u + v;            // no multiply exists here, at any stage
hi = (u - v) * w;
```

The unity multiply is not skipped, predicated, or scheduled around — **it is never
written**. No shared memory, no schedule table: the register medium R1 vindicated, with
the multiply cut R1 proved relieves the pipe.

**Result: 16.283 ms `eval + finalize` (locality), −20.9 % against R0's bar and −29.4 %
against v2's best arm** — the first arm to land inside the design's original 16–19 ms
first landing zone, at its bottom edge.

### Geometry and the re-pair

A group's 16 taps live on **8 lanes, two per lane**; a warp holds 4 groups, so a block of
256 threads covers **32 logical rows** — twice R0's decode amortization, free. While the
chain pairs on tap bit `b`, lane `l` holds the two elements whose bits-other-than-`b` are
`l` and whose bit `b` is the slot; that map is a bijection at every `b`.

The pairing a stage needs changes with its distance, so between stages each lane **keeps
one output and trades the other**: one `shfl_xor` per re-pair. In the lane index at stage
`b` (the tap index with bit `b` deleted) the bit to trade is `b_next`, shifted down by one
when it sat above the deleted bit — giving masks **4, 2, 1, 1, 2, 4** for the chain's six
bit changes. Both sides of a trade run the same three selects:

```
sent = high ? lo : hi;   recv = shfl_xor(sent, MASK);
lo   = high ? recv : lo; hi   = high ? hi : recv;
```

Two consequences fall out. The chain **ends on the map it started on**, so `H` (loaded as
taps `l`, `l + 8`) and the coset (cells `l`, `l + 8`) share one layout and the consumer
needs no re-indexing. And the warp's four groups sit at lane offsets `group * 8`, so the
epilogue merge is `xor 8` then `xor 16` — R0's single `xor 16` argument at four groups,
gated by `q` rather than by analogy.

### The counts

| | R0 `lsb-recompute` | R1 `lsb-compact` G = 4 | **R2 `lsb-pair`** |
| --- | --- | --- | --- |
| lanes per group | 16 | 16 (staged) | **8** |
| rows per block | 16 | 32 | **32** |
| issued multiplies per group | 112 | 64 (+ SMEM staging) | **64** |
| producer multiplies per row (static SASS) | 77.0 | 44.0 | **44.0** |
| producer shuffles per row (static SASS) | 88.0 | 0 (SMEM instead) | **33.0** |
| shared-memory instructions | ~0 | 4.44 G | **~0** |
| accumulators per lane | 2 `e4` | 2 `e4` | 4 `e4` |

R2 reaches R1's multiply count with **none** of R1's medium: 64 issued multiplies per
group either way, but R1 paid 4.44 G shared instructions for it and R2 pays 0. The
residual over the algebraic 50 is the 14 exponent-zero pairs (1+2+4+4+2+1 across the six
stage tables), lane-divergent at pack-2 and deliberately left issued.

### Gates — all pass

- **Host executor** (`cpu_pair_chain_matches_reference`): runs the pair chain's semantics
  in the kernel's own shape — pair butterfly, re-pair permutation, twist — against
  `domain::coset_from_taps` over the canonical extremes, all 16 single-tap impulses and 64
  pseudorandom sets, plus every `E4` limb position against a dense apply
  (`cpu_pair_chain_e4_limbs`). **Mutation-checked**: moving the DIF multiply to the low
  output fails it, and so does perturbing one re-pair mask.
- **Cross-mode oracle**: `q` bit-exact equal to `lsb-recompute`'s, compared device-to-device
  with `--dump-q` under both term orders — same `sha256[0:16] = ed3bead0bce8833d` as every
  other v3 arm.
- **Standard cells**: 8/8 `q validate: OK (32/32)` — {`census`, `locality`} x
  {`--validate`, `--validate-flat-eq`} x {`--self-products 0`, `--self-products 12`}.
- **ptxas 0 stack / 0 spill and zero `LDL`/`STL` on sm_80/89/90/120.**

| kernel | sm_80 | sm_89 | sm_90 | sm_120 | blocks/SM (sm_120) |
| --- | --- | --- | --- | --- | --- |
| `…_lsb_w0_kernel` (R0) | 96 | 96 | 56 | **40** | 6 |
| `…_lsb_compact_g4_kernel` (R1) | 127 | 127 | 73 | 67 | 3 |
| `…_lsb_pair_kernel` (R2) | 138 | 138 | 72 | **72** | **3** |

  Four `e4` accumulators instead of two costs 40 -> 72 registers and halves occupancy;
  R2 wins by 21 % anyway, which is the headline finding of the profile below.

- **SASS mechanism**, four-arch, from the chain's 22 inlined instantiations (6 `bf`
  operand sites + 4 `e4` sites x 4 limb passes). The chain slice is separable from the
  rest because the remainder scales with elements per lane, so the split below is a
  measurement rather than an attribution (sm_120):

| kernel | total `IMAD.WIDE` | of which chain | non-chain remainder | elements/lane | rows/walk | **chain muls/row** | issued muls/group |
| --- | --- | --- | --- | --- | --- | --- | --- |
| R0 `lsb-recompute` | 423 | 22 x 7 = 154 | 269 | 1 | 2 | **77.0** | 112 |
| **R2 `lsb-pair`** | 655 | 22 x 8 = 176 | **479** | 2 | 4 | **44.0** | **64** |

  **Erratum (2026-08-09, found in v3 R4 Task 1B): 655 pools two different mnemonics.**
  It was a naive substring count, so it included 9 `UIMAD.WIDE.U32` on the UNIFORM
  datapath. Mnemonic-anchored — the convention this record uses from here, with `U`-forms
  counted separately — the R2 control is **646** `IMAD.WIDE.U32` + 9 `UIMAD.WIDE.U32`, and
  R4's cached body is 701 + 6. The 1.4 % shift changes no conclusion here; the note exists
  so a cross-rung subtraction does not silently mix the two conventions.

  The remainder is 479 against 269 for twice the elements per lane — 1.78x, the same
  near-linear scaling R1's table showed at 1.96x/3.89x for 2 and 4 — so the chain slice is
  not absorbing it. Shuffles: **6 per chain x 22 = 132 static = 33.0/row** against R0's
  `8 x 22 = 176` over 2 rows = 88.0, i.e. **0.375x**. (Measured `SHFL` totals are 164 and
  184; the extra 32 and 8 are the epilogue reductions — two masks x four `e4`
  accumulators, and one mask x two.)

  **Correction (2026-08-09 audit round): the "of which chain" column is wrong in
  absolute terms.** Line-info attribution measures chain static `IMAD.WIDE` at **339
  (R2) / 316 (R0)** — ~15.4/14.4 per inlined site, because a `bf::mul` context costs
  ~2 WIDE (mul_wide + a red_wide-form reduction on some paths) and interleaved
  next-reference addressing lands inside the chain slice. The non-chain remainders are
  316/107, and the separability-by-scaling argument above fails (2.95x for 2x
  elements). The conclusions survive and strengthen as direct measurements: producer
  `bf::mul` per row 1141 → 652 (−43 %, exactly the recorded ratio), chain instructions
  per row −29 %, whole stream −22.3 %.

### Timings

**All four rows below are one session, one build**, and every number in the table is
emitted from the run log by `tools/timing_table.py` rather than transcribed (the bold
emphasis and the U+2212 minus signs are hand-applied on top of the emitter's output) —
the R1 record lost two review rounds to hand-assembled tables, so the capture and the
emit are now separate steps:

```bash
.agents/bin/with_gpu_lock.sh bash -c '
  B=target/release/gpu_gkr_uniskip_bench
  for spec in "lsb-pair census" "lsb-pair locality" \
              "lsb-recompute census" "lsb-recompute locality"; do
    set -- $spec
    echo "=== MODE=$1 ORDER=$2"
    $B --log-trace 24 --warmup 10 --iterations 100 --mode $1 --term-order $2
  done' > /tmp/runlog.txt

python3 gpu/gkr_uniskip_bench/tools/timing_table.py /tmp/runlog.txt \
    --control lsb-recompute --bar census=20.713 --bar locality=20.596
```

| arm | `eval` | `finalize` | **eval + finalize** | vs recorded bar | vs same-session control | spread (`eval` min-max) |
| --- | --- | --- | --- | --- | --- | --- |
| `lsb-pair` census | 16.420 | 0.033 | **16.453** | **−20.6 %** | **−21.0 %** | 16.410–16.504 |
| `lsb-pair` locality | **16.250** | 0.033 | **16.283** | **−20.9 %** | **−21.4 %** | 16.247–16.275 |
| `lsb-recompute` census | 20.767 | 0.061 | 20.828 (control) | +0.6 % | — | 20.352–20.834 |
| `lsb-recompute` locality | 20.645 | 0.061 | 20.706 (control) | +0.5 % | — | 20.326–20.713 |

A second independent run of the two `lsb-pair` cells gives 16.612 / 16.294 — census drifts
+1.2 %, locality +0.03 %, the same session-level scale the R1 record documented. The
control sits +0.5 to +0.6 % above its recorded bar, so the win is −20.6 % to −21.4 %
whichever denominator is used.

**Annotation (2026-08-09, v3 R4): these numbers are a record, not a cross-session gate.**
R4 used the 16.28–16.51 ms band derived from them as a sanity gate and the **frozen,
byte-identical shipping kernel missed it in both orders** (16.545 / 16.624 in the factorial,
16.690 / 16.608 standalone in a second session) under an active `SwPowerCap` and a
monotonically warming session. The band is kept — it caught a real 1.4–2.0 % session effect
— but a miss now demands a standalone anchor plus an event-reason sample before it is read
as a regression. See *v3 R4*.

Against the whole ladder: **v1 90.462 -> v2 23.078 -> R0 20.596 -> R2 16.283** on
`pass − fold`, i.e. **5.56x v1** and **−29.4 % against v2's recommended arm**. On the
corrected unit basis, 16.283 / 1.875 = **8.68 ms/unit**, **1.09x** the 8.00 ms/unit
windowed reference — the parity bar for a k = 4 pass is 15.0 ms, now **8.6 %** away.

### ncu — `lsb-pair` locality against R0

R0's recipe with the kernel regex and mode swapped; the report's session page carries
this command line internally:

```bash
.agents/bin/with_gpu_lock.sh ncu --set full \
    --metrics dram__bytes.sum,l1tex__t_sectors_pipe_lsu_mem_global_op_ld.sum,smsp__inst_executed.sum \
    --kernel-name-base demangled --kernel-name 'regex:ab_gkr_uniskip_eval_lsb_pair_kernel' \
    --launch-count 1 --target-processes all -o target/profiling/ncu/v3r2_pair_locality_full \
    target/release/gpu_gkr_uniskip_bench --log-trace 24 --warmup 1 --iterations 1 \
    --mode lsb-pair --term-order locality
```

As with R0, the `-o` omitted the doc's date prefix; the report was renamed post-capture
to `target/profiling/ncu/20260808_190552_v3r2_pair_locality_full.ncu-rep`. The R0
section's capture-deviation note (`--set full` vs the doc's explicit section list, no
NVTX include, no source import) applies to this capture identically.

| metric | R0 `lsb-recompute` | R1 `lsb-compact` G = 4 | **R2 `lsb-pair`** |
| --- | --- | --- | --- |
| duration under the profiler | 21.14 ms | 23.84 ms | **16.91 ms** |
| **bounding pipe** | `fmaheavy` 81.51 % | `lsu` 86.85 % | **`fmaheavy` 81.85 %** = SM SOL 81.59 % |
| `sm__inst_executed_pipe_lsu` | 32.20 % | 86.85 % | **18.27 %** |
| `sm__inst_executed_pipe_alu` / `adu` | 35.00 / 57.95 % | 28.19 / 9.06 % | 39.53 / 50.21 % |
| executed instructions | 24 388 763 648 | 25 475 055 616 | **18 941 444 096** (−22.3 % vs R0) |
| shared instructions | ~0 | 4 444 979 200 | **~0** |
| `dram__bytes.sum` vs floor | 6.21 GB, 1.000× | 6.22 GB, 1.000× | **6.21 GB, 1.000×** |
| global load sectors | 684 195 840 | 684 195 840 | **684 195 840** (identical) |
| registers, blocks/SM | 40, 6 | 67, 3 | **72, 3** |
| achieved occupancy | 99.28 % | 49.74 % | **49.71 %** |
| stalls: `math_pipe_throttle` | 28.4 % | 8.6 % | 22.3 % |
| stalls: `not_selected` / `wait` | 27.1 / 15.3 % | 13.6 / 22.6 % | 22.7 / 21.5 % |
| stalls: `short_scoreboard` | 9.9 % | 33.9 % | 10.3 % |

What this settles:

- **The win is a pure work reduction.** Executed instructions fall **22.3 %** and the wall
  falls 21 % — the kernel stays exactly where R0 was, `fmaheavy` ≈ SM SOL ≈ 82 %, and
  simply has less to do. Nothing moved to another pipe; `lsu` *fell* 32.2 % -> 18.3 %
  because the shuffle traffic dropped 0.375x and each element is still one global load.
- **It wins at HALF R0's occupancy.** 72 registers puts it at 3 blocks/SM against R0's 6,
  and it is 21 % faster regardless — the same lesson v2's rung 2a recorded, restated: on a
  throughput-bound kernel occupancy is not what orders the arms.
- **Memory behaviour is untouched**: byte-identical issued load sectors to R0 and R1, and
  1.000× the DRAM floor. Every v3 arm now agrees on this, which is what makes the three
  comparable as pure compute experiments.
- **R1's read-across held.** The same −43 % multiply cut that bought R1 −12.7 `fmaheavy`
  points bought R2 −22 % of instructions and −21 % of wall — the difference being entirely
  the medium. R1 was the control that proves R2's mechanism is the multiply cut and not
  something incidental.
- `adu` at 50.2 % is now the second pipe, and the R1 record's open question about the ADU
  attribution stands unresolved — R2 does not settle it either.

### Verdict and what it does to the radix-4 arm

**R2 ships as the recommended v3 arm.** It is the fastest arm this crate has measured, on
the same 5.75 GiB footprint, at 1.000× the DRAM floor, zero spills, and a `q` that is
bit-exact with every other v3 mode.

**Blocked radix-4 is closed as a distinct arm, not merely parked.** Its stated prize was
recovering unity multiplies while keeping the shuffle binding. Pair-residency reaches
**64 issued multiplies per group — the same count any co-located packing achieves — at the
smallest register bill of the family** (2 elements per lane; radix-4 needs 4, doubling the
accumulators again on a kernel already at 3 blocks/SM) and with no transposes and no `e4`
axis complication. What packing higher could still buy is part of the residual 14
exponent-zero pairs, and R1 measured what removing *all* 62 of R0's unity multiplies is
worth once a medium is priced. There is no longer a hypothesis under which radix-4 wins
that pair-residency has not already collected more cheaply; the gate does not advance and
the arm should not be built without a new argument.

## 2026-08-09 — v3 audit round: two independent audits + production pricing

Four reports, all under `.agents/audits/` (gitignored; referenced by name):
`2026-08-09-gkr-uniskip-v3-pair-perf-audit.md` and `…-pair-perf-audit-codex.md` (two
audits from the same brief, run blind to each other), `…-uniskip-window-pricing-from-
blue-nsys.md` (production timings), and `…-windowed-vm-learnings-for-uniskip.md`
(red-worktree lesson mining). Fresh **doc-conformant** Full Picture captures (13–16 MB
vs the deviating recipe's 250–360 MB): `target/profiling/ncu/`
`20260809_114230_full_v3r2_pair_locality.ncu-rep` (+ R0 `_114251_`, R1 `_114317_`, and
codex's independent `_113848_`/`_113909_` pair). Every counter re-measured under the
conformant recipe reproduces the committed `--set full` values (executed instructions
to the last digit, pipe percentages within 0.05 pt) — the capture deviation recorded
at the R0 block was cost-only, as claimed. Capture gotcha for future runs: the crate's
NVTX range is push/pop, so ncu needs `--nvtx-include "gkr_uniskip_pass0/"` (trailing
slash) or it profiles nothing.

### Verdicts — both audits, independent agreement

- **The pair kernel is bound by the width of the fmaheavy pipe.**
  `sm__pipe_fmaheavy_cycles_active` 81.9 % = SM SOL 81.6 %, while the *instruction*
  rate is only 65.5 %: `IMAD.WIDE` (every `mul_wide`) double-pumps the pipe ~2 cycles.
  Memory is nowhere (DRAM at **1.0024×** the compulsory floor — the recorded `1.000×`
  was a fair rounding, not an exact ratio), LSU 18 %, issue slots 64 %. Occupancy
  49.7 %, reg-limited, and **not binding** — R0 is the control: 100 % occupancy, the
  same 82 % pipe ceiling, loses by 21 %. Same-session A/B reproduces the record:
  16.281 vs 20.587 ms = −20.9 % (absolute drift vs the recorded bars +1.4–1.7 % across
  arms today; ratios stable — the same-session rule holds).
- **Producer = 78.7 % of executed instructions / 78.5 % of warp time** (the
  shuffle-NTT chain alone 65.1 % / 58.6 %); consumer ~20 %, epilogue ~1 %. 234 of the
  326 producer passes per warp are repeat productions.
- **The window is the only lever of size, and it is bigger than the parity gap.**
  Perfect-window ceiling −50…−54 % of executed instructions (wall floor ≈ 7.5–9 ms);
  parity needs only **~19 % capture of the removable productions** (~44 of 234 per
  warp ≈ 1.3–1.5 ms). A schedule-free fixed **top-4-BF register window** costs exactly
  the 8 spare registers to the 80-reg/3-block cliff and models **−8…−10 %** (hot-8 =
  39.7 % of refs ≈ −12…−13 % but crosses 80 regs → needs the 2-block study). E4
  sources are the best per-register retention: 42 % of producer passes come from the
  15 % of references that are E4. Landing the top-4 window models ≈ 14.3 ms ≈ 7.6
  ms/unit = 0.95× the windowed reference.

  **Superseded (2026-08-09, v3 R3 — measured and refuted).** The top-4-BF register
  window was built as a six-arm factorial and MISSED: the best window arm is 17.173 ms
  (+5.44 % over the control), not ≈ 14.3. At fixed occupancy the machinery costs
  +1.207 ms against a −0.879 ms removal. The *schedule* is validated (−1.124 ms alone,
  100/100) — the register carrier is not. See *v3 R3* for the decomposition and the
  recalibrated 18.70 µs/production slope, which raises the parity capture from ~19–24 %
  to ~38 %.
- **Second lever: twiddle-remat fix**, −1.5…−3.5 %, trivial A/B
  (`__launch_bounds__(256, 3)` so ptxas sees the true 80-reg budget, or a 448 B smem
  stage per block, which is remat-proof). Competes with the window for the same 8
  spare registers — decide jointly; the window subsumes part of it.

  **Superseded (2026-08-09, v3 R3 — the A/B was run and does not test this).**
  `__launch_bounds__(256, 3)` is **+3.43 %**, not −1.5…−3.5 %, and bank-resolved counters
  show the twiddle remat **byte-identical** with and without it (824 loads/walk both
  ways) — it moved a *different*, bank-0 stream from the uniform to the vector datapath.
  The lever was tested in neither direction; it is now closed **on priority**, with the
  smem-table variant closed too (no replay amplification is visible in any captured
  counter). See *v3 R3*.
- **Closed**: 4-block/64-reg occupancy (control above; −8 regs would spill); the 14
  residual exponent-zero pairs — **confirmed closed with a sharper argument**: at warp
  granularity they are lane slots inside the 8 mul warp-instructions each pass must
  issue anyway, there is no instruction to delete; lazy add/sub canonicalization
  (≲ 2 %, on alu — not the binding pipe); epilogue smem conflicts (0.8 % of stream);
  load path (sectors byte-identical across arms, already minimal). Pure tuning without
  work removal is capped at −10…−18 %.
- **ADU resolved, quantitatively, blind-agreed by both audits**: divergent
  lane-indexed `LDC` replays from the twiddle loads that **ptxas rematerializes inside
  the record loop** — source-level "hoisted once at entry" does not survive
  compilation (R2: 8 entry loads + 6 remat sites, 5.03 `LDC`/record). Predicted vs
  measured pipe %: R0 56.7 / 57.95, R2 50.0 / 50.25, R1 (smem-staged, no indexed
  stream) 8.2 / 9.06 — the swing is fully explained; the R1 record's "adu OPEN" is
  closed. Not binding: 31.6 pt below the fmaheavy pipe, IDC hit ≥ 99.8 %.

### Parity re-anchored against shipping production

From the one existing production profile (`green/target/profiling/nsys/
20260807_095813_add_sub.nsys-rep`, `av_gkr_compiler` prover, add_sub, 2^24 trace =
this bench's size, same GPU): shipping layer-0 sumcheck is **not windowed** — one
kernel per round (`bwd_seg_r0` BF + `bwd_seg_cont` E4) — and rounds 0–3 cost
**24.11 ms** (5.522 + 8.039 + 6.541 + 4.010 + 0.355 aux; r1 > r0 because the BF→E4
lift beats the halving). **The 16.283 ms pass beats shipping today: −32.5 %**, and
still −12.8 % under the most conservative accounting that charges the bench's separate
4.743 ms fold to the pass. Per halving-adjusted unit: production 12.86, `lsb-pair`
8.68, windowed bench 7.79 ms/unit. The 15.0 ms bar is therefore *demoted, not wrong*:
it prices parity vs the windowed **candidate** (red worktree, unmerged), whose actual
endpoint is 13.637 ms → tightened bar **14.61 ms**. The remaining window-lever prize
stays bench-derived — 0.89 ms/unit ≈ **1.67 ms/pass** — consistent with the audits'
~19 %-capture arithmetic. Caveats in the pricing report: single-sample profile,
2-day-old green tip, synthetic census mix, fold-boundary accounting.

### Corrections applied to this record (2026-08-09)

1. **R2 §SASS mechanism**: the "of which chain 22 × 8 = 176 / 22 × 7 = 154"
   `IMAD.WIDE` split understated the chain ~2× — measured 339/316, remainders
   316/107, separability-by-scaling fails. Corrected in place at the table; the −43 %
   conclusion survives as a direct measurement.
2. **R0 "constant-load serialization designed out / profile does not contradict it"**:
   contradicted — the remat is the ADU signal. Corrected in place; README and the
   pair-kernel comment carried the same claim and were corrected with it.
3. Minor: `compact_g8` is **130 regs** in the shipped native-only build vs the
   recorded 128 (four-arch diagnostic build); R2/R0/R1-g4 match exactly (72/40/67).

### Imported lessons (red worktree, `rr/gpu_windowed_gkr`)

Compact pointer — full mapping with evidence in the learnings report. Stackable
micro-levers for after the window rung: unfuse the E4-by-BF fold (~1 %), lazy
wide-product accumulation on the term side (~1–2 %), invariant-first `e4::mul` operand
order in the eq epilogue (two-token edit), host-resolved per-source pointers (priced
3.28 % on windowed's identical addressing shape). Inherited negatives: never outline;
SMEM staging loses in this family (now a two-kernel law with R1); forced
`__launch_bounds__` down-regs = spills; at math-SOL, occupancy pushes regress.

### Ratification pass (resident codex reviewer, same day)

The long-lived codex reviewer read all five reports plus this section and **ratifies
the pipe-width verdict, the IMAD.WIDE model, the window as the only gap-sized lever,
and the two-rung ladder** — with three refinements, each verified before adoption:

1. **The ~19 % parity-capture figure is stale against the tightened bar** (it was
   computed vs 15.0). Vs 14.61 ms: 16.283 → 14.61 = 1.673 ms at the measured
   29.6 µs/pass slope ⇒ **~56–57 of 234 removable ≈ 24 % capture**. Top-4-BF alone
   saves 51 refs − 4 fills = 47 productions = 20.1 % ⇒ ≈ 14.9 ms — **borderline, not
   a 14.3 ms landing**; clearing 14.61 likely takes top-4 + the twiddle win together
   (or a fifth retained source). **Superseded (2026-08-09, v3 R3):** the direction was
   right and the magnitude was not — top-4 + the launch bound measured **17.173 ms**,
   and at the measured 18.70 µs/production slope parity needs ~38 % capture, not 24 %.
2. **The 8-register top-4 figure is a coset-only window** — verified against
   `uniskip_pair_resolve(…, bf h[2], bf c[2])`: a fully retained BF source is 4 regs
   (h + c), so top-4 full retention = 16 regs; 8 regs retains `c[2]` only and reloads
   `h[2]`, skipping the chain but not the resolve loads. The −50…−54 % perfect ceiling
   and the top-4 model are therefore *different realizations*; don't mix their
   arithmetic.
3. **E4 is not the best per-register retention on this census**: width cancels —
   saved component passes per register = (refs − 1)/2 for BF and E4 alike — so the
   hot BF sources (12–13 refs) beat the hot E4 sources (7 refs) per register. E4's
   42 %-of-passes share is a *coverage* argument for larger W, not a marginal one.

Further qualifications adopted: realization D **reframes rather than dissolves**
A-vs-B (global scratch, publish traffic, residency uncertainty, extra consumer loads
are new costs); keep D bounded by admitted W — never publish all 59 sources — publish
coset values only at first, and keep the pair kernel's row ownership (each warp
produces admitted sources for its own 4 rows; seg's lane=row striping does not
transplant). The `.cs` hint on H prologue loads is wrong while H is still reread from
its original backing — stays `.ca` unless H is also published. Rung-1 design: a
four-arm same-session factorial (R2 control / twiddle-fix only / coset-only top-4
only / both), gated on SASS facts (production count 326 → 279, zero spills, dynamic
remat-LDC count, exact regs + blocks/SM) and using a real warp-uniform source→slot
selector — hardcoded source IDs would dodge the production addressability cost.
Rung-2: W ∈ {0, 4, 16-BF-equivalent} with publish/read DRAM directions counted
separately and `q` parity pinned across W. The shipping-production −32.5 % margin is
directional comfort, **not** a reason to relax the 14.61 ms target (census and fold
boundaries are not yet production-equivalent).

## v3 R3 — register-window factorial (`--pair-arm` / `--factorial`): MISS, and what it decomposed

The audit round named the coset-only top-4-BF register window as the one lever bigger than
the parity gap and modelled it at **−8…−10 %**. Built and measured as a balanced
same-session factorial, it is **a miss, and not a marginal one**: no window arm beats the
R2 control, the best is **+5.44 %**, and the rung's value is what the decomposition buys
rung 2 rather than any arm it produced.

The rung is deliberately built as a factorial rather than as one candidate kernel, because
the interesting quantity was never "is the window faster" — it is **what a retained source
costs to carry and what a skipped production is worth**, separately. Those two numbers are
the rung-2 calibration, and they only exist because arms were built that nobody would ship.

### Design — what was built

- **Carrier: a coset-only top-4-BF register window.** A retained slot keeps the BF source's
  `c[2]` only; `h[2]` is still loaded on reuse. That is the audit's 8-register realization
  (a fully retained BF source is 4 registers, so top-4 full retention would be 16) — it
  skips the chain, not the resolve loads. The 8 registers are exactly the spare capacity to
  the 80-register / 3-block cliff.
- **Wire: a window-only side descriptor**, `UniskipWindowDesc` (272 B, align 16, offsets
  0 / 256 / 264, `.cuh` twin with `static_assert`s). **The control wire is untouched**, so a
  bare `--mode lsb-pair` is bit-identical to the R2 record — the window is additive, not a
  re-plumbing.
- **Tags: two-operand nibbles.** One byte per record carries operand A in the low nibble and
  operand B in the high (`0 = None`, `1+slot = Fill`, `1+SLOTS+slot = Reuse`). Two operands
  per byte is forced by the census: 11 of the tags on the default census land on operand B,
  and 2 fills / 27 tags land *inside* group members where `uniskip_lsb_pair.cu` multiplies
  `ac[k]` in place — so a fill must capture its slot copy before the clobber.
- **Slots: named registers behind warp-uniform switches**, with the production done once
  before the switch. A dynamically indexed slot array would spill to local memory and a
  hardcoded source ID would dodge the addressability cost the arm exists to measure.
- **Schedule: host-planned per (program, term order, census knobs)**, with an always-on
  state-machine validator (a reuse of a slot that is not live is a plan bug, not a device
  symptom). `select_slots` takes the top-4 BF sources by reference count; on the default
  census that is sources 0–3 with **13 / 13 / 13 / 12** refs, **47 reuses**, component
  passes per walk **326 → 279**.
- **The six arms.** `control` = R2 unchanged. `t` = `__launch_bounds__(256, 3)` alone.
  `w` = window alone. `wt` = both. `wnone` = the window kernel and its descriptor with an
  all-`none` tag stream — it pays the machinery and takes none of the saving. `wtnone` = the
  same at 3 blocks, which is what splits `wt − t` into **machinery alone** and **removal
  alone** without crossing an occupancy class.

Commits: `4814469b` (host schedule, tags, validator, CLI), `47cdf650` (kernel arms),
`a9529726` + `3f9b7cbe` + `8f63acdc` (gates and two fix rounds), `2ca39cea` + `7184169f` +
`0626a985` (factorial runner, the `wtnone` lane, emitted tables).

### Gates — all pass, and two of them changed the result

- **Control SASS frozen before any edit** and re-verified after: per-function, **5104**
  instructions, verified independently and unmasked. Spill gate on every arm and arch: zero
  stack, zero spill, zero `LDL`/`STL`.
- **Registers and blocks/SM (sm_120)**: `control` 72/3, `t` 79/3, `w` 82/**2**, `wt` 80/3,
  `wnone` 82/**2**, `wtnone` 80/3. **`w` and `wnone` are 2-block arms.** The cliff is
  measured, not assumed: `__launch_bounds__(256, 3)` caps at **80** registers, not 85, and
  allocation granularity is 8 — so 82 registers is 88 allocated and drops a block. `wt`'s
  82 → 80 cut is the confirmation. Every contrast in the table below is labelled with its
  occupancy class for exactly this reason.
- **`q` parity, 40/40 cells** — all five non-control arms against the control across
  2 term orders x 2 `eq` forms x 2 censuses, device-to-device via `--dump-q`, with an
  empty-digest rejection because an empty dump hashes identically on both sides and would
  pass every cell vacuously. Run on both the shipped and the diagnostic build.
- **Production count EXACT, both term orders**: a compile-gated device counter reads **279**
  chain executions per warp-program walk under `w`/`wt` and **326** under
  `control`/`wnone`/`wtnone` — the host model's 326 → 279 is achieved, not merely planned,
  and the all-`none` stream provably skips nothing.
- **Mutation tests discriminate slot identity and retention.** (a) *Retarget*: a reuse is
  pointed at a **different, already-live slot holding another source**, and the corrupted
  descriptor is uploaded through the unchecked path that bypasses the always-on validator —
  `q` diverges in all four (arm x order) cells. This is the strongest evidence in the rung
  that the device reads the tag's slot number rather than deriving it. (b) *Poison*: every
  slot's retained copy is corrupted after its fill, and `q` changes for exactly the arms
  that have reuses (`w`, `wt`) while `control`, `wnone` and `wtnone` are unaffected.
- **Two hazards found by the gates, both now closed.** (1) The diag define was only passed
  when set, so a CMake cache went sticky and an env-unset rebuild kept compiling the counter
  atomic — the define is now always `ON`/`OFF`. (2) Diag and shipped objects share one native
  build dir: **wipe the native build dir before any timed run**, then verify `GLOBAL:0`, zero
  `ATOM`/`RED`, and per-function SASS identical to the frozen control before taking timings.
  This ritual ran before the timings below and its evidence is saved.

### The measurement — 6 arms, 100 paired rounds, one session

`--factorial` runs all six arms in one process against shared allocations, in a generated
cyclic rotation each round so no arm keeps a fixed position; every table below is emitted by
`tools/factorial_table.py` from the run log, never transcribed.

```bash
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench \
    --log-trace 24 --warmup 10 --iterations 100 --mode lsb-pair --factorial \
    --term-order locality > /tmp/factorial.log
python3 gpu/gkr_uniskip_bench/tools/factorial_table.py /tmp/factorial.log
```

**Use a round count that is a multiple of 6** — `--iterations 102` — so every arm starts an
equal number of rounds. The run below used 100, leaving starting positions at
16/16/17/17/17/17; the residual is ≤ 0.005 ms, below every contrast here, so the data stands
and the rule is for the next run.

| arm | regs | blocks/SM | `eval + finalize` locality | census |
| --- | --- | --- | --- | --- |
| `control` | 72 | 3 | **16.287** | **16.441** |
| `t` | 79 | 3 | 16.846 | 17.054 |
| `wt` | 80 | 3 | 17.173 | 17.252 |
| `wtnone` | 80 | 3 | 18.052 | 18.251 |
| `w` | 82 | **2** | 20.184 | 20.461 |
| `wnone` | 82 | **2** | 21.308 | 21.690 |

Paired contrasts, medians, **percentages of each contrast's own baseline** (the second term,
named in the row) — not of the control:

| contrast | locality | census | what it isolates |
| --- | --- | --- | --- |
| `t` − `control` | **+0.559** (+3.43 %) | +0.614 (+3.73 %) | the launch bound alone, 3 v 3 |
| `wt` − `control` | **+0.886** (+5.44 %) | +0.812 (+4.94 %) | the best window arm, 3 v 3 |
| `w` − `wnone` | **−1.124** (−5.28 %) | −1.229 (−5.67 %) | **the SCHEDULE alone** — identical kernel, 2 v 2 |
| `wtnone` − `t` | **+1.207** (+7.16 %) | +1.197 (+7.02 %) | **the MACHINERY alone**, 3 v 3 |
| `wt` − `wtnone` | **−0.879** (−4.87 %) | −0.998 (−5.47 %) | **the REMOVAL alone**, 3 v 3 |
| `w` − `control` | +3.897 (+23.92 %) | +4.021 (+24.46 %) | **2 v 3 — NOT occupancy-neutral** |
| `wnone` − `control` | +5.020 (+30.82 %) | +5.250 (+31.94 %) | **2 v 3 — NOT occupancy-neutral** |

**Every one of the nine emitted contrasts holds its sign in 100/100 rounds**, and the
decomposition closes: machinery + removal = +1.207 − 0.879 = **+0.328** against the directly
measured `wt` − `t` = **+0.327** (census: +1.197 − 0.998 = +0.198 = the measured +0.198).
Medians are not exactly additive; the per-round identity is exact by construction.

The factorial interaction `wt − w − t + control` is **−3.570 ms** (census −3.823). It is
reported for completeness and **must not be read as an effect size**: `w` and `wt` differ by
one block/SM as well as by the launch bound, so the term mixes occupancy classes.

### Verdict — MISS against the 14.61 ms bar, and the carrier is dead at this census

**No arm beats the control.** The control at **16.287** is still the fastest arm this crate
has measured; the best window arm `wt` is **17.173**, i.e. **+5.44 %** over the control and
**+17.5 %** over the 14.61 ms bar (16.287 is +11.5 %). On the halving-adjusted unit basis:
control 16.287 / 1.875 = **8.686 ms/unit**, `wt` 17.173 / 1.875 = **9.159**, against the
windowed reference's 7.79.

All three pre-registered prediction bands missed, all high, and `t` **inverted**:

| arm | pre-registered band | measured (locality) | verdict |
| --- | --- | --- | --- |
| `w` | 14.65–14.98 | **20.184** | MISS, high |
| `t` | 15.71–16.04 | **16.846** | MISS — a **slowdown** where −1.5…−3.5 % was predicted |
| `wt` | 14.1–14.8 | **17.173** | MISS, high |

Two separate findings, and they point opposite ways:

- **The register-window CARRIER is dead at this census.** At fixed 3-block occupancy the
  machinery costs **+1.207 ms** while the removal it enables refunds **−0.879 ms** — a
  carrier that eats **1.37×** what it delivers. Widening it does not help: 82 registers
  costs a block, and the 2-block arms are 24–31 % slower than the control.
- **The SCHEDULE mechanism is validated.** `w` − `wnone` is the schedule alone at identical
  kernel and identical occupancy: **−1.124 ms, 100/100 rounds**, and the ncu stream shows
  the removal as **exactly 47 chain executions per walk**. The plan is right; the medium it
  was carried in is wrong.

### Slopes for rung 2 — the calibration deliverable

Three slopes over the 47 removed productions, all emitted, **none of them "the" production
cost**:

| slope | locality | census | what it is |
| --- | --- | --- | --- |
| removal at 3 blocks `(wtnone − wt)/47` | **+18.70 µs** | +21.24 µs | **the shippable figure** — same carrier, control's occupancy |
| gross removal at 2 blocks `(wnone − w)/47` | +23.92 µs | +26.14 µs | the removal alone, but in a carrier that costs a block |
| net W = 4 `(control − w)/47` | −82.91 µs | −85.55 µs | carries the 3→2 block change with it |

The 2-block slope is **1.279×** the 3-block one (23.92 / 18.70). Stated with its
denominator both ways: 23.92 is **27.9 % above** 18.70, and 18.70 is **21.8 % below** 23.92.
Quoting the 2-block slope as the value of a production overstates it, because the carrier's
occupancy loss is inside it.

**What 18.70 µs does to the capture arithmetic.** The gap to the bar is
16.287 − 14.61 = **1.677 ms**. At 18.70 µs/production that is
1.677 / 0.01870 = **89.7 productions**, i.e. **38 % of the 234 removable** — against R2's
recorded 16.283 the same arithmetic gives 89.5. For comparison, the audit's ~19 % was
(16.283 − 15.0) / 29.6 µs = 43.3 = 18.5 % of 234, and the ratification's ~24 % was
1.673 / 29.6 µs = 56.5 = 24.2 %. The measured slope roughly **doubles the capture parity
requires**. Top-4 alone is 47 = **20.1 %** of the removable set and is worth 0.879 ms =
**52 %** of the gap — so even a **machinery-free** top-4 window does not reach the bar.

**The bar this sets for rung 2 (realization D).** D — prologue-publish → barrier → `ld.ca`
from a published bank — must cost **≪ the 1.207 ms** the register carrier paid, and it must
capture roughly twice what top-4 captures. Its machinery is paid in DRAM and barrier
currency rather than in hot-loop instructions on the binding pipe, which is precisely why it
remains the designed rung-2 arm after this result: R3 did not refute publication, it priced
the register medium and found it too expensive to carry the schedule.

**Tightened (2026-08-09, v3 R4).** The local-memory carrier now sets the incumbent budget at
**≪ 0.7–0.9 ms** of machinery — roughly two-thirds of the register carrier's 1.207 ms
(0.910 = 75 %, 0.743 = 62 % of it) — and, unlike this carrier, it wins: −1.45…−1.83 ms at
`hot16` with no synchronization at all. D must beat *that*, not this paragraph's 1.207 ms.
See *v3 R4 — the bar this sets for rung 2*.

### ncu — where the +1.207 ms sits, and what the −0.879 ms removes

Six captures, one per arm, one locked session, locality order, the profiling doc's Full
Picture block verbatim (never `--set full`), NVTX `gkr_uniskip_pass0/` and source import
under lineinfo, with a lineinfo↔shipped SASS parity gate passed **before** any capture:

```
target/profiling/ncu/20260809_151516_v3r3_control_locality.ncu-rep
target/profiling/ncu/20260809_151539_v3r3_t_locality.ncu-rep
target/profiling/ncu/20260809_151546_v3r3_w_locality.ncu-rep
target/profiling/ncu/20260809_151553_v3r3_wt_locality.ncu-rep
target/profiling/ncu/20260809_151600_v3r3_wnone_locality.ncu-rep
target/profiling/ncu/20260809_151607_v3r3_wtnone_locality.ncu-rep
```

Counts below are per-SASS-instruction "Instructions Executed" = warp-instructions, opcode
families (dot-suffixes and `U`-forms folded; `LDC`/`LDCU` kept split), 262,144 warps and 175
records per walk. Full derivation in the Task 4 record.

- **Machinery** (`wtnone` − `t`, 3 v 3): **+988,282,880 instructions (+5.23 %)** for
  **+1.207 ms (+7.16 %)**. The largest term is **`MOV`, +435,421,184** — the slot switch's
  register traffic, not the tag decode; then `LOP3` +186 M (nibble decode), `IMAD` +107 M,
  `BRA` +86 M, `ISETP` +68 M. Net *new* constant traffic is only **+1.77 per record**
  (`LDC` +243 M against `LDCU` −162 M). `short_scoreboard` 15.6 → 18.4 % and `mio_throttle`
  1.3 → 2.8 %: dependency-bound work, not throughput-bound work.
- **Removal** (`wt` − `wtnone`, 3 v 3): **−1,291,059,200 instructions (−6.50 %)** for
  **−0.879 ms (−4.87 %)**, and it is *exactly* 47 chain executions per walk —
  `SHFL` −73,924,608 = **282/walk = 47 × 6.0** to the instruction, `IMAD` and `VIMNMX`
  −295,698,432 each = 1128/walk = 47 × 24.0. This is the same 279-vs-326 fact the device
  counter proved, now visible in the executed stream.
- **`fmaheavy` is still the wall in all six arms**, within **0.3 points of SM SOL**
  everywhere (control 81.90 vs 81.62; `wtnone` 79.19 vs 79.10 = 0.09 pt). **R1's failure
  mode did not recur**: `lsu` is at or below the control's 18.28 % in every window arm, so
  the window's cost is register/dependency pressure, not a pipe migration.
- **The 2-block arms are starved, not contended.** Issue-slot utilization 64.1 → 50.6 %,
  eligible warps per scheduler (`smsp__warps_eligible.avg.per_cycle_active`) **1.85 → 0.94**,
  `math_pipe_throttle` 22.3 → 12.2 % and `not_selected` 22.8 → 12.4 % — fewer warps to
  select from, so the math pipe waits rather than queues.
- **The asymmetry is the rung's real result.** Machinery instructions cost **1.37×**
  proportional; removed chain instructions returned **0.75×** proportional. Removing 1.29 G
  dense, well-pipelined `fmaheavy` instructions to add 0.99 G dependent `MOV`/`LOP3`/`BRA`
  ones is a net **loss** of 0.33 ms even though the instruction count *falls*. Any future
  window must be judged on the character of the instructions it adds, not their count.

### The twiddle lever — CLOSED on priority, not by measurement

The `t` arm was supposed to test the audit's second lever. **It tested it in neither
direction.** Split by constant bank, the twiddle remat is *byte-identical* in all six arms:
the eight register-indexed bank-3 sites each execute **27,000,832** times in both `control`
and `t` = **824 per walk = 4.709 per record**, unchanged. (The audit's 5.03 is *total*
`LDC`/record and reproduces as 232,292,352 / 262,144 / 175 = **5.064**; the bank-3 subset is
5.051. Three different quantities.) All of `t`'s **+136,577,024** extra `LDC`s are **bank 0**
— kernel parameters and the descriptor — and they match its `LDCU` decrease exactly, to the
instruction: `__launch_bounds__` added or removed **zero** constant loads and moved that many
from the uniform datapath to the vector one.

**No replay amplification is visible in any counter the section list captures.** If each
lane-divergent constant load serialized into several passes, the stream would be ~9 % of
issue and a once-per-block 448 B smem table (distinct from R1's per-element staging) would be
worth reviving. It does not: `idc__request_cycles_active` / `idc__requests` =
49.852066 / 49.849729 = **1.00005**, one cache cycle per request; `idc__requests` − dynamic
`LDC` = **1,614,807,040, invariant across all six arms** whose `LDC` counts span 232 M–612 M;
issued == executed exactly. The stream is 824 / 72,256 = **1.14 % of warp-instructions**.

  **Corrected and re-grounded (2026-08-09, v3 R4's LDC rider).** The unhedged **"It does
  not"** above is right about these counters and wrong about the hardware. A direct
  microbenchmark measures lane-divergent `LDC` at **2.0 cycles per unique address**
  (31.98× throughput on a 32× address axis); `idc__request_cycles_active` / `idc__requests`
  is simply blind to it. Three consequences: (1) the fourth closure ground below — *"there
  is no replay amplification to recover"* — is **RETIRED**; (2) the conditional in this
  paragraph is therefore **live and unquantified** — 1.14 % bounds the stream's share of
  *instructions*, not of *cycles*, and once an `LDC` costs 2.0 cycles per unique address the
  448 B smem-table prize needs a cycle-level measurement nobody has taken; it is recorded as
  an open item and a rung-2 side experiment, **not** as a revived lever; (3) the closure
  **still stands on its other three grounds** — the audit round had already priced this
  stream indirectly and found it **not binding** (ADU 31.6 pt below the fmaheavy pipe, its
  remat-replay model predicting 50.0 % against 50.25 % measured), it competes for the same
  eight spare registers as the window (`w` prices that misallocation at +23.9 %), and R1
  measured the only actual removal of the indexed stream at **−15 %**. See *v3 R4 — the
  LDC-divergence rider*.

**The `S`/`WS` arms were NOT built, and the lever is closed on priority — not by
disproof.** The grounds: the prize is capped at **1.14 %** of the stream against the record's
−1.5…−3.5 % bound; it competes for the *same* eight spare registers as the window, whose
misallocation `w` prices at **+23.9 %**; R1 already measured the only removal of that
indexed stream via shared memory at **−15 %**; and there is no replay amplification to
recover. Reopening it needs a new argument, not a re-run.

### Open

- **`t` is +0.559 ms (+3.4 %) slower than the control while executing 54.3 M FEWER
  instructions**, and the only structural change is a uniform→vector constant datapath swap.
  Nothing in these captures explains it. Recorded open.
- **A window body that reaches 3 blocks without `__launch_bounds__` was never built** — the
  one untested carrier variant. `wt` gets to 80 registers by being told to; whether a
  narrower window body gets there on its own is unmeasured.
- **Everything here is one geometry, one census, one session** (`--log-trace 24`, the default
  add/sub-shaped census, sm_120). The between-session shift this session measured was
  ~0.1–0.2 % and concentrated in the 2-block arms; absolute medians above are from the 6-arm
  session only and must never be mixed with the earlier 5-arm table.

## v3 R4 — local-memory coset cache (`--cache-arm` / `--cache-factorial`): the produce-once budget line

R3 killed the register *carrier* and left the *schedule* validated. R4 carries that same
admission schedule in the cheapest medium the current kernel shape allows — a per-thread
local frame filled by a prologue — because here **producer = consumer thread**: no barrier,
no cross-warp traffic, no publish direction. It is the **budget line** the segmented rung
(realization D) has to beat, not a shipping candidate.

**Result: the cache pays, at the right width.** `hot16` (28 units, 145 of the 234 removable
productions) at 128 threads is **15.129 ms `eval + finalize` census / 14.836 locality** raw,
and **−1.453 ms census / −1.826 locality on `eval` against the in-session shipping control,
110/110 rounds**. Against the 14.61 ms windowed-candidate bar the honest answer is
**drift-sensitive**: this session's frozen shipping control missed its own sanity band, and
four defensible bridges straddle the bar (§*Verdict*). Everything below is one branch,
`rr/gkr_uniskip_bench`, tip `30e648e4`; the per-task reports and the oracle live under
`.agents/sdd/2026-08-09-v3-r4/` (uncommitted working-tree artifacts; referenced by name).

### Design — what was built

- **Admission is plan-time and source-global.** One canonical list off the live resolver
  stream (post-`force_self_products`, post-`apply_term_order`): references descending, cut at
  **refs ≥ 2**, ties **E4 before BF** then lower source id. Default census: **59 live sources
  (48 BF + 11 E4), 55 reused (44 + 11), 4 once-used BF**. Because a disposition belongs to a
  *source*, R3's two-operand tag problem cannot recur — a `PRODUCT`'s operands each fetch
  their own record.
- **Slots are assigned E4-first**, 4 units per E4 source as an aligned 32 B c-object-major
  span, 1 unit (8 B) per BF source — so every span is 16 B-aligned with zero padding.
- **One body, one frame, per block size.** The static frame is **736 B/thread**
  (`struct alignas(16) uniskip_coset_cache`, `UNISKIP_COSET_FRAME_UNITS = 92` with a
  `static_assert` on both sides of the ABI), sized at `C_max` for *every* arm, so arms differ
  only in uploaded records + prologue table and never in codegen. ptxas: **STACK 736, LOCAL 0,
  zero spill** on all three cached bodies.
- **Wire: the record's existing `cache_slot` u8** (`0xff` = recompute, else the source's first
  unit index). No record widening, no side descriptor, no per-record tag decode.
- **Prologue = store-once through the *unchanged* resolver**, E4 class first then BF, one
  walking loop with a warp-uniform class branch. The E4 resolver builds `c[0]`/`c[1]` only
  after all four limbs, so the store is **2 × `STL.128` immediately after resolve returns**,
  never per-limb. Static local forms measured in SASS: `LDL.64` ×6, `LDL.128` ×8, `STL.64` ×1,
  `STL.128` ×2 — no 4 × `LDL.64` on an E4 span.
- **Consume** = `LDL.64` (BF) / 2 × `LDL.128` (E4 span) plus the unchanged `h[2]` load; every
  admitted source's H is therefore loaded once in the prologue **and** reread at each
  reference (+8C B/thread, pinned in the gates).
- **Kernels**: `cached@256` **75 regs / 3 blocks/SM**; `cached@128_lb` **72 / 7**
  (`__launch_bounds__(128, 7)`, the 128 measurement arm); `cached@128` unbounded **75 / 6** —
  the occupancy step, kept as the pricing arm.

Arm menu and its oracle (`expected-counts.md`, controller-derived out-of-tree before any
implementation and reproduced first try by the planner, both term orders):

| arm | admitted | C (units / B) | Rc | chains | stores | loads | removals |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `cache0` | 0 | 0 / 0 | 0 | 326 | 0 | 0 | 0 |
| `hot4` | 4 bf | **4 / 32** | 51 | 279 | 4 | 51 | **47** |
| `hot16` | 12 bf + 4 e4 | **28 / 224** | 173 | 181 | 20 | 133 | **145** |
| `e4top2` | 2 e4 | 8 / 64 | 56 | 278 | 4 | 28 | 48 |
| `e4rich` | 11 e4 | 44 / 352 | 136 | 234 | 22 | 68 | 92 |
| `allrepeat` | 44 bf + 11 e4 | **88 / 704** | 322 | 92 | 66 | 254 | **234** |
| `all59` | 48 bf + 11 e4 | **92 / 736** | 326 | 92 | 70 | 258 | **234** |

`hot4` is R3's window with a different carrier — same four sources, same 13/13/13/12
references, same 47 removals — which is what makes the two rungs directly comparable.
`all59` buys **zero** extra removals over `allrepeat` for +4 stores, +4 loads and +32 B: the
once-used-caching waste, priced below. `e4top2` is the family-stop lane (RR ruling 2); it
replaced an all-11-E4 stop arm that could never satisfy its own L1-residency precondition.

Commits: `aa413e51` + `8b4943d0` (admission, slots, wire, always-on validator, CLI),
`d0301375` + `2d06d34b` (`control128`), `b1a988af` + `fc4c3689` (cached kernels, the
launch-bounds sibling, `control128_lb`, `e4top2`), `0807f5ed` + `a461e8a5` + `c0b43fd5` +
`d6b8aebc` (gates), `c22665cf` + `cc54d0b0` + `30e648e4` (factorial runner + emitter).

### Gates — all pass

**Frozen SASS 9/9 byte-identical** through every edit of the rung, including the LDC rider's
TUs and a `-lineinfo` rebuild: **5104, 5104, 5592, 5600** (the four R3 pair functions),
**5048** (`control128`), **5064** (`control128_lb`), **6024** (`cached@256`), **5992**
(`cached@128` bounded), **5976** (`cached@128` unbounded); per-fatbin, scoped by TU/function
name, never by archive ordinal. **Occupancy gate held**: 75 regs / 3 blocks at 256 = the
control's 3; 72 / 7 at 128 = `control128`'s 7. The 128 axis **stepped** (unbounded 75 regs →
6 blocks) and was corrected with the `__launch_bounds__(128, 7)` sibling rather than measured
around — both bodies ship, `--no-cache-launch-bounds` prices the bound and
`--control-launch-bounds` supplies the bound-matched no-cache baseline. **Parity 112/112**
(7 cached arms × 2 block sizes × 2 term orders × 2 `eq` forms × 2 censuses) plus **28/28**
E4 self-product cells and **14/14** CPU-oracle cells; both 128 launch-bounds sibling pairs
bit-identical. **Dynamic counts exact**: chain executions per warp-program walk 326 / 279 /
181 / 92 / 92 / 234 / 278 for `cache0` / `hot4` / `hot16` / `allrepeat` / `all59` / `e4rich` /
`e4top2`, direct `smsp__inst_executed_op_local_{ld,st}` equal to the oracle on all seven arms
with `pred_off_all = 0`, local sectors equal to the width identity on every arm, and the
prologue H delta equal to **8C B/thread to the byte**. Mutations discriminate: retarget
through the unchecked upload path diverges `q` on the **three** arms it was run against;
poison after the prologue diverges on cached arms only, leaving `cache0` and both controls
untouched. R3 regression green throughout (matrix 40/40, blocks 8/8, six `--pair-arm` lanes
32/32); 77 lib tests.

**Process note.** The 3A review caught a **Critical** in the factorial runner: the pass config
was not forced to the 128-thread row tile, so every lane's grid covered half the rows — and
the runner's own "grid doubling" self-check was ratio-only and survived it. It was fixed and
then verified three ways — Opus re-review (all medians recomputed from the raw log), an
independent codex full verification, and a focused codex audit of the grid math at the
minimum legal `log_rows` — and **every functional number produced before the fix was
discarded, not reconciled**. The pre-3B evidence log was regenerated from the committed
binary under the lock.

### The measurement — 11 lanes, 110 paired rounds per order, one session

```bash
.agents/bin/with_gpu_lock.sh bash -c '
  B=target/release/gpu_gkr_uniskip_bench
  for order in census locality; do
    $B --log-trace 24 --warmup 11 --iterations 110 --mode lsb-pair --cache-factorial \
       --term-order $order
  done' > /tmp/r4.log
python3 gpu/gkr_uniskip_bench/tools/r4_table.py /tmp/r4.log
```

Eleven lanes in one process against shared allocations in a generated cyclic rotation;
**110 rounds per term order** (a multiple of 11), 1210 samples per order, both orders in one
locked session with **zero builds between the shipped rebuild and the last timing**.

**Provenance, because these two things differ.** Every **contrast** table below is emitted by
`tools/r4_table.py` from the run log, never transcribed — medians, IQRs, on-sign counts,
baselines and occupancy labels alike. The **`eval + finalize` per-lane medians** and the
sanity-gate row are *not* emitter output: the emitter summarizes `eval` and `finalize`
separately on purpose (the 128 lanes reduce twice the partials), so the combined figures are
computed in the 3B report as medians of the per-round sums over the same log. The two are
never mixed inside one table here, and each is labelled by measure.

**Pre-registered before the run**: an arm loses iff its paired per-round contrast has
median > 0 with **≥ 99/110 on-sign** — spec §6's 90 % rule restated at the 11-lane round
count. (The spec's "≥ 90/100" wording assumed 10 arms; the amendment was recorded
pre-dispatch and needed no code change, since the emitter never hardcoded a round count.)

**The sanity gate FAILED, and is reported as a failure.** The frozen shipping control fell
outside the R2 band in **both** orders:

| order | `control@256` `eval + finalize` | band | miss |
| --- | --- | --- | --- |
| census | **16.545** | 16.28–16.51 | +0.035 |
| locality | **16.624** | 16.28–16.51 | +0.114 |

and the historical `locality < census` relation for `control@256` **inverted**. Per the
brief the implementer stopped without interpreting; an authorized ABA discriminator session
followed (§*Verdict*, drift paragraph).

Per-lane medians, `eval + finalize` (ms):

| lane | regs, blocks/SM | census | locality |
| --- | --- | --- | --- |
| `control@256` | 72, 3 | 16.545 | 16.624 |
| `cache0@256` | 75, 3 | 17.455 | 17.353 |
| `hot4@256` | 75, 3 | 16.606 | 16.515 |
| `hot16@256` | 75, 3 | **15.178** | **14.938** |
| `allrepeat@256` | 75, 3 | 20.092 | 16.828 |
| `control@128` | 72, 7 | 16.262 | 16.467 |
| `control_lb@128` | 72, 7 | 16.216 | 16.390 |
| `cache0@128` | 72, 7 | 16.952 | 17.063 |
| `hot4@128` | 72, 7 | 16.186 | 16.198 |
| `hot16@128` | 72, 7 | **15.129** | **14.836** |
| `allrepeat@128` | 72, 7 | 24.416 | 18.697 |

Paired contrasts on `eval` (medians; each row's percentage is of its own named baseline;
`eval` and `finalize` are summarized separately because the 128 lanes reduce twice the
partials):

| contrast | census | on-sign | locality | on-sign |
| --- | --- | --- | --- | --- |
| `cache0@256` − `control@256` | **+0.910** (+5.51 %) | 110/110 | **+0.768** (+4.63 %) | 110/110 |
| `hot4@256` − `cache0@256` | −0.855 | 110/110 | −0.875 | 110/110 |
| `hot16@256` − `cache0@256` | **−2.285** | 110/110 | **−2.464** | 110/110 |
| `allrepeat@256` − `cache0@256` | **+2.631** | 110/110 | −0.523 | 110/110 |
| `hot4@256` − `control@256` | **+0.072** | **96/110** | −0.107 | 108/110 |
| `hot16@256` − `control@256` | −1.387 | 110/110 | −1.694 | 110/110 |
| `cache0@128` − `control_lb@128` | **+0.743** (+4.60 %) | 110/110 | **+0.665** (+4.07 %) | 110/110 |
| `hot4@128` − `cache0@128` | −0.777 | 110/110 | −0.889 | 110/110 |
| `hot16@128` − `cache0@128` | **−1.824** | 110/110 | **−2.230** | 110/110 |
| `allrepeat@128` − `cache0@128` | **+7.461** | 110/110 | +1.636 | 110/110 |
| `control_lb@128` − `control@128` | −0.052 | **89/110** | −0.062 | 109/110 |
| `hot4@128` − `control@256` | −0.419 | 110/110 | −0.483 | 110/110 |
| `hot16@128` − `control@256` | **−1.453** | 110/110 | **−1.826** | 110/110 |
| `allrepeat@128` − `control@256` | **+7.832** | 110/110 | +2.043 | 110/110 |

The three cross-size rows are the decision contrasts and are **7 v 3 blocks/SM — not
occupancy-neutral**; on `eval + finalize`, where the doubled finalize is load-bearing, they
are `hot4@128` **−0.389 / −0.454**, `hot16@128` **−1.422 / −1.795**, `allrepeat@128`
**+7.863 / +2.072** (census / locality, 110/110 each).

Three contrasts fall **below** the pre-registered 99/110 threshold and are reported as
measured, with the rule unadjusted: `hot4@256 − control@256` at 96/110 (a **wash**, not a
loss — the distinction is what kept the family stop-lane from firing, below),
`control_lb@128 − control@128` at 89/110, and `hot4@128 − control_lb@128` at 71/110 on the
census run — the same story as the first, within its size: −0.023 ms at 71/110 census,
−0.228 at 110/110 locality.

### Verdict — three yardsticks, three different answers

**1. Against the 14.61 ms windowed-candidate bar: drift-sensitive / inconclusive.** Raw
`hot16@128` is **15.129** (census) / **14.836** (locality) on `eval + finalize` — **above the
bar in both orders**; only bridging onto the recorded R2 level brings any construction under
it. That bridge is the honest thing to do — the session's own frozen control missed the R2
band — but it must be stated as what it is. Two constructions (additive
`R2_control + (hot16 − base)`, and ratio-normalized `R2_control × hot16/base`) over two bases:

| order | base | additive | normalized |
| --- | --- | --- | --- |
| census | `control@256` | 14.863 | 14.886 |
| census | `control_lb@128` | **15.129** | 15.126 |
| locality | `control@256` | **14.357** | 14.395 |
| locality | `control_lb@128` | 14.595 | 14.604 |

The four constructions span **14.357–15.129 and the 14.61 bar sits inside that span**. Per the
framing fixed before the analysis, a straddle is reported as **drift-sensitive**; the whole
span is the honest uncertainty and **must not be collapsed by choosing a base**.

**The straddle splits by term order, not by base**, which is the informative part: all four
census constructions (14.863–15.129) are **above** the bar and all four locality constructions
(14.357–14.604) are **below** it, whichever base or normalization is used. **That split is a
real term-order effect, and it is a different object from the raw pair's.** The bridge is
built from R2's *recorded per-order levels* and this session's *standalone* anchors, where the
ordering is the stable historical one — locality faster in all six standalone runs
(−0.082 / −0.054 / −0.418), matching R2 and R3. The factorial-context caveat below applies to
the raw 15.129-vs-14.836 pair, which was measured *inside* the rotation; it does not travel to
the bridged numbers. What remains genuinely open is which order a shipping pass would run in,
not whether the order difference is real. Note also the terminology collision with spec §6,
which reserved *drift band* for the numeric interval 14.36–14.61; **drift-sensitive** here
means the bridge span straddles the bar, and applying §6's original three-state test literally
to the raw candidate returns **MISS in both orders** (see the spec amendment).

**2. Against the in-session shipping control: a clear win.** `hot16@128` − `control@256` =
**−1.453 ms census / −1.826 locality on `eval`, 110/110 rounds** (−1.422 / −1.795 on
`eval + finalize`). Both legs are the same session, the same rotation, the same allocations;
this contrast owes nothing to the band.

**3. Against shipping production: the margin widens.** The audit round priced shipping
layer-0 rounds 0–3 at **24.11 ms** (green nsys, `av_gkr_compiler`, add_sub, 2^24, not
windowed) and the R2 pass at **−32.5 %**. At `hot16@128`'s raw ≈ 14.8–15.1 ms the same
comparison extends to ≈ **−37…−38 %**. This one is cross-session by construction and inherits
every caveat of the pricing report (single-sample profile, synthetic census mix, fold-boundary
accounting) plus this session's own (below).

**Sanity and drift — method, because the number matters less than the procedure.** The band
miss is a **real session effect, not a rotation artifact**, and the discriminator says so
three ways. (i) A standalone `control@256` in a fresh locked session reproduces the miss on
its own: **16.690 census / 16.608 locality**, +1.4 % / +2.0 % over R2 — outside the band with
no factorial anywhere near it. (ii) The rotation does **not** inflate the controls: factorial
lane minus *time-interpolated* flanking anchors is **−0.195 / −0.223 ms** at census (the
controls run *faster* in rotation) and within ±0.02 ms at locality, and the frozen 3B run
reproduces that pattern to within 0.06 ms. (iii) Telemetry flags the cause class: `SwPowerCap`
active in **5 of 28** inter-phase samples, power peaking at **561 W**, no thermal or
hardware-slowdown bits, memory clock pinned, P0 throughout — and the session **warms
monotonically** (on all six anchor runs the second standalone block is **+0.074…+0.189 ms
slower** than the first),
which is exactly why the anchors are interpolated rather than averaged.

The census/locality **inversion is a property of the factorial context, not of the program**:
it appears in both factorial sessions (`control@256` +0.079 and +0.070) and in **none** of the
six standalone runs, which all show the historical `locality < census` (−0.082 / −0.054 /
−0.418). Its cause is unmeasured. **Never read a term-order difference taken inside a
factorial as a program property.** Two rules for future rungs follow: sample `nvidia-smi`
event reasons around every timed session, and put an **in-session anchor** in any run whose
conclusion is a cross-history absolute.

### Economics — the budget lines rung 2 consumes

The ledger is **linear in removals with a fixed intercept**, and it explains every arm.

- **Machinery intercept** (`cache0` − control, the frame + prologue walk + slot addressing
  with *zero* removals): **+0.910 ms @256 / +0.743 ms @128** timed, 110/110 both. Under ncu's
  locked clocks the same quantity reads **+1.051 / +0.676** — a different scale (absolutes
  there run ~6 % high), never to be mixed with the timed one. The 128 ncu figure is also not
  bound-to-bound (`cache0@128` bounded − `control@128` unbounded); the timed +0.743 is.
- **Removal slope, by block size.** Under ncu: **−21…−26 µs per removed production @256**
  (`hot4` −25.7, `hot16` −20.8), **−17…−23 µs @128** (`hot4` −22.5, `hot16` −17.1). Against
  each size's own intercept that is a breakeven of **≈ 41–50 removals @256** and **≈ 30–40
  @128**. The timed machinery-corrected slopes are the same order of magnitude, not the same
  number — `hot4@256` −18.20 (census) / −18.63 (locality) µs, `hot16@256` −15.76 / −16.99 —
  and all four **sit just under R3's 18.70 µs** removal slope at 3 blocks (15.8–18.6):
  **this carrier buys a production back at roughly the price the register carrier did, and
  pays 62–75 % of the register carrier's 1.207 ms for the privilege.**
- **`hot4` brings 47 removals = exactly the breakeven.** It buys back its own machinery and
  nothing else. That *is* the +0.072 ms / 96/110 wash at 256 — arithmetic, not noise.
- **`hot16` brings 145 ≈ 3.1× the intercept**, so two thirds of the refund is profit: under
  ncu, −3.011 ms against a −1.051 ms bill = net **−1.96 ms ≈ 1.9× its machinery**.
- **A removed production is worth 105–110 executed instructions per warp, flat from C = 4 to
  C = 92.** The instruction side of the ledger is perfectly linear; nothing about the removal
  changes with width. What changes is only the ratio to the fixed intercept — and, past
  `hot16`, which resource the removal is removed *from* (next section).

  **Superseded in part (2026-08-10, v3 R5 — the instruction leg holds, the *price* does
  not).** This bullet's flatness claim is about *instructions*, and it survives: R5 measures
  it at the margin, where `k24@128` executes **1,478 fewer instructions per warp** than
  `hot16@128` for its 16 extra removals = **92.4 net instructions per marginal removal**
  (105–110 is the *gross* slope against `cache0`; the marginal is lower because the 8 added
  sources pay their own +8 `STL`, +24 `LDL`, +16 `LDG` inside the same step). What does not
  survive is the **blended** reading the R5 spec §1 built on this bullet — instructions *and*
  the µs slopes as one flat marginal value. At this section's ncu-clock-locked −17…−23 µs @128
  those 16 removals model **−0.27…−0.37 ms**; at R5's own *timed* @128 machinery-corrected
  slope (−12.97 census / −15.26 locality µs/removal) they model **−0.21…−0.24 ms**. They
  measured **+0.140 ms locality / +0.188 census**, 100/100 both — wrong in sign either way.
  The bite point is between **C = 28 and C = 36**, not near `allrepeat`. See *v3 R5*.

### Residency — no arm is L1-resident, and the winner is an L2 cache

**The spec's §6 residency predicate does not discriminate.** Leg (a) — local-load L1 hit
≥ 95 % — is failed by **every one of the 11 arm × size cells**, best non-`allrepeat`-locality
reading **2.41 %** (`hot4@256`), most below 0.1 %. Leg (b)'s known contamination never flips a
verdict. The predicate returns *NOT L1-resident* for the −2.3 ms winner and the +7.5 ms loser
alike, so **"is it L1-resident" is not the gate this family needs**.

L1 is not merely exceeded — it is **structurally unavailable as the medium**. `hot4` touches
24 KiB/SM @256×3 and 28 KiB @128×7, fits the 128 KiB L1 five times over, and still hits at
2.41 % / 0.09 %. The walk streams **684 M global sectors ≈ 21.9 GB** through the same L1
between a slot's fill and its use; capacity against the *frame* is irrelevant next to capacity
against the *stream*. The only lever that has ever moved this number is shortening the reuse
distance (§*Term order*), never shrinking the footprint.

**Order-scoped (2026-08-10, v3 R5).** This paragraph's conclusion does not hold for the winner
in both term orders. R5 captured `hot16@128` under both, on the same body, the same admitted
set and the same instruction stream: local-load L1 hit is **0.010 % in census and 47.871 % in
locality**. So "structurally unavailable" describes reuse distance *in census order*, not the
medium — and the lever the last sentence names is exactly the one that moves it. (The
elsewhere-cited locality readings in this section, e.g. `allrepeat`'s, are unaffected; so is
the capacity finding below.) See *v3 R5*.

**What `hot16` actually is: an L2-resident cache**, and that is the headline of the rung —
but the two block sizes must be quoted separately, because **the candidate is the 128 one and
its L2 hit rate falls**:

| `hot16` | device-wide local set | % of 128 MiB L2 | local sectors L2-served | L2 hit % on L1TEX reads | DRAM SOL % |
| --- | --- | --- | --- | --- | --- |
| @256×3 | 32.3 MB | **24 %** | **≥ 84 %** (≤ 67.0 M of 421.5 M reach DRAM, +2.1 GB) | 69.20 → **75.40 (rises)** | 37.50 |
| @128×7 (the candidate) | 37.7 MB | **28 %** | **≥ 65 %** (≤ 146.9 M of 421.5 M reach DRAM) | 71.26 → **68.99 (falls)** | 50.40 |

Both are floors: part of each DRAM delta is the arm's own prologue global re-reads (bound
58.7 M sectors), which the device cannot separate from local traffic beyond L1. So the honest
statement is that `hot16` is **L2-served, not L1-served, at both sizes** — comfortably at 256,
and at 128 with the L2 hit rate already **2.3 pt down** and DRAM SOL at half the machine while
it still wins by −1.45…−1.83 ms. The 128 candidate is closer to the wall than the 256 arm is,
and that is the number rung 2 inherits.

**Order-scoped (2026-08-10, v3 R5) — the capacity half survives, the residency half gains a
qualifier.** Both rows above are census captures. R5 re-captured `hot16@128` in both orders:
the **L2-resident framing is the durable part** — 28.1 % of L2 in either order, and it is the
L2/DRAM counters that price the knee one step later — but **"not L1-served" is census-order
only**. In `locality` the frame is roughly half L1-served (47.871 % local-load L1 hit), so the
sentence to carry forward is "`hot16` is L2-served, not L1-served, **in census order**". See
*v3 R5*.

**The capacity wall is the L2 occupancy fraction, not the L1 one:**

| arm | device-wide local set | % of L2 | L2 hit % @256 | L2 hit % @128 | DRAM SOL % | verdict |
| --- | --- | --- | --- | --- | --- | --- |
| `hot4` | 4.6 / 5.4 MB | 3 / 4 % | 69.20 → 74.17 | 71.26 → 75.44 | 22.28 / 23.42 | coexists, wins nothing |
| `hot16` | **32.3 / 37.7 MB** | **24 / 28 %** | 69.20 → **75.40** | 71.26 → **68.99** | 37.50 / 50.40 | **the winner** |
| `allrepeat` | 101.6 / 118.6 MB | 76 / **88 %** | 69.20 → 56.53 | 71.26 → 44.43 | **84.46 / 85.13** | collapses |
| `all59` | 106.3 / 124.0 MB | 79 / **92 %** | 69.20 → 56.02 | 71.26 → 42.91 | 83.53 / 85.75 | collapses harder |

(Every paired cell is `@256×3 / @128×7`; `allrepeat@128` is its census capture.) The pipe
signature crosses at the same place: `math_pipe_throttle` 1.735 → 1.364 (`hot4`) → 1.149
(`hot16`) → **0.449** (`allrepeat`) while `long_scoreboard` 1.267 → 1.523 → 2.189 → **7.712**.
Through `hot16` the kernel is *still* fmaheavy-issue-limited (72.8 % cycles active), so each
removed production comes off the binding resource; at `allrepeat` the arm has flipped
**DRAM-bound at 84.5 % SOL** and further removals are free instructions on a pipe that is no
longer the bottleneck. **Never quote "`hot16` is not L1-resident" without this half of the
finding** — alone it is misleading. (The `allrepeat`/`all59` rows are census captures; in
locality order at 256 the same `allrepeat` body is **faster than `cache0` by −0.523 ms** — see
§*Term order*. The capacity verdict is a per-term-order statement, not a property of the
admitted set alone.)

The sizing rule a future admission policy inherits is therefore the **L2 budget** (share of
128 MiB across 188 SMs), and the cliff is where DRAM SOL crosses ~80 %.

### Term order and prologue order — one mechanism, priced twice

**`allrepeat@128` moves 5.7 ms on term order alone**, with an **identical instruction stream**
(12.856 G, 254 `LDL` + 66 `STL` per warp) and identical request counts (168,820,736 local-load
requests). The only counter that moves at the source is the L1 hit rate:

| | census | locality | delta |
| --- | --- | --- | --- |
| local-load L1 hit | 0.010 % | **26.918 %** | +181.7 M sectors |
| DRAM read sectors | 854,131,072 | 611,587,352 | **−242.5 M (−7.76 GB)** |
| DRAM SOL | 85.13 % | 85.41 % | both saturated |
| duration | 24.459 ms | 18.704 ms | **−5.755 ms** |

This is **reuse distance, not eviction interleave**. Each admitted source is referenced
**4.0× on average** per walk (the admitted range runs from 13 references down to the cut at
2), and in census order the consumers of one source are scattered across the record stream,
so megabytes pass through a 128 KiB L1 between two loads of the same slot and essentially
every load misses. The locality permutation clusters records reading the same sources, so
consecutive loads land inside one L1 lifetime. The arm is DRAM-saturated either way, so each
sector L1 absorbs is a sector DRAM does not fetch: at the arm's measured **1.359 GB/ms**,
7.76 GB is **5.71 ms** against the 5.755 ms measured — the swing is accounted for with nothing
left over. It is an `allrepeat`-class phenomenon by construction: it needs an arm whose local
traffic is DRAM-bound in the first place (`hot16@128` sits at 50.4 % DRAM SOL and shows
nothing like it).

**The same mechanism reaches into the arm ordering at 256.** `allrepeat@256 − cache0@256` is
**+2.631 ms in census but −0.523 ms in locality**, 110/110 both — in locality order the
capacity arm *beats* the machinery-only arm, and its net against the control shrinks from
+3.547 to +0.194 (still a loss against the control in both orders). **Only the 256 cell
flips**: `allrepeat@128 − cache0@128` stays a loss in both orders, +7.461 census and +1.636
locality. So the capacity verdict is three losses and one win across the four
arm×order cells, and the size that flips is the one with the smaller footprint per SM. Only
the census capture exists for `allrepeat@256` under ncu, so the flip has timing evidence and
no counter evidence.

**The prologue's class order is the same mechanism at the other end of the fill, and
`e4first` stays pinned.** BF-first loses everywhere: timed ABBA (33 rounds, positions 1 and 4
agreeing to ≤ 0.014 ms, so block drift is negligible) gives **+2.087** (`allrepeat@256`),
**+2.043** (`all59@256`), **+1.514** (`allrepeat@128`), **+1.414** (`all59@128`); ncu brackets
it at +2.63 / +2.29 @256 and explains it — producing the E4 units first leaves the 32 B spans,
4× the bytes per unit, coldest at walk entry: DRAM reads **+124.2 M / +110.7 M sectors** and
L2 hit 56.5 → 49.0 / 56.0 → 48.7.

**The waste case is priced.** `all59` − `allrepeat` = **+0.640 ms @256 / +0.700 @128** timed
(+0.380 / +0.810 under ncu) for the oracle's +4 stores, +4 loads, +32 B and **zero** extra
removals. Caching a once-used source is not free — it is measurably negative — which is the
`refs ≥ 2` admission cut, validated.

### The LDC-divergence rider — the lore is true, and R3's counters could not see it

Spec §8's standalone probe (`src/bin/uniskip_ldc_divergence.rs`, one instruction stream for
all K — the address count is runtime data behind a mask — with a live sink and a true
loop-carried dependency in the latency arm):

| stride | latency K=1 → K=32 (cyc/dependent load) | ratio (baseline-corrected) | throughput cyc/warp-`LDC` K=1 → K=32 | ratio |
| --- | --- | --- | --- | --- |
| 4 B | 35.01 → 376.00 | 10.74× (11.59×) | 2.001 → 64.001 | **31.98×** |
| 64 B | 35.01 → 376.10 | 10.74× (11.60×) | 2.001 → 64.005 | **31.99×** |
| 128 B | 35.01 → 3416.02 | 97.58× (106.03×) | 2.001 → 104.943 | **52.45×** |

**Lane-divergent constant loads serialize, at exactly 2.0 cycles per UNIQUE ADDRESS** —
per *address*, not per line: 32 addresses packed into a single 128 B line (4 B stride,
**31.98×**) cost the same as 32 addresses each in their own 64 B line (64 B stride,
**31.99×**). Single-warp latency grows by a **constant +11.0 cycles per extra address** — a
linear increment, but only **10.74×** across a 32× address axis, which is what says the
replays *pipeline* rather than serializing the dependent load end to end. The 128 B-stride
row is a separate, larger cliff (**52.45×** throughput, 106× latency): at K = 32 that sweep
spans 4 KB, and per-SM constant-cache overflow is the natural hypothesis — **the probe
records the cliff, it does not establish its cause.**

**Reconciliation with R3, which said something stronger than it could support.** R3 wrote an
unhedged **"It does not"** against exactly this mechanism, on
`idc__request_cycles_active / idc__requests = 1.00005`, and then listed *"there is no replay
amplification to recover"* as one of four grounds for closing the twiddle lever. The rider
settles it in three parts:

- **That ground is retired.** The serialization is real; the `idc__*` counter set is blind to
  it. R3's *measurement* stands — those counters do read 1.00005 — but it never licensed the
  hardware claim. (The audit round, by contrast, *had* seen the replays indirectly: its ADU
  resolution modelled this same lane-indexed remat stream and predicted the pipe at 50.0 %
  against 50.25 % measured. What the rider adds is the per-address price, not the existence.)
- **R3's conditional is now live, and unquantified.** It read: *if* each divergent constant
  load serialized into several passes, a once-per-block 448 B smem table would be worth
  reviving. It does serialize — but **1.14 % bounds the stream's share of instructions, not
  of cycles**, and at 2.0 cycles per unique address the two are no longer interchangeable.
  Nobody has taken the cycle-level measurement. It is recorded below as an open item and a
  rung-2 side experiment, **not** as a reopened lever.
- **The closure still holds on its other three grounds**: not binding (audit round: ADU
  31.6 pt below the fmaheavy pipe), it competes for the same eight spare registers as the
  window (`w` prices that misallocation at +23.9 %), and R1 already measured the only actual
  removal of the indexed stream — shared-memory staging — at **−15 %**.

The lesson imported from the red/blue worktrees — never put a lane-indexed constant load in a
hot path — now has a number behind it.

### The bar this sets for rung 2 (realization D / segmented carrier)

- **Machinery budget: ≪ 0.7–0.9 ms.** That is this rung's measured intercept and it replaces
  R3's ≪ 1.207 ms as the incumbent. D must land its prologue-publish + barrier + `ld.ca`
  machinery under it *at equal capture*, or it loses to a cache that needs no synchronization
  at all.
- **Where D can beat this: removals this carrier cannot reach.** The per-thread frame caps at
  C = 92 units / 234 removals on this census and **every thread pays its own prologue and its
  own frame** — there is no cross-warp sharing. D's upside is exactly the removals beyond that
  cap plus the amortization of one production across consumers.
- **D's risk currency is L2/DRAM traffic, and `allrepeat` prices it.** Saturating L2 is not a
  gentle degradation: +7.461 ms against `cache0@128`, L2 hit collapsing to 42–56 %, the arm
  flipping DRAM-bound. The publish direction must therefore stay inside the L2 headroom
  `hot16` leaves — **~76 % of L2 unused at C = 28 @256×3, ~72 % @128×7** — and be counted per
  direction, published bytes and read bytes separately, as the audit round already required.
  The 128 candidate is the one rung 2 must beat and it is the one with less headroom: its L2
  hit rate is already falling (71.26 → 68.99) at 28 % occupancy.
- **Term order is a first-class knob for D**, not a tie-break: the 5.755 ms swing above is
  what reuse distance is worth once local traffic is DRAM-bound.

### Open

- **`control_lb@128` was never captured under ncu**, so the 128 machinery intercept is
  bound-to-bound only in the timed data, not in the counter evidence.
- **The conditional mini-factorial machinery was never built** — correctly: spec §6's stop
  lane requires `hot4` to *lose* at both block sizes under the ≥ 99/110 rule, and it **washed**
  at 256 (96/110) and **did not lose at either size** (at 128 it is −0.023 ms at 71/110
  census, a wash, and −0.228 at 110/110 locality). The condition was evaluated, not skipped.
- **`e4top2` was never timed.** It is built, its literals are verified on the binary, and it
  is the only clean BF-vs-E4 carrier comparison at equal removals — 48 removals at 64 B
  against `hot4`'s 47 at 32 B.
- **The factorial-context census/locality inversion has no measured cause.**
- **The twiddle stream's cost in CYCLES is unmeasured**, and R3's conditional is now live.
  Its 1.14 %-of-stream bound is an *instruction* share; at 2.0 cycles per unique address the
  cycle share can be larger, and R3's own "if it serializes, a once-per-block 448 B smem table
  would be worth reviving" is no longer counterfactual. This is a rung-2 **side experiment**
  (measure the bank-3 stream's cycles, then decide), not a reopened lever — the other three
  closure grounds are untouched.
- **Every ncu figure is a single NVTX-wrapped launch.** Instruction and sector counts are
  deterministic and close exactly against the oracle; the *rate* metrics (SOL, hit rates,
  stall ratios) carry one sample's uncertainty, unlike the 110-round timed medians.
- **The R2 band is no longer usable as a cross-session gate without telemetry control.** Do
  not delete it — it caught a real 1.4–2.0 % session effect on its first use. Annotate it: a
  band miss now demands a standalone anchor and an event-reason sample before it is read as a
  regression.

### Branch state

The LDC rider (`native/uniskip_ldc_probe.cu`, `src/ldc_probe.rs`,
`src/bin/uniskip_ldc_divergence.rs`, CMake/lib wiring) and this record are **parked as
patches** under `.agents/sdd/2026-08-09-v3-r4/patches/`, not committed: the signing agent was
down and `commit.gpgsign` is on. Tip is `30e648e4`; the rider's files are live in the working
tree; nothing is pushed.

## v3 R5 — admission frontier (hotK sweep)

R4 priced the two ends of the local-memory cache and left the middle unmeasured: `hot16`
(C = 28 units) wins by **−1.422 census / −1.795 locality on `eval + finalize`** against the
shipping control, `allrepeat` (C = 88) collapses, and nobody had looked in between. R5 looks —
six canonical prefix points from C = 36 to C = 69, rotated in one process against the
incumbent, the machinery-only lane and both no-cache baselines. Every timed figure in this
section is `eval + finalize`, the bar quantity, unless it says otherwise.

**Result: there is nothing in the middle to find.** `hot16@128` is the frontier optimum in
**both** term orders, and the next lane in the sweep — `k24@128`, eight sources and eight units
further along the list at C = 36 — already loses by **+0.140 ms locality / +0.188 census**,
100/100 rounds. The knee is between C = 28 and C = 36 — far below `allrepeat` — and it is an
**L2** knee in both orders. Against the 14.61 ms
windowed-candidate bar the raw in-rotation medians are over (14.717 locality / 15.120 census);
the spec's anchor mini-session **upgrades the locality bar claim** (both bridge forms under, at
14.537 / 14.538) and returns **no decision** in census. Everything below is one branch,
`rr/gkr_uniskip_bench`, tip `30e648e4`; the per-task reports, the oracle, the raw logs and
every emitted table live under `.agents/sdd/2026-08-10-v3-r5/` (uncommitted working-tree
artifacts, referenced by name).

### Design — what was built

The lanes are **prefix truncations of the one canonical R4 admission list**, and nothing else:
references descending, ties E4-before-BF then lower source id — the R4 comparator verbatim,
`b.refs.cmp(&a.refs).then(b.width.cmp(&a.width)).then(a.source.cmp(&b.source))` — cut at
**refs ≥ 2**, giving 55 reused sources of the 59 live. Because an E4 entry is four units wide,
only **prefix-K points are canonical**, so the sweep walks K and never C directly; `hot16` is
exactly the K16 point, which is what makes the incumbent a member of its own frontier rather
than a neighbour of it. Admission depends on reference counts alone, so **the frontier is
identical under both term orders**. The kernel is untouched — a lane differs from an R4 arm
only in the host-built admission list and prologue table, same body, same 736 B `C_max` frame.
`--frontier-factorial` runs **ten lanes in one process** — {`k24`, `k32`, `k40`, `k45`, `k46`,
`k48`, `hot16`, `cache0`, `control_lb`}@128 plus the in-rotation shipping anchor
`control@256` — at **100 paired rounds per term order, warmup 10**, both orders, one locked
session; `--frontier-extension` (eight lanes, 104 rounds, warmup 16, `k49`–`k51`) is
conditional and did not run. Three preregistered rules are binding verbatim and are
implemented in the emitter, not in prose: the **signed rule** (A *wins over* B iff the paired
per-round contrast has median < 0 **and ≥ 90/100 on-sign**; loses iff median > 0 and ≥ 90/100
positive; anything else a *wash*), the **headline selector** (eligible = lanes that win over
`hot16@128` under BOTH orders; select the maximum worst-order improvement; ties toward smaller
C; an empty eligible set is the valid outcome "hot16 remains the frontier optimum"), and
**bar success** = the selected lane's raw `eval + finalize` median < 14.61 ms in both orders,
this session.

Oracle for the lane set — controller-derived out-of-tree before any implementation, by the R4
method, and reproduced by the planner rather than defined by it
(`.agents/sdd/2026-08-10-v3-r5/expected-counts-r5.md`, derivation in `oracle-derivation.txt`,
which also pins the full 55-entry admission ordering):

| lane | prefix K | C (units / B) | Rc | chains | stores | loads | removals |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `hot16` (incumbent) | 16 | **28 / 224** | 173 | 181 | 20 | 133 | **145** |
| `k24` | 24 | **36 / 288** | 197 | 165 | 28 | 157 | **161** |
| `k32` | 32 | 44 / 352 | 221 | 149 | 36 | 181 | 177 |
| `k40` | 40 | 52 / 416 | 245 | 133 | 44 | 205 | 193 |
| `k45` | 45 | 57 / 456 | 260 | 123 | 49 | 220 | 203 |
| `k46` | 46 | 61 / 488 | 268 | 119 | 51 | 224 | 207 |
| `k48` | 48 | 69 / 552 | 284 | 111 | 55 | 232 | 215 |
| `k49` † | 49 | 73 / 584 | 292 | 107 | 57 | 236 | 219 |
| `k50` † | 50 | 77 / 616 | 300 | 103 | 59 | 240 | 223 |
| `k51` † | 51 | 81 / 648 | 308 | 99 | 61 | 244 | 227 |

† extension lanes — built and gated, never run (the trigger did not fire). The shape of the
tail is the reason the sweep was drawn this way: through K45 the list is the refs-3 BF band,
and from K46 it is the refs-2 E4 block, where each added source is +4 units, +8 `Rc` and only
+4 removals — **marginal removals-per-unit halves to 1.0** while footprint grows 4× faster per
source. The knee, if it were inside the sweep, was expected at that transition. It is not
inside the sweep at all.

### Gates — all pass, and the kernel never moved

- **Oracle reproduction, 12 fields × 9 `kN` lanes + `hot16`, both term orders**, exactly
  matching `expected-counts-r5.md`; every lane's admitted-id list equals the ordered first-K
  prefix of the pinned 55-entry ordering, and `hot16` is whole-struct equal to `prefix(16)`.
- **The reversal gate is mutation-proven.** Counts alone cannot see a reordering among
  equal-ref, equal-class sources: flipping the comparator's final tie-break leaves the count
  tests **passing** and fails the ordered-list tests. That is why the gate is on the lists.
- **`tools/r5_gates.sh`**: `q`-parity **72/72** cells plus **18/18** E4 self-product cells
  (`--self-products 60` — the `kN` arms admit up to 10 E4 sources against `hot16`'s 4, and
  `--self-products 12` never reaches an E4×E4 record, so the E4 cache path was uncovered
  surface) plus **9/9** CPU-oracle cells; direct ncu local ld/st counts **9/9** lanes with
  `pred_off_all = 0`; the chain counter
  **36/36** cells, both term orders **and** both block sizes; admitted-id lists **20/20**
  ordered prefixes from four *live* rotations, with a negative control (ids 6↔7 swapped) that
  fails all 24 gated appearances; frozen SASS **9/9**.
- **Zero native churn all rung.** The nine frozen bodies are byte-identical at every step,
  including the post-wipe shipped rebuild and Task 4's `-lineinfo` rebuild: **5104, 5104,
  5592, 5600, 5048, 5064, 6024, 5976, 5992** instructions. No `.cu` file was edited in this
  rung, by construction.
- **R4 and R3 stay green**: `r4_gates.sh` 112/112 + 28/28 + 14/14 + 7/7, `r3_gates.sh` 40/40 +
  8/8, `--cache-factorial` still runs, and the R4 emitter's tables are byte-for-byte what they
  were (15 R4 fixtures reproduce message for message).
- **Infrastructure hazard, found live and fixed.** `with_gpu_lock.sh` holds the GPU lock on
  **fd 9**; a `cargo build` under it starts the **sccache** daemon, which inherits fd 9 and
  keeps holding the lock after the build exits — every later locked run then blocks forever
  (recovery: `sccache --stop-server`). Every build in this rung either runs outside the lock or
  closes the fd (`9>&-`). Task 3's insurance ritual rebuilds several times and inherited the
  rule.

**Process note.** The emitter (`tools/r4_table.py`) is the **single decision authority** for
every derived quantity in this rung — curves, signed verdicts, C\*, the extension trigger, the
broad-knee test, the first loser, the headline selector, the bar verdict, the dual bridges and
the ncu capture manifest. It was double-reviewed (one round found a Critical: canonical
neighbours were computed for the per-order winners but not for the headline candidate, which
would have silently dropped the knee bracket for the named lane) and covered by **50 fixtures**
plus a **57-case rejection matrix** *before* any timing ran. Nothing in the sections below is
re-derived from the logs by hand.

### The measurement — ten lanes, 100 paired rounds per order, one session

```bash
# insurance first: gate suites (under the lock), then wipe + shipped rebuild (outside it),
# then diag-OFF / zero ATOM-RED / 9-of-9 frozen SASS / res-usage, then hash the inputs.
.agents/bin/with_gpu_lock.sh bash -c '
  B=target/release/gpu_gkr_uniskip_bench
  for order in census locality; do
    $B --log-trace 24 --warmup 10 --iterations 100 --mode lsb-pair --frontier-factorial \
       --term-order $order > task3-primary-$order.log
  done'
python3 gpu/gkr_uniskip_bench/tools/r4_table.py \
  task3-primary-census.log task3-primary-locality.log      # ONE invocation, both orders
```

One process per term order, both inside a single lock hold (04:37:45 → 04:38:22 UTC), and
**zero builds from the shipped rebuild through the last timed run** — the binary, the native
archive and the emitter hash identically before the first run and after the last. The rebuilt
shipped binary came out **byte-identical to the pre-wipe one**, and the in-session emission is
`cmp`-clean against a post-session re-emission of the same two logs, so the emitter is
deterministic on this input.

**Sanity anchors — 4 of 4 IN.** The preregistered gate is ±2 % of R4's frozen in-rotation
medians on `control@256` and `hot16@128`, per order; one violation aborts the session:

| order | anchor | this session | R4 frozen | delta | verdict |
| --- | --- | --- | --- | --- | --- |
| `locality` | `control@256` | 16.567 | 16.624 | −0.34 % | **IN** |
| `locality` | `hot16@128` | 14.717 | 14.836 | −0.80 % | **IN** |
| `census` | `control@256` | 16.666 | 16.545 | +0.73 % | **IN** |
| `census` | `hot16@128` | 15.120 | 15.129 | −0.06 % | **IN** |

Worst |delta| is 0.80 % of a ±2 % band, so no abort, no cool-down repeat, and the
PAIRED-RESULTS-ONLY clause does **not** apply — the raw-vs-bar claim is admissible from this
session. The **extension trigger was evaluated inside the lock and did not fire**: it requires
`k48` to *win over* `k46` in either order under the signed rule (a wash does not trigger), and
`k48 − k46` is **+0.407 ms locality / +1.515 census, 100/100 on-sign** — a loss in both. No
extension log exists, which is the correct state.

**Telemetry, and what it costs the absolutes.** `nvidia-smi` sampled before and after every
phase: SM clock 2332 → 2280 MHz, power 543–562 W, memory clock 12481 MHz throughout, no
thermal and no hardware-slowdown bit at any sample — but `clocks_event_reasons.active = 0x4`
(**SW Power Cap**) at *every* sample during and after the timed runs. That is the same
behaviour R4 recorded. Paired per-round contrasts are the drift-robust currency and are
unaffected; **every absolute in this session inherits a capped clock**, which matters when it
is set beside Task 4's two uncapped sessions (below) and must never be mixed with the
clock-locked ncu durations.

**Per-lane `eval + finalize` medians** (ms). Both columns are copied cell-by-cell from the two
emitted per-order lane tables in `task3-frontier.md`; no arithmetic was done to combine them.
The emitter also reports `eval` and `finalize` separately on purpose — the 128 lanes reduce
twice the partials — and `finalize` is 0.061–0.063 ms on every 128 lane and 0.033 on
`control@256` in both orders.

| lane | regs, blocks/SM | C | removals | census | locality |
| --- | --- | --- | --- | --- | --- |
| `hot16@128` | 72, 7 | 28 | 145 | **15.120** | **14.717** |
| `k24@128` | 72, 7 | 36 | 161 | 15.292 | 14.824 |
| `k32@128` | 72, 7 | 44 | 177 | 15.474 | 14.893 |
| `k40@128` | 72, 7 | 52 | 193 | 16.048 | 14.998 |
| `k45@128` | 72, 7 | 57 | 203 | 17.113 | 15.076 |
| `k46@128` | 72, 7 | 61 | 207 | 17.862 | 15.106 |
| `k48@128` | 72, 7 | 69 | 215 | 19.372 | 15.504 |
| `cache0@128` | 72, 7 | 0 | 0 | 17.002 | 16.936 |
| `control_lb@128` | 72, 7 | 0 | 0 | 16.356 | 16.302 |
| `control@256` | 72, 3 | 0 | 0 | 16.666 | 16.567 |

The three curves are the emitter's, and are **never pooled across term orders**; all three are
paired per round on `eval + finalize`, the bar quantity. Each table below sets the emitter's
two per-order emissions side by side — every cell **copied cell-by-cell, no arithmetic**. IQRs
for every cell are in `task3-frontier.md`; every row below is 100/100 on-sign.

**Curve 1 — total-net vs `control_lb@128`.** The bound-matched baseline; this is the curve
C\* is read off.

| lane | C | census | verdict | locality | verdict |
| --- | --- | --- | --- | --- | --- |
| `hot16@128` | 28 | **−1.242** | win | **−1.580** | win |
| `k24@128` | 36 | −1.043 | win | −1.468 | win |
| `k32@128` | 44 | −0.874 | win | −1.404 | win |
| `k40@128` | 52 | −0.300 | win | −1.300 | win |
| `k45@128` | 57 | **+0.756** | lose | −1.224 | win |
| `k46@128` | 61 | **+1.511** | lose | −1.198 | win |
| `k48@128` | 69 | **+3.017** | lose | −0.794 | win |

**Curve 2 — marginal vs `hot16@128`.** The incumbent as baseline; the per-removal column
divides by the *incremental* removals over `hot16`, from the runner's `ARM` lines.

| lane | C | census | µs / incr. removal | locality | µs / incr. removal | verdict (both orders) |
| --- | --- | --- | --- | --- | --- | --- |
| `k24@128` | 36 | **+0.188** | +11.77 | **+0.140** | +8.78 | lose |
| `k32@128` | 44 | +0.371 | +11.58 | +0.197 | +6.15 | lose |
| `k40@128` | 52 | +0.934 | +19.46 | +0.301 | +6.27 | lose |
| `k45@128` | 57 | +1.996 | +34.41 | +0.377 | +6.50 | lose |
| `k46@128` | 61 | +2.748 | +44.33 | +0.384 | +6.20 | lose |
| `k48@128` | 69 | +4.253 | +60.75 | +0.789 | +11.28 | lose |

**Curve 3 — machinery-corrected refund vs `cache0@128`.** `cache0` pays the frame, the walk
and the lookup and removes nothing, so this curve is the removals alone; the per-removal
column divides by the lane's own removals.

| lane | C | census | µs / removal | verdict | locality | µs / removal | verdict |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `hot16@128` | 28 | **−1.881** | −12.97 | win | **−2.213** | −15.26 | win |
| `k24@128` | 36 | −1.667 | −10.36 | win | −2.081 | −12.92 | win |
| `k32@128` | 44 | −1.500 | −8.47 | win | −2.020 | −11.41 | win |
| `k40@128` | 52 | −0.925 | −4.79 | win | −1.917 | −9.93 | win |
| `k45@128` | 57 | **+0.114** | +0.56 | lose | −1.840 | −9.06 | win |
| `k46@128` | 61 | **+0.861** | +4.16 | lose | −1.832 | −8.85 | win |
| `k48@128` | 69 | **+2.364** | +11.00 | lose | −1.427 | −6.64 | win |

Curve 3 is the one that separates the two orders cleanly: in `locality` every prefix point
still refunds more than the machinery costs, all the way to C = 69 — the sweep is *profitable*
there and merely *less* profitable than `hot16`. In `census` the refund itself turns negative
at `k45`. Both orders nonetheless pick the same optimum — C\* is read off Curve 1, and no lane
beats the incumbent in either order, which is Curve 2's story.

### The frontier verdict

The decision lines below are the emitter's own, quoted from `task3-frontier.md`; nothing in
this subsection is re-derived.

> - winner (C\*): **`hot16@128`** at C = 28, -1.580 ms vs `control_lb@128` — spec 2.3.
> - broad knee in `locality`: **no** — longest run of consecutive canonical lanes within
>   0.10 ms of the optimum is 1 (spec 2.3 needs >= 3).
> - first loser in `locality`: **`k24@128`** (C = 36), +0.140 ms vs the winner, 100/100
>   on-sign — spec 2.5.

> - winner (C\*): **`hot16@128`** at C = 28, -1.242 ms vs `control_lb@128` — spec 2.3.
> - broad knee in `census`: **no** — longest run of consecutive canonical lanes within
>   0.10 ms of the optimum is 1 (spec 2.3 needs >= 3).
> - first loser in `census`: **`k24@128`** (C = 36), +0.188 ms vs the winner, 100/100
>   on-sign — spec 2.5.

> ⇒ eligible set is EMPTY ⇒ **hot16 remains the frontier optimum** (spec 2.3 — a valid
> outcome).

No lane wins over `hot16@128` in either order, let alone both, so the headline selector's
eligible set is empty by the widest possible margin — the best worst-order figure on the whole
sweep is `k24`'s **+0.1884 ms** *against* the incumbent. **Not broad** in either order gates
off the preregistered reuse-distance follow-up, which is therefore not part of this rung.
**No right-censoring**: a first loser exists in both orders, so the emitter's censoring branch
was never taken, and with no extension there is no session seam to be undecidable across.

**The marginal-removal slope is falsified above C = 28.** The model under test is the R5
spec's own hypothesis (§1), which blended R4's two separate findings — the *instruction* figure
this rung confirms, and R4's **ncu-clock-locked** µs slopes — into a single flat marginal value
"from C = 4 to C = 92". `k24` brings **16 extra removals** over `hot16`. At R4's clock-locked
−17…−23 µs @128 those removals model **−0.27…−0.37 ms**; priced instead on R5's own *timed*
@128 machinery-corrected slope (Curve 3's −12.97 census / −15.26 locality µs per removal, which
is the like-for-like currency) they model **−0.21…−0.24 ms**. They measured **+0.140 ms
locality / +0.188 census**, 100/100 — the model is wrong in *sign*, not merely in magnitude,
and the conclusion does not depend on which slope is used. Its instruction leg is intact
(Task 4 measures 1,478 fewer instructions per warp for those 16 removals, exactly as predicted
in kind), so what has changed is not what a removal saves but what its footprint costs: at
`k24`'s **288 B/thread** (the oracle's `touched = 8C`) the frame occupies **36.1 % of the
128 MiB L2** at 128×7 threads against `hot16`'s 28.1 % (Task 4's ncu extraction), and that
capacity price already exceeds the removal value. **The bite point is between C = 28 and
C = 36** — one lane along the sweep, and far below `allrepeat`, where R4 could first see it.
The supersession note sits at the R4 economics bullet.

### The bar — three layers, kept separate

*The locality-order bar claim now stands on both bridge forms and a standalone raw run; census
remains open.* The three layers below are preregistered as distinct and **must not be blended**
— each has its own scope, and the first is the one the spec fixes as THE raw finding.

**(a) Raw, in-rotation — NOT met.** The spec fixes bar success to the selected lane's raw
`eval + finalize` median in the primary session's rotation, in both orders:

| order | lane | raw median | vs 14.61 bar |
| --- | --- | --- | --- |
| `locality` | `hot16@128` | 14.717 | **over** |
| `census` | `hot16@128` | 15.120 | **over** |

All four sanity anchors were IN, so this raw claim stands as measured rather than being
downgraded to paired-results-only. **This is the rung's raw answer against the bar.**

**(b) The anchor mini-session — locality upgrades, census returns no decision.** The
mini-session is conditional and it applied: 14.717 − 14.61 = **+0.107 ms**, inside the ±0.25 ms
trigger in at least one order. It ran **first**, in its own lock hold, on the untouched Task 3
binary, as an ABBA block of standalone runs per order, 33 timed rounds each, arm order reversed
between blocks. **This table is not the emitter's**: it is `task4-anchor-bridges.md`, computed
by `task4-anchor-analyze.py` from the eight mini-session run logs. Bridge forms are the spec's,
with `R2c` = 16.453 census / 16.283 locality, and the spec fixes the base for this procedure to
the standalone `control@256`:

| order | medC (`control@256`) | medW (`hot16@128`) | additive | ratio | flank spread (ctrl / winner) | verdict |
| --- | --- | --- | --- | --- | --- | --- |
| `locality` | 16.288 | 14.542 | **14.537** | **14.538** | 0.000 / 0.030 | **bar claim UPGRADES — both forms under 14.61** |
| `census` | 16.517 | 15.027 | 14.963 | 14.969 | **0.135** / 0.021 | **unstable — no decision** |

`locality` is not a split and not drift-sensitive: both forms land under, with 0.072–0.073 ms
of margin, on flanks that agree to 0.000 and 0.030 ms; the `total`-median cross-check gives
14.540 / 14.540, the same verdict. Its `control@256` anchor reproduces `R2c` to **0.005 ms**
(16.288 against 16.283), so in this session the bridge barely bridges — which is the reason it
lands where it does. **It is also one session's evidence about a 0.072–0.073 ms margin**: R4's
addendum measured the same standalone arm at 16.608 the day before (+2.0 % over R2), and the
same procedure would have produced a materially different additive number from it. The upgrade
is what the preregistered procedure returns, not a wide margin (see *Open*).

`census` fails the flank gate first — its control flank drifts **0.135 ms**, 2.7× the 0.05 ms
gate, because that block starts from a cold 180 MHz idle — so per the spec it is reported
**unstable and carries no upgrade**. Its two forms did agree with each other and with Task 3's
raw census result (both over, 14.963 / 14.969); that is recorded as data, **not** as a verdict.

**The emitter's own dual bridges — unconditional corroboration, and they split by base.**
Separately from the mini-session, the emitter computes an in-rotation bridge for `hot16@128`
against *both* baselines, unconditionally, from Task 3's own medians (`task3-frontier.md`):

| order | base | medW | medBase | additive | ratio |
| --- | --- | --- | --- | --- | --- |
| `locality` | `control@256` | 14.717 | 16.567 | **14.433** | **14.465** |
| `locality` | `control_lb@128` | 14.717 | 16.302 | **14.698** | **14.700** |
| `census` | `control@256` | 15.120 | 16.666 | 14.908 | 14.927 |
| `census` | `control_lb@128` | 15.120 | 16.356 | 15.218 | 15.210 |

In `locality` these **split by base**: on `control@256` both forms land under 14.61 (14.433 /
14.465), on `control_lb@128` both land over (14.698 / 14.700). R4's own rule governs that
shape — *the whole span is the honest uncertainty and must not be collapsed by choosing a
base* — so the in-rotation corroboration is **14.433–14.700 across bases**, straddling the bar.
It neither confirms nor refutes (b)'s upgrade, and it is not what (b) rests on: the upgrade
comes from the preregistered anchor procedure (spec §2.3), which fixes a **single** base — the
standalone `control@256` — by design, precisely so the answer cannot be chosen by base
selection after the fact. In `census` all four figures land over, consistent with everything
else that order produced.

**(c) Two side facts, with their scope stated.** Neither changes (a).

- **Standalone, `locality`, raw: 14.527 and 14.557** — the two mini-session `hot16@128` runs
  are already *below* 14.61 with no bridge at all. The spec fixes "bar success" to the primary
  session's in-rotation medians, so this does not move (a); it is the reason the bridge lands
  under.
- **The two sessions are not on the same footing.** Task 3's timed session read SW Power Cap
  (`0x4`) at every sample; Task 4's anchor and capture sessions read `0x0` on all 32 samples.
  That is a plausible mechanism for the standalone runs being **0.16–0.19 ms** faster than
  Task 3's in-rotation 14.717 at the identical arm. Paired within-session contrasts are
  unaffected by it; absolutes across the two are not comparable.

### The knee — L2-priced, in both orders

The direction was fixed before the captures: past the winner, **L2 hit rate falls and/or DRAM
SOL rises** while executed-instruction savings keep improving; `long_scoreboard` growth and
fmaheavy recession corroborate but never suffice. Any other pattern would have forced the
record to say "timing optimum located; mechanism unresolved". It does not.

Four Full Picture captures plus four supplementary `--metrics` passes, driven by the emitter's
own two-line ncu manifest (`hot16@128` and `k24@128`, each under both orders), on a `-lineinfo`
rebuild whose nine frozen bodies were re-proved identical at both the archive and the
device-linked-executable level. **The `ncu ms` column below is clock-locked and belongs to a
different scale from every timed median above — the two are never mixed.**

| lane | ncu ms | inst/warp | local-ld L1 hit % | L2 hit % | DRAM SOL % | DRAM rd sectors | fmaheavy active % | long_scoreboard | L2-occupancy |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `hot16@128` census | 15.270 | 57,637 | 0.010 | **69.06** | **50.57** | 340,235,488 | 75.8 | 2.387 | 28.1 % |
| `k24@128` census | 15.425 | 56,159 | 0.009 | **65.97** | **59.77** | 396,660,464 | 73.0 | 2.920 | 36.1 % |
| `hot16@128` locality | 14.820 | 57,637 | **47.871** | 63.14 | **41.99** | 266,107,656 | 77.0 | 1.890 | 28.1 % |
| `k24@128` locality | 14.841 | 56,159 | **41.595** | 63.09 | **48.45** | 294,366,496 | 74.7 | 2.174 | 36.1 % |

Occupancy is 57.8–57.9 % on all four (same body, same 72 registers, 7 blocks/SM), so nothing
here is an occupancy artifact. The counts close **exactly** against the oracle in both orders:
20.0 / 133.0 `STL`/`LDL` per warp at `hot16` against the oracle's 20 and 133, 28.0 / 157.0 at
`k24` against 28 and 157, and the prologue's global fill moves 481 → 497 `LDG`/warp = **+2 per
added cached source**, matching R4's pin. `hot16`'s 57,637 instructions per warp reproduces
R4's figure exactly, on a different build in a different session.

**The signature holds in both orders.** In `census` both primary counters move decisively:
L2 hit **−3.10 pp**, DRAM SOL **+9.20 pp**. In `locality` the L2-hit movement is **−0.05 pp**,
which sits inside the ±0.15 pp resolution floor established by the two independent ncu passes
and is therefore **not claimed** — but the rule is disjunctive, and DRAM SOL moves **+6.46 pp**,
far outside any noise, so the memory leg carries that order on its own. The instruction leg is
exact rather than statistical in both orders: **−1,478 instructions per warp** for +16
removals, i.e. 92.4 net instructions per marginal removal. The corroborators agree — fmaheavy
pipe activity recedes 2.3–2.7 pp and `long_scoreboard` grows 0.28–0.53 — so the arm is spending
instruction savings on a resource that has become scarcer. **Verdict: the knee is L2-priced.**

The traffic accounting is the capacity claim in counter form. `k24` adds **+67,108,864** local
sectors over `hot16` (421.5 M → 488.6 M, +15.9 %); of that added traffic, **84.1 %** arrives
from DRAM in `census` and **42.1 %** in `locality` (≥ 59.1 % / ≥ 17.1 % after subtracting the
prologue's own extra global fill). The L2 stops absorbing **exactly at the margin**: 28.1 % of
L2 coexists with the walk's global stream, 36.1 % does not. DRAM *write* sectors move the same
way (+18.2 M census, +20.0 M locality) — the added frame is being written back, not held.

**Caveat, stated plainly: this is established at the knee, not along a curve.** The manifest is
the deterministic capture set and it names two lanes, so "monotonic across the captured lanes"
degenerates to one step per order. Tracing the curve would need `k32`/`k40` captures, which
nothing in this rung authorizes. Magnitudes also do not travel: ncu's clock-locked `k24 − hot16`
deltas are +0.155 ms census / +0.021 locality against the timed session's +0.188 / +0.140 — the
sign agrees in both orders and census agrees in size, but a single clock-locked launch does not
resolve a 0.14 ms separation. **The timing session remains the authority on size.**

### ★ The winner's residency is order-dependent — and R4 said otherwise

R4 captured `hot16@128` in `census` only and concluded that essentially *nothing* is resident
(local-load L1 hit 0.01 %). That reading is reproduced here exactly — **0.010 %** — and it is a
**census-order fact, not a property of the arm**. The same body, the same admitted set and the
same instruction stream read **47.871 %** local-load L1 hit in `locality`; `k24` reads
**41.595 %**, so the larger footprint measurably erodes it. This is the reuse-distance
mechanism R4 identified for `allrepeat@128` (0.010 % → 26.918 %), now observed **at the winner**
and roughly twice as strong. Store-side hit rates stay ≈ 0 in every cell.

Two consequences, and both are written back into the R4 record at the passages they correct:

- **"L1 is structurally unavailable as the medium"** is census-scoped. The mechanism it names
  — reuse distance, not footprint — is precisely what the locality permutation changes.
- **"`hot16` is an L2-resident cache"** survives as the **capacity** story (28.1 % of L2 in
  either order, and the L2/DRAM counters are what price the knee), but the **residency** half
  now carries a term-order qualifier: in `locality` the frame is roughly half L1-served.

The practical rule: **never write "`hot16` is not L1-resident" without naming the term order.**

### The bar this sets for rung 2 (realization D / segmented carrier)

- **The local-memory carrier's ceiling is `hot16`, C = 28.** Not the frame's capacity — the
  frame holds 92 units — but the machine's willingness to pay for them. Anything past C = 28
  costs at least `k24`'s delta, **+0.140 ms locality / +0.188 census per +8 units (+16
  removals)** at 128×7 threads. That is the price D must undercut to justify capturing more.
- **D's structural advantage is exactly the thing this rung ran out of.** Every thread here
  pays its own prologue and its own frame, so bytes-per-removal is fixed; D's cross-warp
  sharing divides it by the sharing factor. That is the only known lever that moves the
  capacity price, and this rung shows the capacity price is now what binds.
- **What D must beat, concretely.** (i) **Machinery ≪ 0.7–0.9 ms on `eval`** — R4's measured
  intercept in R4's own measure (+0.910 @256 / +0.743 @128, paired on `eval`, not on this
  section's default `eval + finalize`), carried forward unchanged; R5's rotation contains
  `cache0@128` and `control_lb@128` but the
  emitter's three curves are baselined on `control_lb`, `hot16` and `cache0`, and no
  `cache0 − control_lb` contrast was emitted, so the intercept was **not re-measured here**.
  (ii) **Capacity at equal capture ≤ `hot16`'s 28.1 % of L2** — 36.1 % is already past the
  knee. (iii) Or **capture beyond C = 28 at no more than the measured marginal price** above.
- **Term order is a first-class knob for D, and now has a measured L1 leg at the winner**
  (47.871 % vs 0.010 %), not only the L2/DRAM leg R4 priced.
- **The smem-twiddle cycle probe** was still open when this rung closed; it was resolved
  zero-build the next day — see *The smem-twiddle side item — CLOSED* below.

### Open

- **The `census` bridge returned no decision.** Its control flank drifted 0.135 ms because the
  block started from a cold GPU; a repeat with a soak in front of it would probably pass. The
  spec did not authorize one inside this rung and none was run.
- **The `locality` upgrade is one session's evidence about a 0.072–0.073 ms margin** — stated
  where it is claimed, in §*The bar* (b) — and the emitter's unconditional in-rotation bridges
  straddle the bar across bases (**14.433–14.700**), so nothing outside the preregistered
  procedure corroborates it. A second anchor mini-session would settle it; none was authorized.
- **Every absolute from the timed session inherits a capped clock** (`0x4` at every in-run
  sample), and Task 4's two sessions ran uncapped. The 0.16–0.19 ms gap between in-rotation and
  standalone `hot16@128 locality` is consistent with that and is not otherwise explained.
- **Every ncu figure is a single NVTX-wrapped launch.** Instruction and sector counts are
  deterministic and close exactly against the oracle; the *rate* metrics (SOL, hit rates, stall
  ratios) carry one sample's uncertainty — which is why `locality`'s −0.05 pp L2-hit movement
  is reported as inside noise rather than as evidence.
- **The knee is established at the knee, not along a curve** (two-lane manifest, above).
- **The tree is left on the `-lineinfo` build** Task 4 profiled, deliberately: rebuilding would
  break the captures' provenance. Any future timing session must run the insurance sequence —
  wipe the build dirs, rebuild shipped, re-prove 9/9 — before it times anything. That was
  already mandatory; it is now also not optional.
- **The machinery intercept was not re-measured** in this rung (above), so R4's +0.743 ms @128
  — an `eval` figure, not `eval + finalize` — is still the incumbent number.
- **C = 29…35 is unmeasured.** The sweep's first step is eight sources wide: K17…K23 are
  canonical prefix points by this section's own definition and none was sampled. The bracket
  "the knee is between C = 28 and C = 36" is therefore exactly as tight as the evidence, and
  where inside it the crossing sits is unknown.
- **Parked minors** carried out of the gate work: the gate script's negative-control evidence
  is prose-only for the cases the reviewer did not re-run, a `mktemp`-before-trap window, the
  55-entry admission ordering duplicated between the script and Rust without a cross-check,
  and the emitter's "Incomplete for Task 4" note sitting *outside* the fenced manifest block
  (the in-band `orders=` field carries the same signal, which is why no code fix was made).
- **N/A, and recorded as such**: the conditional extension (`k49`–`k51`) — trigger evaluated,
  did not fire; **right-censoring** — a first loser exists in both orders, so the branch was
  never taken.

### The smem-twiddle side item — CLOSED (2026-08-10, zero-build)

The cycle-level measurement R3 left as a conditional and the LDC rider made priceable was
taken **from the R5 Task 4 captures that already existed** — no kernel variant was built. The
zero-build route (per-PC source counters from the winner's own Full Picture reports,
`ncu --import --page source --csv` on `20260810_0452*_v3r5_hot16_128_{census,locality}_full`)
is a *reject* gate: it can prove the prize too small to chase; only a built variant could have
proven a positive. It rejected.

- **The stream, at the winner.** 40 bank-3 `LDC`/`LDCU` sites (9 entry-block at 262,144
  executions each = once per warp-walk; 31 in-loop, the 8 hottest at 27,000,832 each), total
  **313,524,224 warp executions = 2.075 %** of the launch's 15,109,128,192 warp instructions.
  Byte-identical across both orders, as R3's bank-split established.
- **Warp residency at those PCs** (PC sampling, ~1.5 M samples/launch): 3.268 % of all samples
  in `census`, 3.573 % in `locality` — that is *everything* the sites cost, issue included.
- **Actually stalled (not-issued) at those PCs: 0.933 % (`census`) / 0.986 % (`locality`) of
  all samples** — below the 1.5 %-of-wall build threshold preregistered for this probe, in
  both orders. This is the decision line.
- **The stall mix says the smem table would not collect even that.** `stall_mio` dominates
  (51.6 % / 53.4 % of samples at the sites) — MIO instruction-queue backpressure, and the
  replacement `LDS` issues through the *same shared MIO queue*, which in this kernel also
  carries the coset cache's local-memory traffic. Next is `stall_wait` (24.1 % / 22.8 %) —
  the lane-indexed address arithmetic dependency, unchanged by moving the table. The
  serialization the rider priced (2.0 cyc/unique address) is real as *pipe occupancy*
  (1.25–5.02 G SM-cycles device-wide for Ū ∈ [2, 8]) but overlapped: the exposed part is the
  ≤ 1 % above.
- **Attribution caveat**: PC sampling charges dependency stalls to consumers, so
  twiddle-*latency* exposure at consuming FMAs is not in the 0.93–0.99 %. Against chasing it:
  R3's `t`-arm — the one measured attempt to touch this codegen — inverted **+3.43 %**, and
  R1's smem move lost 15 % on the LSU wall.
- **Corroboration**: the resident-codex static bound (R2-normalized, taken independently the
  same day) put the exposed prize at ~1.50 % for the *uncached control* and "probably below"
  at the winner (181/326 chains remaining); the capture-derived number lands at 0.93–0.99 %.

**Verdict: NOT BUILT — closed below threshold.** Reopening needs a new argument, not a re-run;
the standing candidate argument is a D-style variant in which the MIO queue is no longer
contended by local-memory cache traffic, re-pricing `stall_mio` at the sites.

### Branch state

The rung's parked patches landed as signed commits via the layered-patch replay (2026-08-10),
on top of `30e648e4`: `d51251f1` (R4 LDC rider) → `f6b42072` (R4 record) → `6ab19f66` (R4
tooling fixes) → `591f8ff8` (task0: prefix-K admission + frontier lanes) → `e7b048df` (task1:
frontier factorial runner + curve emitter) → `1b814909` (task2: frontier gates) → `e51b1f95`
(task5: this record + README). Replay verified byte- and mode-identical to the live tree
(`.agents/**` excluded). Pushed to `origin/rr/gkr_uniskip_bench` 2026-08-10.

## v3 R6 — the carveout probe

RR-ordered ("do (a)") after the R5-capture finding: the cached 128-thread kernels ran with a
64 KiB shared-memory carveout of the 128 KB unified L1/smem pool while using 3.07 KB/block ×
7 resident blocks = 21.5 KB — L1 at ~62 KB with ~43 KB of SRAM idle — while the uncached
`control@256` got 32 KiB (L1 ≈ 95 KB). The driver APPEARS to size the carveout for the
WARP-limit block count (12 @128, 6 @256), ignoring the register limit (72 regs → 7 blocks)
that actually binds — a heuristic inferred from two kernels, not proven — so every R4/R5
cached-vs-control contrast carried a ~33 KB L1 handicap on the cached side, and the cached
arms won anyway. The probe: hand the idle carveout back to
L1 on the one frozen cached body and re-measure the R5 knee neighborhood. **Locality order
only** (RR ruling: the reordered/locality order IS the shipping order — that is the point of
the reordering machinery; the census bar question is moot). Spec + codex READY-with-
amendments: `.agents/specs/2026-08-10-gkr-uniskip-v3-r6-carveout-probe-design.md`.

### Mechanism and G0 — the hint ladder is NOT the documented rounding

`--carveout-hint <pct>` → `cudaFuncSetAttribute(PreferredSharedMemoryCarveout)` on
`eval_lsb_pair_cached_128_lb_kernel` only, once per process before any launch. Host-only:
the 9/9 frozen SASS bodies are byte-identical through the whole probe (r5_gates `all`
re-proved on the shipped rebuild). The documented percent-of-max-rounds-up model predicts
25 → 32 KB; the driver actually realized **65.54 KB for every hint in 24–40** (the first G0
attempt FAILED on it). Empirical ladder (config captures, this driver/arch):

| hint % | realized config | Block Limit Shared Mem | Theoretical Occupancy |
|-------:|----------------:|-----------------------:|----------------------:|
| 0 | 8 KB | 2 | 16.67 % (LOST) |
| 8 | 16 KB | 5 | 41.67 % (LOST) |
| **16** | **32 KB** | **10** | **58.33 % unchanged** |
| 24–40 | 64 KB | 21 | 58.33 % |
| 50–100 | 100 KB | 33 | 58.33 % |

Every rung has a saved report (`target/profiling/ncu/*_v3r6_ladder_hint*` +
`ladder-probe.log` in the evidence dir — the ladder was re-run with persisted artifacts
after review found the first pass unsaved).

⇒ the probe value is **16**, and the G0 realized-configuration gate (codex amendment 1) is
what caught the doc-model failure. G0 at `--log-trace 24`, fresh processes: hinted 32.77 KB
/ limit 10 / occupancy unchanged — PASS; unhinted 65.54 KB — R5 reproduction, PASS.
Non-gating memory evidence at `hot16`/locality (one launch each): local-load L1 hit sectors
**47.7 % → 56.2 %** (+8.5 pp) under the hint, DRAM read sectors −0.5 % — the L1-capacity
mechanism is real at the winner.

### The sessions — a preregistered design, emitter-decided

5-lane rotation `--carveout-probe` `[k24, k32, k40, hot16, control@256]` (k40 per codex, so
a moved frontier needs no second probe; `control@256` launches the uncached body and is
never hinted — the cross-process anchor), 100 rounds / warmup 10, four processes ABBA by
hint state (off, on, on, off), one locked session each. `tools/r6_probe_table.py` is the
single decision authority — fail-closed, PINNED to the final contract (locality, hint 16,
100 rounds / 10 warmup, applied-hint echo cross-checked against the schedule line); 47
fixtures incl. both-sided threshold pins, mutation-tested with 11 single-line mutants each
caught. `tools/r6_gates.sh` carries the 25-row rejection matrix (both the Rust and the
emitter pins), the self-generating fixture lane (`tools/r6_fixtures/`) and the cpu lane.

- **Session 1** (07:32): sanity anchors all IN (±2 % of R4's frozen medians). ABBA pair 1
  failed the 0.05 ms control flank gate (0.098 — the GPU started cold at 180 MHz/29 °C):
  P2 withheld. P1 decided (below).
- **Soaked repeat** (07:44) — pre-declared in the ledger AFTER the cold raw session was
  observed but BEFORE anything was emitted: remediation of the known cold-start instrument
  failure, with both sessions reported and P1 required to agree across them. ~80 s
  discarded soak first; both pairs then pass the flank gate (0.032 / 0.037).

### VERDICTS (the emitter's lines; both sessions agree on P1)

- **P1 — the frontier does NOT move: "carveout is not the binding capacity term."** Every
  k-lane loses to `hot16` in every process (98–100/100); Δk24 does not shrink under the
  hint in any adjacent pair (session 1: +0.045/+0.047 off vs +0.052/+0.049 on; soaked:
  +0.024/+0.032 off vs +0.032/+0.026 on). Scope: the tested 32 KiB carveout did not move
  the measured {hot16, k24, k32, k40} frontier in this rotation — it does not rule out an
  unmeasured K17–23 optimum, and only `hot16` received memory profiling. Within that
  scope, `hot16` (C = 28) remains the admission optimum and the R5 knee is not
  L1-capacity-priced via the carveout despite the +8.5 pp L1 leg — consistent with the
  knee's DRAM/L2 signature being about traffic the bigger L1 does not intercept.
- **P2 — `hot16` itself improves under the hint: δ = −0.103 / −0.088 ms** (soaked session,
  both pairs stable, control-bridged in-rotation; session 1's one stable pair corroborates
  at −0.100). ~0.6–0.7 % on the winner from a one-line host-side attribute. Locality/
  shipping order only; NOT comparable to the R5 bar layers (the emitter prints this
  scoping on every run).
- In-rotation k-lane deltas are rotation-composition-dependent: this 5-lane rotation prices
  Δk24 at +0.045 (session 1 off) vs R5's 10-lane +0.140 — the signed RELATIONS replicate,
  the magnitudes do not transfer across rotation shapes. Absolutes additionally carry
  SwPowerCap `0x4` (R4/R5-consistent) and the soaked session runs ~0.15 ms slower at 65 °C.

### Follow-ups this opens

- **Baking `carveout-hint 16` into the cached launcher** as the default is a one-line win
  candidate (−0.09..−0.10 ms on the winner) — parked for RR: it shifts every future
  session's baseline, so it should land as its own deliberate step, not ride along.
  ADDENDUM: R7 Task 0 baked hint 16 as the default (parked item (a)); the historical
  off-state is reproducible via `--carveout-hint none`. Every R4/R5 median recorded above
  predates the bake, and `r4_table.py` / `factorial_table.py` carry no hint field, so a
  post-bake log is identified ONLY by the harness's config echo in the raw log — never by the
  emitted tables. The echo is column-aligned, so the grep literal is
  `  carveout hint       16% (eval_lsb_pair_cached_128_lb)`.
- **The driver heuristic generalizes.** Any production kernel whose register limit binds
  below its warp limit may be running with an oversized carveout and a shrunken L1 for no
  reason. A sweep of the production prover's kernels (`Shared Memory Configuration Size`
  vs static-smem-×-resident-blocks) is cheap and could surface free L1 elsewhere.
- **D-rung pricing note:** smem and L1 are ONE 128 KB pool (carveout cap ~100 KB) on this
  architecture — a shared-memory publish buffer prices against the L1 the locality order
  demonstrably uses, not against idle capacity.

### Artifacts and branch state

`.agents/sdd/2026-08-10-v3-r6/`: spec-amended G0 evidence (`g0-*`), the hint-ladder probe
(`ladder-probe.log` + saved reports), both sessions' logs + telemetry + emitted verdicts
(`session*-verdict.md`), the emitter report, ledger (`progress.md`). RR-requested
follow-up: a Full Picture of the WINNING configuration (hot16@128, locality, hint 16) at
`target/profiling/ncu/20260810_084735_v3r6_hot16_128_locality_hinted16_full.ncu-rep` —
sections-only on the shipped post-rebase binary (no lineinfo, so no source correlation),
one launch: 14.78 ms, config 32.77 KB, L1/TEX hit 38.70 % (unhinted R5 capture: 32.96 %),
L2 hit 60.34 %, DRAM 41.87 % SOL, SM 77.18 %, occupancy 57.88 %. Lands as a feat + docs
commit pair on top of `a39da580`.

## v3 R7 — the segmented pair (seg-K4)

This is rung 2 of the ladder R4/R5 set a bar for — "realization D", the segmented carrier.
The winning kernel today gives each 8-lane group one row and walks all 175 term records of
that row, recomputing coset values on the fly out of a 16-source per-thread cache in local
memory (which physically lives in L2). R7 reshapes the kernel the way production's segmented
VM is shaped: the four warps of a block work on the SAME four rows at a time (rows in flight
per block drop 16 → 4, in four sequential *cohorts*), the cached sources are produced ONCE per
cohort cooperatively into a slab the four warps share, each warp then walks only a quarter of
the term list, and the quarter-sums are combined through a shared reduction plane at the end of
every cohort. Total math work is unchanged — there is no 1/K speedup — so the whole thesis was
economic: the cache's live working set shrinks 4×, and if that re-prices residency then the
cache can grow again past R5's `hot16` frontier. The bill for it is ~15 block barriers instead
of 1. The slab's MEDIUM was measured as an open axis (RR: the carrier is not a settled call):
**carrier S** puts it in dynamic shared memory (SRAM on the SM, immune to tap-stream eviction,
but it hard-partitions the one 128 KB L1+smem pool) and **carrier G** puts it in a small
per-block device-scratch region reused across the four cohorts, `st.wb` publish / `ld.ca`
consume (production's exact pattern — no carveout demand, adaptive L1, eviction risk). Spec:
`.agents/specs/2026-08-10-gkr-uniskip-v3-r7-segmented-pair-design.md`; its §7 prior, which
codex and I shared going in, was "seg-recompute is a wash or loss (barriers, unchanged math);
the hot16-capture seg lanes have a credible low-single-digit-% path if the carrier change beats
15 barriers; the capture lanes are where a real step lives (~13.8–14.0 ms IF a carrier
re-prices the frontier)".

**R7 preregisters no closure threshold** (spec, RR ruling): every arm is a datapoint about
where the optimum lies, and the record has to let a reader tell an implementation defect from a
refuted idea. Nothing here declares a winner. The baseline is `hot16@128` WITH the R6 carveout
hint baked in (best-vs-best, RR ruling) — R7 Task 0 made hint 16 the launcher default.

**Headline: no segmented lane beats the incumbent, and it is not an implementation defect.**
Every seg lane in both rotations loses by **+1.822 to +3.939 ms** at maximal sign-stability
(100/100 SMEM, 99/99 GMEM). The decomposition says why: the segmented cohort walk costs
**+3.690 ms** before anything is published, the publish machinery adds **+0.242 ms**, and the
capture only refunds **−2.113 ms**.

### Design — what was built

Five kernel symbols, all 72 registers under `__launch_bounds__(128, 7)`:
`eval_lsb_seg_recompute` (the machinery floor — cohort loop, quarter-lists, reduction plane, no
slab and no prologue), `eval_lsb_seg_s_cv64` / `eval_lsb_seg_s_cv100` (carrier S at the 64 KiB
and 100 KiB carveout requests — one body, two carveout clones, byte-identical SASS),
`eval_lsb_seg_s_acc` (carrier S with the accumulator-first reduction shape) and
`eval_lsb_seg_g` (carrier G). S and G share one templated eval-loop source body behind
compile-time carrier accessors. Host side: a capture-blind K4 dealer (quarter-lists +
prologue owner striping) checked against a committed oracle (`tools/r7_fixtures/seg_oracle.json`,
fnv1a64 over LE record bytes), the `--seg-smem-factorial` (10 lanes) / `--seg-gmem-factorial`
(9 lanes) / `--seg-anchor` (2 lanes) rotations and a single-arm `--carrier
{seg-s,seg-s100,seg-s-acc,seg-g,seg-recompute}` surface for gates and profiling.
`tools/r7_table.py` is the single decision authority (positional, fail-closed, tag/order/rounds/
warmup/per-symbol-carveout all read from the log, never from a filename) and
`tools/r7_gates.sh` is the wall (74-cell support matrix, seg-body SASS digests with teeth so a
diag build cannot be accepted, 76 fixtures, the R5 regression lane). Device parity: **q parity
24/24 bit-exact** against the local control, poison 12/12.

### G0 aborted the first attempt — the carveout ladder is BODY-DEPENDENT

The P4-AMENDED realized-configuration gate failed 2 of 6 points on the first frozen binary
(`7df8640a…`): the two symbols requesting the 64 KiB tier (`eval_lsb_seg_s_cv64`,
`eval_lsb_seg_s_acc`, both at hint 32) realized a **32.77 KB** configuration and ran **4
blocks/SM against a pinned 7**. No timed session was started — the correct abort; zero sessions
wasted. A profiler-independent ABBA×2 corroboration (same body, same slab, differing only in
the carveout request) priced the mis-configuration at **+3.31 ms (+20.4 %), stable to ±0.03 ms**
— an order of magnitude larger than the differentials the rung exists to measure, so had the
sessions run, three decision rows would have been 4-blocks-vs-7-blocks comparisons wearing the
label of a carrier or capture effect.

Root cause, from the diagnostic captures (task-7 report, Part I): **R6's hint ladder is exactly
right on the body it was mapped on, and does not transfer across the shared-memory KIND.**

| body | shared kind, size | hint | realized configuration | Block Limit Shared Mem |
| --- | --- | --- | --- | --- |
| `eval_lsb_pair_cached_128_lb` | **static** 2.05 KB | 16 | 32.77 KB | 10 |
| " | " | 20 | 32.77 KB | 10 |
| " | " | **24** | **65.54 KB** | 21 |
| " | " | **32** | **65.54 KB** | 21 |
| " | " | 40 | 65.54 KB | 21 |
| " | " | 50 | 102.40 KB | 33 |
| `eval_lsb_seg_s_cv64` / `_acc` | **dynamic** 7.17 KB | **32** | **32.77 KB** | 4 |
| `eval_lsb_seg_s_cv100` (hot16) | **dynamic** 7.17 KB | 100 | 102.40 KB | 12 |
| `eval_lsb_seg_s_cv100` (k40) | **dynamic** 13.31 KB | 100 | 102.40 KB | 7 |

The fix wave (`29e36e34`) did three things: made `--carveout-hint` compose with `--carrier` as a
permanent ladder-mapping surface (the frozen CLI could not probe a dynamic body at all),
re-mapped the ladder on a dynamic body — **65.54 KB from hint 33, plateau 33–56, next tier at
64** — and set `SegS64 | SegSAcc => 33`. It also added an in-process **occupancy self-gate**:
`cudaOccupancyMaxActiveBlocksPerMultiprocessor` per seg lane after the carveout is set, asserting
against the lane table's pinned `blocks_per_sm` (it floors rather than asserts on the
static-plane symbols, where the calculator models a smaller partition than the driver selects).
That matters beyond this rung: the `ARM` line prints `lane.blocks_per_sm`, a pinned constant, so
before the self-gate the emitter would have faithfully reproduced a claim of 7 blocks for a lane
the hardware ran at 4. **G0 then passed 6/6** on the fixed binary (`fabf2b5b…`, tip `29e36e34`),
with both former failures realizing 65.54 KB at 7 blocks.

Portable finding: **a carveout-hint ladder is per-body.** Mapping it on a static-shared kernel
says nothing about a dynamic-shared one, and the pinned occupancy constant must be verified
in-process, not only under `ncu`.

### The measurement — eight positional processes, and a corrected soak

`.agents/bin/with_gpu_lock.sh` around every GPU execution; the P1 binary sha (`fabf2b5b…`) was
equal before G0 and after the last session log, with no cargo/cmake invocation anywhere in the
window. A peer agent shared the GPU throughout (prover `ncu`/`nsys` jobs in another worktree),
which is why each session holds the lock across soak *and* measurement.

P3 as briefed defined the soak as an **idle** wait. Measured on session 1, that reproduces
exactly the R6 cold-start artifact the soak exists to remove:

| session-1 attempt | soak | state at first timed launch | `control@256` flank | `hot16@128` flank |
| --- | --- | --- | --- | --- |
| `tuning-nosoak-…` | none (nvidia-smi field error voided it) | cold | — | — |
| `session-reanchor-census-cold` | 80 s **idle** | 180 MHz, 31 °C | 0.008 | **+0.295** |
| `tuning-worksoak80-…` | 80 s **discarded work** | 2295 MHz, 78 °C | 0.044 | 0.060 |
| `tuning-worksoak150-…` | 150 s discarded work | 2317 MHz, 77 °C | 0.200 | 0.182 |

The adopted procedure is R6's 80 s, as **discarded work**: one lock hold containing 80 s of
discarded work on the same rotation, immediately followed by the timed process, 1 Hz telemetry
across both and a `.mark` file at the boundary. 150 s was not better than 80 s — the residual
drift is the inter-process gap (the timed process re-allocates and regenerates 5.75 GiB before
its first launch, ~1.4 s of relative cooldown), not soak length. Session 1 was re-run fresh
under the finalized procedure rather than promoting a tuning run, so no session was selected on
its own flank. Every timed process started at steady state (2295–2385 MHz, 77–78 °C, ~600 W,
6.48 GiB resident, or 9.75 GiB on the GMEM rotation whose G lanes allocate the device slab), and
no foreign compute process appears in any measurement window.

The Step-7 repeat trigger fired on the first pass, so four sessions were re-run in full, soaked,
same flags, and the emitter was re-run with them substituted. Both emitter outputs are kept:
`r7-tables.md` (first pass, history) and **`r7-tables-repeat.md` — the primary decision record.**

Provenance of everything below, stated once. Every **timing** table — session inventory, dealt
plan, lane facts, per-lane medians, paired deltas, machinery decomposition, capture slope, the
carrier bridge, attribution, re-anchor — is copied cell-by-cell from `r7-tables-repeat.md`, and no
timing number here was assembled by hand. The **G0, hint-ladder, soak, flank, Full-Picture and
counter** tables come from the measurement report `.agents/sdd/2026-08-10-v3-r7/task-7-report.md`
(whose only hand-computed figures are the scratch-accounting floors, from C / cohorts / blocks read
off the logs and the ABI). The gate and parity counts quoted in *Design* (74-cell support matrix,
76 fixtures, q parity 24/24, poison 12/12) come from the Task 5 and Task 6 implementation reports.

Every paired figure is stable across the two passes, which is the strongest evidence the tripped flanks did not move the decision:
attribution +0.063 → +0.067 (cv64) and +0.280 → +0.295 (cv100); census machinery +0.315 →
+0.305; census capture −2.243 → −2.197; census acc A/B +0.253 → +0.257. The repeat pass also
brought the one out-of-band anchor back in (`reanchor-census/control@256` +2.20 % → +1.54 %), so
the primary record carries no `ANCHOR OUT OF BAND` banner.

| # | position | tag | order | rounds | warmup | incumbent hint | log |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | reanchor-census | SEG-ANCHOR | `census` | 100 | 10 | 16% | `.agents/sdd/2026-08-10-v3-r7/session-reanchor-census-repeat.log` |
| 2 | reanchor-locality | SEG-ANCHOR | `locality` | 100 | 10 | 16% | `.agents/sdd/2026-08-10-v3-r7/session-reanchor-locality-repeat.log` |
| 3 | smem-locality | SEG-SMEM | `locality` | 100 | 10 | 16% | `.agents/sdd/2026-08-10-v3-r7/session-smem-locality.log` |
| 4 | smem-census | SEG-SMEM | `census` | 100 | 10 | 16% | `.agents/sdd/2026-08-10-v3-r7/session-smem-census-repeat.log` |
| 5 | gmem-locality | SEG-GMEM | `locality` | 99 | 9 | 16% | `.agents/sdd/2026-08-10-v3-r7/session-gmem-locality.log` |
| 6 | gmem-census | SEG-GMEM | `census` | 99 | 9 | 16% | `.agents/sdd/2026-08-10-v3-r7/session-gmem-census.log` |
| 7 | attr-cv64 | SEG-ANCHOR | `locality` | 100 | 10 | 32% | `.agents/sdd/2026-08-10-v3-r7/session-attr-cv64.log` |
| 8 | attr-cv100 | SEG-ANCHOR | `locality` | 100 | 10 | 100% | `.agents/sdd/2026-08-10-v3-r7/session-attr-cv100-repeat.log` |

Dealt-plan identity, validated against the committed Task 2 oracle (the owner census is the
`hot16` REFERENCE stripe the dealer pins arm-independently, not what any one run's prologue
striped):

| order | carried by | list offsets | predicted cost | owners e4 | owners bf | program hash |
| --- | --- | --- | --- | --- | --- | --- |
| `census` | smem-census, gmem-census | 0,49,87,137,175 | 783,731,749,725 | 1,1,1,1 | 3,3,3,3 | `e10a9e26dbf0b75d` |
| `locality` | smem-locality, gmem-locality | 0,46,89,132,175 | 759,713,772,744 | 1,1,1,1 | 3,3,3,3 | `02dbf4b0cd52aae9` |

Lane facts, from the `ARM` lines (identical across every process that carries the lane):

| rotation | lane | kernel | regs | blocks/SM | threads | grid | C | removals | admitted |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| SEG-ANCHOR | `control@256` | `eval_lsb_pair` | 72 | 3 | 256 | 32768 | 0 | 0 | 0 |
| SEG-ANCHOR | `hot16@128` | `eval_lsb_pair_cached_128_lb` | 72 | 7 | 128 | 65536 | 28 | 145 | 16 |
| SEG-SMEM | `control@256` | `eval_lsb_pair` | 72 | 3 | 256 | 32768 | 0 | 0 | 0 |
| SEG-SMEM | `control_lb@128` | `eval_lsb_pair_128_lb` | 72 | 7 | 128 | 65536 | 0 | 0 | 0 |
| SEG-SMEM | `hot16@128` | `eval_lsb_pair_cached_128_lb` | 72 | 7 | 128 | 65536 | 28 | 145 | 16 |
| SEG-SMEM | `seg-recompute@128` | `eval_lsb_seg_recompute` | 72 | 7 | 128 | 65536 | 0 | 0 | 0 |
| SEG-SMEM | `seg-cache0-s@128` | `eval_lsb_seg_s_cv64` | 72 | 7 | 128 | 65536 | 0 | 0 | 0 |
| SEG-SMEM | `seg-hot16-s64@128` | `eval_lsb_seg_s_cv64` | 72 | 7 | 128 | 65536 | 28 | 145 | 16 |
| SEG-SMEM | `seg-hot16-s100@128` | `eval_lsb_seg_s_cv100` | 72 | 7 | 128 | 65536 | 28 | 145 | 16 |
| SEG-SMEM | `seg-k24-s@128` | `eval_lsb_seg_s_cv100` | 72 | 7 | 128 | 65536 | 36 | 161 | 24 |
| SEG-SMEM | `seg-k40-s@128` | `eval_lsb_seg_s_cv100` | 72 | 7 | 128 | 65536 | 52 | 193 | 40 |
| SEG-SMEM | `seg-hot16-acc@128` | `eval_lsb_seg_s_acc` | 72 | 7 | 128 | 65536 | 28 | 145 | 16 |
| SEG-GMEM | `control@256` | `eval_lsb_pair` | 72 | 3 | 256 | 32768 | 0 | 0 | 0 |
| SEG-GMEM | `control_lb@128` | `eval_lsb_pair_128_lb` | 72 | 7 | 128 | 65536 | 0 | 0 | 0 |
| SEG-GMEM | `hot16@128` | `eval_lsb_pair_cached_128_lb` | 72 | 7 | 128 | 65536 | 28 | 145 | 16 |
| SEG-GMEM | `seg-recompute@128` | `eval_lsb_seg_recompute` | 72 | 7 | 128 | 65536 | 0 | 0 | 0 |
| SEG-GMEM | `seg-cache0-g@128` | `eval_lsb_seg_g` | 72 | 7 | 128 | 65536 | 0 | 0 | 0 |
| SEG-GMEM | `seg-hot16-g@128` | `eval_lsb_seg_g` | 72 | 7 | 128 | 65536 | 28 | 145 | 16 |
| SEG-GMEM | `seg-k24-g@128` | `eval_lsb_seg_g` | 72 | 7 | 128 | 65536 | 36 | 161 | 24 |
| SEG-GMEM | `seg-k40-g@128` | `eval_lsb_seg_g` | 72 | 7 | 128 | 65536 | 52 | 193 | 40 |
| SEG-GMEM | `seg-allrepeat-g@128` | `eval_lsb_seg_g` | 72 | 7 | 128 | 65536 | 88 | 234 | 55 |

### The arms — per-lane medians (`eval`, `finalize`, `eval + finalize`, ms)

Copied cell-by-cell from the primary emitter record; the metric is `eval + finalize` per round.

| position | lane | eval | finalize | eval+finalize |
| --- | --- | --- | --- | --- |
| reanchor-census | `control@256` | 16.767 | 0.034 | **16.801** |
| reanchor-census | `hot16@128` | 15.214 | 0.063 | **15.277** |
| reanchor-locality | `control@256` | 16.621 | 0.033 | **16.654** |
| reanchor-locality | `hot16@128` | 14.644 | 0.065 | **14.709** |
| smem-locality | `control@256` | 16.625 | 0.033 | **16.659** |
| smem-locality | `control_lb@128` | 16.313 | 0.061 | **16.374** |
| smem-locality | `hot16@128` | 14.641 | 0.065 | **14.705** |
| smem-locality | `seg-recompute@128` | 18.334 | 0.061 | **18.396** |
| smem-locality | `seg-cache0-s@128` | 18.577 | 0.061 | **18.639** |
| smem-locality | `seg-hot16-s64@128` | 16.467 | 0.061 | **16.528** |
| smem-locality | `seg-hot16-s100@128` | 16.582 | 0.061 | **16.644** |
| smem-locality | `seg-k24-s@128` | 16.715 | 0.061 | **16.776** |
| smem-locality | `seg-k40-s@128` | 17.073 | 0.061 | **17.134** |
| smem-locality | `seg-hot16-acc@128` | 16.706 | 0.061 | **16.767** |
| smem-census | `control@256` | 16.718 | 0.033 | **16.751** |
| smem-census | `control_lb@128` | 16.399 | 0.061 | **16.462** |
| smem-census | `hot16@128` | 15.161 | 0.063 | **15.224** |
| smem-census | `seg-recompute@128` | 18.402 | 0.061 | **18.463** |
| smem-census | `seg-cache0-s@128` | 18.708 | 0.061 | **18.770** |
| smem-census | `seg-hot16-s64@128` | 16.512 | 0.061 | **16.574** |
| smem-census | `seg-hot16-s100@128` | 16.629 | 0.061 | **16.691** |
| smem-census | `seg-k24-s@128` | 16.754 | 0.062 | **16.817** |
| smem-census | `seg-k40-s@128` | 17.200 | 0.061 | **17.262** |
| smem-census | `seg-hot16-acc@128` | 16.769 | 0.062 | **16.830** |
| gmem-locality | `control@256` | 16.636 | 0.033 | **16.669** |
| gmem-locality | `control_lb@128` | 16.326 | 0.061 | **16.387** |
| gmem-locality | `hot16@128` | 14.651 | 0.065 | **14.714** |
| gmem-locality | `seg-recompute@128` | 18.344 | 0.061 | **18.406** |
| gmem-locality | `seg-cache0-g@128` | 18.592 | 0.061 | **18.653** |
| gmem-locality | `seg-hot16-g@128` | 16.557 | 0.063 | **16.621** |
| gmem-locality | `seg-k24-g@128` | 16.748 | 0.065 | **16.812** |
| gmem-locality | `seg-k40-g@128` | 17.153 | 0.063 | **17.217** |
| gmem-locality | `seg-allrepeat-g@128` | 17.464 | 0.063 | **17.529** |
| gmem-census | `control@256` | 16.875 | 0.033 | **16.908** |
| gmem-census | `control_lb@128` | 16.538 | 0.061 | **16.602** |
| gmem-census | `hot16@128` | 15.280 | 0.063 | **15.344** |
| gmem-census | `seg-recompute@128` | 18.582 | 0.061 | **18.644** |
| gmem-census | `seg-cache0-g@128` | 18.860 | 0.061 | **18.922** |
| gmem-census | `seg-hot16-g@128` | 16.770 | 0.063 | **16.834** |
| gmem-census | `seg-k24-g@128` | 16.913 | 0.063 | **16.977** |
| gmem-census | `seg-k40-g@128` | 17.375 | 0.063 | **17.438** |
| gmem-census | `seg-allrepeat-g@128` | 17.729 | 0.063 | **17.792** |
| attr-cv64 | `control@256` | 16.633 | 0.033 | **16.666** |
| attr-cv64 | `hot16@128` | 14.722 | 0.063 | **14.787** |
| attr-cv100 | `control@256` | 16.680 | 0.033 | **16.713** |
| attr-cv100 | `hot16@128` | 14.992 | 0.063 | **15.056** |

Paired deltas vs the incumbent `hot16@128`, per round, on `eval + finalize`. Sign-stability is
the count of rounds on the median's own side against ceil(0.9 N); R7 preregisters no closure
threshold, so it is REPORTED and no row selects a winner:

| position | lane | C | removals | median Δ (ms) | sign-stability |
| --- | --- | --- | --- | --- | --- |
| smem-locality | `seg-recompute@128` | 0 | 0 | **+3.690** | 100/100 pos (≥ 90) |
| smem-locality | `seg-cache0-s@128` | 0 | 0 | **+3.934** | 100/100 pos (≥ 90) |
| smem-locality | `seg-hot16-s64@128` | 28 | 145 | **+1.822** | 100/100 pos (≥ 90) |
| smem-locality | `seg-hot16-s100@128` | 28 | 145 | **+1.938** | 100/100 pos (≥ 90) |
| smem-locality | `seg-k24-s@128` | 36 | 161 | **+2.071** | 100/100 pos (≥ 90) |
| smem-locality | `seg-k40-s@128` | 52 | 193 | **+2.430** | 100/100 pos (≥ 90) |
| smem-locality | `seg-hot16-acc@128` | 28 | 145 | **+2.062** | 100/100 pos (≥ 90) |
| smem-census | `seg-recompute@128` | 0 | 0 | **+3.244** | 100/100 pos (≥ 90) |
| smem-census | `seg-cache0-s@128` | 0 | 0 | **+3.545** | 100/100 pos (≥ 90) |
| smem-census | `seg-hot16-s64@128` | 28 | 145 | **+1.349** | 100/100 pos (≥ 90) |
| smem-census | `seg-hot16-s100@128` | 28 | 145 | **+1.467** | 100/100 pos (≥ 90) |
| smem-census | `seg-k24-s@128` | 36 | 161 | **+1.591** | 100/100 pos (≥ 90) |
| smem-census | `seg-k40-s@128` | 52 | 193 | **+2.037** | 100/100 pos (≥ 90) |
| smem-census | `seg-hot16-acc@128` | 28 | 145 | **+1.605** | 100/100 pos (≥ 90) |
| gmem-locality | `seg-recompute@128` | 0 | 0 | **+3.693** | 99/99 pos (≥ 90) |
| gmem-locality | `seg-cache0-g@128` | 0 | 0 | **+3.939** | 99/99 pos (≥ 90) |
| gmem-locality | `seg-hot16-g@128` | 28 | 145 | **+1.909** | 99/99 pos (≥ 90) |
| gmem-locality | `seg-k24-g@128` | 36 | 161 | **+2.099** | 99/99 pos (≥ 90) |
| gmem-locality | `seg-k40-g@128` | 52 | 193 | **+2.503** | 99/99 pos (≥ 90) |
| gmem-locality | `seg-allrepeat-g@128` | 88 | 234 | **+2.816** | 99/99 pos (≥ 90) |
| gmem-census | `seg-recompute@128` | 0 | 0 | **+3.291** | 99/99 pos (≥ 90) |
| gmem-census | `seg-cache0-g@128` | 0 | 0 | **+3.567** | 99/99 pos (≥ 90) |
| gmem-census | `seg-hot16-g@128` | 28 | 145 | **+1.483** | 99/99 pos (≥ 90) |
| gmem-census | `seg-k24-g@128` | 36 | 161 | **+1.627** | 99/99 pos (≥ 90) |
| gmem-census | `seg-k40-g@128` | 52 | 193 | **+2.080** | 99/99 pos (≥ 90) |
| gmem-census | `seg-allrepeat-g@128` | 88 | 234 | **+2.438** | 99/99 pos (≥ 90) |

### The four decision differentials

**1 — publish machinery at zero capture** (`seg-cache0` − `seg-recompute`, paired inside one
process): **+0.242 ms** carrier S / **+0.246 ms** carrier G on `locality`. **2 — capture value at
`hot16`** (`seg-hot16` − the same carrier's `seg-cache0`): **−2.113 ms** S at its 64 KiB request,
**−1.995 ms** S at the 100 KiB request, **−2.030 ms** G. **3 — the accumulator-first reduction
A/B** (`seg-hot16-acc` − `seg-hot16-s64`, matched carveout tier): **+0.241 ms**, i.e. fold-first
wins. All rows 100/100 or 99/99 on sign, and all reproduce in `census`:

| position | contrast | symbols | isolates | median Δ (ms) | sign-stability |
| --- | --- | --- | --- | --- | --- |
| smem-locality | `seg-cache0-s@128` − `seg-recompute@128` | `eval_lsb_seg_s_cv64` − `eval_lsb_seg_recompute` | publish machinery at zero capture | **+0.242** | 100/100 pos (≥ 90) |
| smem-locality | `seg-hot16-s64@128` − `seg-cache0-s@128` | `eval_lsb_seg_s_cv64` − `eval_lsb_seg_s_cv64` | capture at hot16, 64 KiB request | **-2.113** | 100/100 neg (≥ 90) |
| smem-locality | `seg-hot16-s100@128` − `seg-cache0-s@128` | `eval_lsb_seg_s_cv100` − `eval_lsb_seg_s_cv64` | capture at hot16, 100 KiB request | **-1.995** | 100/100 neg (≥ 90) |
| smem-locality | `seg-hot16-acc@128` − `seg-hot16-s64@128` | `eval_lsb_seg_s_acc` − `eval_lsb_seg_s_cv64` | accumulator-first reduction A/B | **+0.241** | 100/100 pos (≥ 90) |
| smem-census | `seg-cache0-s@128` − `seg-recompute@128` | `eval_lsb_seg_s_cv64` − `eval_lsb_seg_recompute` | publish machinery at zero capture | **+0.305** | 100/100 pos (≥ 90) |
| smem-census | `seg-hot16-s64@128` − `seg-cache0-s@128` | `eval_lsb_seg_s_cv64` − `eval_lsb_seg_s_cv64` | capture at hot16, 64 KiB request | **-2.197** | 100/100 neg (≥ 90) |
| smem-census | `seg-hot16-s100@128` − `seg-cache0-s@128` | `eval_lsb_seg_s_cv100` − `eval_lsb_seg_s_cv64` | capture at hot16, 100 KiB request | **-2.080** | 100/100 neg (≥ 90) |
| smem-census | `seg-hot16-acc@128` − `seg-hot16-s64@128` | `eval_lsb_seg_s_acc` − `eval_lsb_seg_s_cv64` | accumulator-first reduction A/B | **+0.257** | 100/100 pos (≥ 90) |
| gmem-locality | `seg-cache0-g@128` − `seg-recompute@128` | `eval_lsb_seg_g` − `eval_lsb_seg_recompute` | publish machinery at zero capture | **+0.246** | 99/99 pos (≥ 90) |
| gmem-locality | `seg-hot16-g@128` − `seg-cache0-g@128` | `eval_lsb_seg_g` − `eval_lsb_seg_g` | capture at hot16 | **-2.030** | 99/99 neg (≥ 90) |
| gmem-census | `seg-cache0-g@128` − `seg-recompute@128` | `eval_lsb_seg_g` − `eval_lsb_seg_recompute` | publish machinery at zero capture | **+0.275** | 99/99 pos (≥ 90) |
| gmem-census | `seg-hot16-g@128` − `seg-cache0-g@128` | `eval_lsb_seg_g` − `eval_lsb_seg_g` | capture at hot16 | **-2.074** | 99/99 neg (≥ 90) |

**Semantic note on the acc A/B** (Task 3 ledger, and the record is required to state it): the
reviewer's measured spill fix hoisted the eq scaling pre-publish in the acc epilogue, so the
fixed acc arm carries eq in all four warps, matched with fold-first. The contrast therefore
isolates the xor-fold-plus-plane **shape** at matched eq work — fairer than the original design,
but it is no longer a test of the full epilogue-prefix redundancy. Both bodies realize the same
65.54 KB configuration, so the tier is matched too.

**4 — capture slope per carrier**, paired, matched symbol, per removal (the divisor is the
removals delta read off the two `ARM` lines, so the slope carries no literal of its own):

| position | contrast | Δ removals | median Δ (ms) | µs per removal | sign-stability |
| --- | --- | --- | --- | --- | --- |
| smem-locality | `seg-k24-s@128` − `seg-hot16-s100@128` | 16 | **+0.134** | +8.35 | 100/100 pos (≥ 90) |
| smem-locality | `seg-k40-s@128` − `seg-hot16-s100@128` | 48 | **+0.491** | +10.22 | 100/100 pos (≥ 90) |
| smem-census | `seg-k24-s@128` − `seg-hot16-s100@128` | 16 | **+0.124** | +7.74 | 100/100 pos (≥ 90) |
| smem-census | `seg-k40-s@128` − `seg-hot16-s100@128` | 48 | **+0.572** | +11.91 | 100/100 pos (≥ 90) |
| gmem-locality | `seg-k24-g@128` − `seg-hot16-g@128` | 16 | **+0.190** | +11.86 | 99/99 pos (≥ 90) |
| gmem-locality | `seg-k40-g@128` − `seg-hot16-g@128` | 48 | **+0.592** | +12.34 | 99/99 pos (≥ 90) |
| gmem-locality | `seg-allrepeat-g@128` − `seg-hot16-g@128` | 89 | **+0.906** | +10.18 | 99/99 pos (≥ 90) |
| gmem-census | `seg-k24-g@128` − `seg-hot16-g@128` | 16 | **+0.144** | +9.01 | 99/99 pos (≥ 90) |
| gmem-census | `seg-k40-g@128` − `seg-hot16-g@128` | 48 | **+0.588** | +12.26 | 99/99 pos (≥ 90) |
| gmem-census | `seg-allrepeat-g@128` − `seg-hot16-g@128` | 89 | **+0.954** | +10.72 | 99/99 pos (≥ 90) |

**The carrier axis** — S vs G at matched capture, bridged over the two lanes both rotations carry
(the R4/R5 cross-session anchor method; δ = (S − A_S) − (G − A_G), negative favours S; the flank
is |A_S − A_G| and past 0.05 ms the row is `unstable`). Matched **capture**, not matched
configuration: the `capture` column names S's carveout request, while G needs no slab carveout and
runs hint 16 / 32.77 KB on every one of these rows. `locality`, the headline:

| capture | S lane | G lane | anchor | flank (ms) | stable | S med | G med | δ (ms) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| machinery floor | `seg-recompute@128` | `seg-recompute@128` | `control@256` | 0.010 | **stable** | 18.396 | 18.406 | **+0.000** |
| machinery floor | `seg-recompute@128` | `seg-recompute@128` | `hot16@128` | 0.009 | **stable** | 18.396 | 18.406 | **-0.001** |
| cache0 | `seg-cache0-s@128` | `seg-cache0-g@128` | `control@256` | 0.010 | **stable** | 18.639 | 18.653 | **-0.004** |
| cache0 | `seg-cache0-s@128` | `seg-cache0-g@128` | `hot16@128` | 0.009 | **stable** | 18.639 | 18.653 | **-0.005** |
| hot16 | `seg-hot16-s64@128` | `seg-hot16-g@128` | `control@256` | 0.010 | **stable** | 16.528 | 16.621 | **-0.082** |
| hot16 | `seg-hot16-s64@128` | `seg-hot16-g@128` | `hot16@128` | 0.009 | **stable** | 16.528 | 16.621 | **-0.083** |
| hot16, 100 KiB request | `seg-hot16-s100@128` | `seg-hot16-g@128` | `control@256` | 0.010 | **stable** | 16.644 | 16.621 | **+0.034** |
| hot16, 100 KiB request | `seg-hot16-s100@128` | `seg-hot16-g@128` | `hot16@128` | 0.009 | **stable** | 16.644 | 16.621 | **+0.033** |
| k24 | `seg-k24-s@128` | `seg-k24-g@128` | `control@256` | 0.010 | **stable** | 16.776 | 16.812 | **-0.025** |
| k24 | `seg-k24-s@128` | `seg-k24-g@128` | `hot16@128` | 0.009 | **stable** | 16.776 | 16.812 | **-0.026** |
| k40 | `seg-k40-s@128` | `seg-k40-g@128` | `control@256` | 0.010 | **stable** | 17.134 | 17.217 | **-0.072** |
| k40 | `seg-k40-s@128` | `seg-k40-g@128` | `hot16@128` | 0.009 | **stable** | 17.134 | 17.217 | **-0.073** |

The `census` bridge is the dealing-damage diagnostic and is never pooled with the locality row;
in the primary record all twelve of its rows are `unstable` (flank 0.157 on `control@256`, 0.120
on `hot16@128`), so **there is no census carrier decision** — its δ values run −0.140…+0.014 and
agree in sign with locality without being admissible on their own.

### Verdict — no winner; the loss is the cohort walk, not the carrier

- **No winner.** No seg lane has a negative paired median against `hot16@128` in any process;
  every one is positive at the maximum sign-stability the rotation can produce.
- **First loser: `seg-hot16-s64@128`, +1.822 ms** locality (+1.349 census) — carrier S, `hot16`
  capture, at its 64 KiB request.
- **The three terms account for the loss.** Walk floor +3.690, publish machinery +0.242, capture
  −2.113 ⇒ +1.819 against the measured +1.822. The 3 µs gap is not an accounting error and the
  agreement is not an identity: each Δ is its own per-round median and medians are not additive,
  so summing them is an approximation (plus three roundings). The machinery is cheap and the
  capture is real and large; the segmented walk floor is what nothing refunds. The same
  decomposition holds on carrier G (+3.693 / +0.246 / −2.030 ⇒ +1.909 vs a measured +1.909) and
  in `census`.
- **Absolutes, for the bar.** The best seg lane's in-rotation median is **16.528 ms** against the
  same process's incumbent at **14.705** and the 14.61 ms windowed-candidate bar — the rung is
  not near it. Against R5's rung-2 requirement, "machinery ≪ 0.7–0.9 ms" (an R4 `eval` figure,
  not this section's `eval + finalize`), the publish machinery at ~0.25 ms passes comfortably and
  the cohort-walk floor at +3.690 ms does not.
- **`hot16` (C = 28) stays the best TESTED admission point under segmentation.** The capture
  slope is POSITIVE on both carriers, +8.35/+10.22 µs per removal on S and +11.86/+12.34/+10.18
  on G: past `hot16` each additional admitted source costs 8–12 µs rather than saving time. Scope
  is the same as R5's and R6's — the tested points are {`hot16`, k24, k40} on S and {`hot16`, k24,
  k40, allrepeat} on G, and **K17–23 (C = 29…35) remains unmeasured in every rung**, so this rules
  out a *further* frontier, not an unsampled one just past C = 28. R5's admission-frontier result
  survives the restructuring within that scope, so the "re-priced frontier" half of the spec's
  thesis is refuted as well as the carrier half.
- **The carrier axis resolves at ±0.08 ms — and not at a matched configuration.** At matched
  capture (`hot16`, C = 28) S is ahead of G by −0.082/−0.083 ms (locality, both anchors, stable)
  when S runs its 64 KiB request; when the same S body instead requests 100 KiB the sign flips to
  +0.034/+0.033. Neither row is a matched-configuration comparison: **carrier G runs hint 16 /
  32.77 KB at every capture size** (it needs no slab carveout — smem carries only its reduction
  plane), while S realizes 65.54 KB or 102.40 KB. So the carrier δ is entangled with the
  shared-memory configuration the two arms run at, and the honest reading is that the whole
  carrier axis lives inside a ±0.09 ms band that is an order of magnitude below the walk floor —
  not that one carrier is established as better at a matched config.
- **Spec §7's prior, scored:** "seg-recompute is a wash or loss" — a loss, +3.690 ms; "the
  hot16-capture lanes have a credible low-single-digit-% path" — they do not: the best of them is
  +1.822 ms on a 14.705 ms incumbent;
  "the capture lanes are where a real step lives IF a carrier re-prices the frontier" — no
  carrier re-priced it.

### Differential scratch accounting — the publish round-trip

`ncu` has no per-address-range attribution, so the round-trip is priced KERNEL-WIDE as carrier G
minus the matched carrier-S lane (identical work, slab in shared memory instead of device
scratch) and minus `seg-recompute`. Targeted `--metrics` captures, one round each; deliberately
not a Full Picture, because the 17-section list does not report these sums exactly. Arithmetic
floor = slab bytes per block × cohorts × blocks, the prologue publishing once per cohort
(`uniskip_seg_prologue` inside the `UNISKIP_SEG_COHORTS = 4` loop), slab = C units × 256 B,
65 536 blocks:

| capture point | C | slab/block/cohort | write floor | in 32-B sectors |
| --- | --- | --- | --- | --- |
| hot16 | 28 | 7 168 B | 1 879 048 192 B = **1.879 GB** | 58 720 256 |
| k40 | 52 | 13 312 B | 3 489 660 928 B = **3.490 GB** | 109 051 904 |

| counter | G−S at hot16 | vs floor | G−S at k40 | vs floor |
| --- | --- | --- | --- | --- |
| `l1tex__t_sectors_…_op_st.sum` | 62 914 560 − 4 194 304 = **58 720 256** | **1.0000×** | 113 246 208 − 4 194 304 = **109 051 904** | **1.0000×** |
| `lts__t_sectors_op_write.sum` | 62 932 644 − 4 214 107 = 58 718 537 | 0.99997× | 113 268 549 − 4 217 250 = 109 051 299 | 0.99999× |
| `dram__bytes_op_write.sum` | 496.00 − 38.09 = **457.91 MB** | **0.244×** | 889.89 − 37.86 = **852.03 MB** | 0.244× |
| `l1tex__t_sectors_…_op_ld.sum` | 1 110 441 984 − 747 634 688 = 362 807 296 | 6.18× the write side | 1 311 768 576 − 797 966 336 = 513 802 240 | 4.71× |
| `lts__t_sectors_op_read.sum` | 677 280 226 − 536 050 788 = 141 229 438 | 0.39× of the L1 read side | 910 344 345 − 736 778 847 = 173 565 498 | 0.34× |
| `dram__bytes_op_read.sum` | 6.18 GB in **every** arm | unchanged | 6.18 GB | unchanged |

**The accounting closes to the sector: the G−S write differential equals the arithmetic slab
floor at 1.0000×** (1.879 GB per pass at `hot16`, 3.490 GB at k40), which independently confirms
the slab is published once per cohort and never re-written. Two facts fall out. **Only 24.4 % of
the published bytes ever reach DRAM** (457.91 MB of 1.879 GB, the same ratio at both capture
points), so the spec's re-dirtying hypothesis — "region re-dirtying across cohorts means most
publish writes plausibly die in L2 before reaching DRAM" — is largely confirmed: three quarters
of them do. And the consume side shows **no measurable incremental DRAM-read signal**:
`dram__bytes_op_read` reads 6.18 GB in every arm — the tap backing alone — so the slab's reads add
nothing the counter can resolve above it. Read both facts for what the method is: a kernel-wide
differential from one capture per point, with no per-address-range attribution, so it bounds the
slab's traffic rather than isolating it. Within that bound the round-trip lives in L1/L2, which is
why carrier G loses only ~0.08 ms to S rather than the 1.9 GB of DRAM traffic the arithmetic floor
would suggest — and equally why neither carrier can pay for the walk.

### Full Pictures — the deterministic set, doc recipe

Ten captures on `gpu/docs/profiling_ncu.md`'s explicit 17-section list (never `--set full`),
`--nvtx-include "gkr_uniskip_pass0/"` with the trailing slash, date-prefixed `-o`, one round
each: `seg-recompute`, both `cache0`s, S-`hot16` (= the first loser), G-`hot16`, S-`hot16`-acc,
`seg-hot16-s100` (the carveout-matched reference for S's cv100 capture lanes), S-`k40`, G-`k40`,
G-`allrepeat`. **Deviation,
unavoidable under P1: lineinfo was NOT enabled** — the doc's Full Picture step requires a
rebuild and no build may run inside the freeze window, so `SourceCounters` has no line mapping.

| capture | duration (ms, profiled) | SM SOL % | DRAM SOL % | L1/TEX hit % | L2 hit % | L1/TEX throughput % |
| --- | --- | --- | --- | --- | --- | --- |
| seg-recompute | 18.05 | 80.27 | 21.57 | 42.90 | 51.34 | 17.01 |
| seg-cache0-s | 18.36 | 80.39 | 21.20 | 28.02 | 61.35 | 16.70 |
| seg-cache0-g | 18.34 | 80.38 | 21.23 | 43.07 | 51.23 | 16.72 |
| **seg-S-hot16** (first-loser) | 16.31 | 74.17 | 23.86 | 28.51 | 64.12 | 14.03 |
| seg-G-hot16 | 16.23 | 73.20 | 25.75 | 38.52 | 71.81 | 14.10 |
| seg-S-hot16-acc | 16.63 | 75.46 | 23.41 | 28.64 | 64.06 | 13.90 |
| seg-hot16-s100 | 16.38 | 73.89 | 23.78 | **8.75** | 71.85 | 13.97 |
| seg-S-k40 | 17.17 | 82.93 | 22.67 | **8.03** | 73.81 | 12.36 |
| seg-G-k40 | 16.91 | 82.34 | 26.19 | 29.22 | 78.38 | 12.55 |
| seg-G-allrepeat | 17.36 | 86.06 | 27.89 | 23.30 | 82.09 | 14.63 |

Three readings. (1) Every seg arm is **SM-bound** (73–86 % SM SOL against 21–28 % DRAM), so the
segmented floor is instruction work, not memory — the same binding term v3 has had since R2, and
the reason a carrier swap cannot pay for the walk. (2) The 100 KiB request collapses the L1 hit
rate (8.75 % at `s100` against 28.51 % at the same body's 64 KiB request) for **+0.116 ms** — that
one is the segmented body's own price for the tier, paired inside the SMEM rotation (`s100` +1.938
− `s64` +1.822). (3) Carrier G's slab shows up exactly where it should — DRAM SOL 25.75 vs S's
23.86 and L2 hit 71.81 vs 64.12 at matched `hot16`, where G runs 32.77 KB and S 65.54 KB.

### Attribution — what the incumbent's carveout hint alone does

The same 2-lane SEG-ANCHOR rotation at three hints, so the contrast is the paired per-round
`hot16@128 − control@256` INSIDE each process (drift-immune) and the attribution is the
difference of those contrasts across processes; `control@256` is a different symbol and is never
hinted.

| position | hint | median (hot16 − control@256) | sign-stability | Δ vs reanchor-locality |
| --- | --- | --- | --- | --- |
| reanchor-locality | 16% | **-1.948** | 100/100 neg (≥ 90) | — |
| attr-cv64 | 32% | **-1.880** | 100/100 neg (≥ 90) | **+0.067** |
| attr-cv100 | 100% | **-1.653** | 100/100 neg (≥ 90) | **+0.295** |

Handing shared memory away from L1 costs the incumbent monotonically: **+0.067 ms at the 64 KiB
tier and +0.295 ms at 100 KiB.** These figures are measured **on the incumbent's own body, in the
2-lane attribution rotation** — they are not a measurement of any segmented arm, and nothing here
licenses subtracting them from a seg lane. What they are good for is the configurations: the
attribution walks the same realized tiers the seg carriers run at (the seg bodies reach 65.54 KB at
hint 33 and the incumbent at 32, but the configuration is identical), so it says what a 100 KiB
carveout costs a cached body of this shape when nothing else changes. The segmented body's own
price for that tier is the +0.116 ms `s100` − `s64` step above. Both readings matter for the
carrier axis: carrier G asks for no slab carveout at all and runs hint 16 / 32.77 KB at every
capture size, so the S100-vs-G bridge row is comparing arms at 102.40 KB and 32.77 KB, not at a
matched configuration.

Re-anchor against R4's frozen in-rotation medians (±2 %, NON-FATAL — it scopes the absolutes and
invalidates no paired contrast; `hot16@128` here carries the R6 hint the frozen anchor did not,
so only `control@256` is like-for-like):

| position | lane | this session | R4 frozen | delta | verdict |
| --- | --- | --- | --- | --- | --- |
| reanchor-census | `control@256` | 16.801 | 16.545 | +1.54 % | **IN** |
| reanchor-census | `hot16@128` | 15.277 | 15.129 | +0.98 % | **IN** |
| reanchor-locality | `control@256` | 16.654 | 16.624 | +0.18 % | **IN** |
| reanchor-locality | `hot16@128` | 14.709 | 14.836 | -0.86 % | **IN** |

### Protocol lessons

- **"Soak" must mean discarded work, not idle.** An idle soak leaves the part at 180 MHz / 31 °C
  at the first timed launch and the session heats through its own rounds — the R6 cold-start
  artifact the soak was invented to prevent, measured here at +0.295 ms of flank and absolutes
  ~0.6 ms off the warm state. The runbook wording is what caused it, and the fix is one word.
- **The 0.05 ms flank rule must scale with the rotation's timed span.** On the 2-lane SEG-ANCHOR
  rotation (~3.4 s timed) the "first full cycle" is two rounds taken within ~30 ms of the first
  launch: 3 of 6 attempts tripped, two of them twice, while every 9- and 10-lane rotation (cycle
  ~150 ms) held at 0.001–0.029 ms in every process. This is an instrument finding, not a data
  problem — the anchor rotations' payload is the PAIRED in-process contrast, which reproduces to
  ±0.015 ms across tripped and untripped versions.

| session | first pass | after the soaked repeat |
| --- | --- | --- |
| **smem-locality (headline)** | control 0.009, control_lb 0.008, hot16 0.002 — **held** | (not repeated) |
| gmem-locality | 0.014 / 0.029 / 0.011 — **held** | (not repeated) |
| gmem-census | 0.006 / 0.003 / 0.006 — **held** | (not repeated) |
| attr-cv64 | 0.049 / 0.048 — **held** | (not repeated) |
| smem-census | 0.148 / 0.124 / 0.111 — **TRIPPED** | 0.007 / 0.008 / 0.001 — **held** |
| reanchor-locality | control 0.050 — **TRIPPED** | 0.028 / 0.010 — **held** |
| reanchor-census | hot16 0.071 — **TRIPPED** | 0.195 / 0.151 — **TRIPPED again** |
| attr-cv100 | 0.073 / 0.064 — **TRIPPED** | 0.187 / 0.160 — **TRIPPED again** |

- **The top carveout tier is not free, and every contrast must name the tiers it compares.**
  Measured on the incumbent's cached body, 100 KiB costs it +0.295 ms against hint 16 (+0.067 at
  64 KiB); measured on the segmented body, the same request costs +0.116 ms (`s100` − `s64`). An
  arm that asks for the top tier is spending that before it does anything useful — and any A/B
  where the two sides realize different configurations is reporting the tier as well as the
  mechanism.
- **Full Pictures taken under a build freeze have no source correlation.** P1 forbids the rebuild
  the doc's recipe asks for, so `--import-source` is present but `SourceCounters` has no line
  mapping. Per-line attribution of the walk needs its own lineinfo build outside a freeze window.
- **Hold the lock across soak and measurement.** The soak is GPU work; a peer's job interleaved
  with two idle soaks before the switch, and both were refused and re-taken.

### Follow-ups this opens

- **Attack the cohort walk, not the carrier.** +3.690 ms of the loss is the `seg-recompute`
  floor: the cohort loop, the four-warp quarter-lists, the per-cohort epilogue through the shared
  reduction plane, and ~15 block barriers where the incumbent has 1 — all of it SM-bound
  (73–86 % SM SOL). A future segmented attempt has to cut that instruction work; where the coset
  pairs live is settled at ±0.08 ms and cannot pay for it.
- **Group chunking is a corpus-wide dealer requirement** (RR, 2026-08-10). This rung's dealer
  deals whole groups and the default census still balances to 1.08, which is why chopping was
  omitted as a POLICY — the rationale is cost, never semantics: production's seg-VM already
  chops expensive groups into still-valid chunks (the core coeff multiply is paid per chunk), and
  that mechanism is the blueprint. The 1.08 figure is single-census evidence (one circuit, one
  layer, one round) and RR expects chunking to be a MUST across the corpus.
- **The accumulator-first question is answered and closed**: fold-first wins by +0.241 ms
  locality / +0.257 census at matched capture and matched carveout tier, 100/100 both orders.
  Read with the semantic note above.
- **The carveout self-gate should outlive the rung.** `cudaOccupancyMaxActiveBlocksPerMultiprocessor`
  per lane after `cudaFuncSetAttribute` costs nothing at run time, turns the `ARM` line's pinned
  `blocks_per_sm` into a verified fact, and would have caught the Part-I defect before any
  session was dispatched.

### Artifacts and branch state

`.agents/sdd/2026-08-10-v3-r7/`: the emitter records **`r7-tables-repeat.md` (primary)** and
`r7-tables.md` (first pass); the eight canonical
`session-{reanchor-census,reanchor-locality,smem-locality,smem-census,gmem-locality,gmem-census,attr-cv64,attr-cv100}.log`
plus the four `session-*-repeat.log`, each with `.telemetry` / `.warm` / `.mark` sidecars; the
soak-procedure history (`session-reanchor-census-cold.*`, `tuning-worksoak{80,150}-*`,
`tuning-nosoak-*`); G0 (`g0b-*`, and the Part-I abort evidence `g0-*` + `g0diag-*`); the dynamic
ladder (`ladder-*`); `full-*.log` and `counters-*.log`; the ledger `progress.md` and the
measurement report `task-7-report.md` (Part I = the abort, Part II = the result).

`target/profiling/ncu/`: `20260811_1341*_v3r7b_g0_*` (6 G0 points),
`20260811_1434-1437*_v3r7_full_*` (10 Full Pictures), `20260811_1437-1440*_v3r7_counters_*` (7
counter captures); the Part-I abort captures `*_v3r7_g0_*` and `*_v3r7_g0diag_*` are retained.

R7 is twelve `gkr_uniskip_bench` commits, `677fc03d`..`29e36e34`, on top of the R6 record; the
frozen session binary is `fabf2b5b…` at tip `29e36e34`.

### Addendum: ncu attribution of the walk floor (post-rung, 2026-08-11)

Question (RR): where does the ~2 ms structure cost actually go? Measured on the ncu-locked
pair `seg-recompute` (18.05 ms, 43.84 G cycles) vs a fresh matched `control_lb@128` Full
Picture (16.60 ms, 38.70 G cycles; `20260811_152907_v3r7_full_control_lb.ncu-rep` — locality,
doc recipe, lineinfo-free; the locked delta 1.45 ms compresses the timed 2.02 ms, ratios
consistent). Total warp-cycle delta +13.5 %, split two ways:

- **~58 % is added work**: +1.48 G executed instructions (+7.9 %, 20.30 G vs 18.82 G) — the
  four per-cohort epilogues (eq in all four warps, xor folds, shared-plane round-trip,
  partials read-modify-write) plus the 4x restarted quarter-list walk.
- **~42 % is slower issue**: warp cycles per issued instruction 10.71 -> 11.27, eligible
  warps per scheduler 2.11 -> 1.70. The stall states that grow are `barrier` (+~0.7
  cycles/issue; 11 block-wide barriers vs 1, each waiting on the slowest list) and
  `short_scoreboard` (+0.87; the epilogues' shared-memory plane round-trips). The states
  that shrink (`math_pipe_throttle` -0.58, `not_selected` -0.49, `long_scoreboard` -0.39)
  are density states - the control is simply busier doing math.

SM throughput is nearly unchanged (80.3 vs 82.6 %): the segmented shape does not hit a
different pipe, it adds instructions and synchronization on the same one. Any walk-floor
attack has two named targets: the per-cohort epilogue (amortize the reduction across
cohorts, e.g. keep running cell partials in registers where the 72-reg budget allows) and
the barrier count (fewer, wider cohorts trade slab size against sync).

## v3 R7b — the direct transplant (segb)

R7 kept 16 rows in flight per block and walked them in four sequential *cohorts*, merging the
four warps' quarter-sums through a shared reduction plane at the end of each one — and that
cohort machinery cost more than the restructuring saved. R7b is the version RR specified
directly: "let each warp write out the result independently to make it simple." A block now owns
exactly one warp-worth of rows — **four rows, not sixteen** — its four warps produce the cached
coset sources once into a slab they share (one fill barrier; the empty-plan floor lane has none
at all), each warp then walks its quarter of the 175-record term list, and **each warp writes its
own partial straight out**. No shared reduction plane, no read-modify-write accumulator, no
cohort loop: everything R7 spent on merging is deleted, and nothing is recomputed. What that
buys in simplicity it pays for in shape — the same trace now needs **4× the blocks** (262,144
against 65,536), and the finalize kernel that reduces the partials sees **16× the slots**
(1,048,576 against 65,536: four per block instead of one). Only the device-scratch carrier is
carried forward (R7 settled the medium question at ±0.08 ms — that figure is quoted from the R7
section above, not from this rung's own sources), plus one rider RR cleared
mid-rung: a **slotted slab**, where a block claims its slab region out of a small
software-managed pool addressed by the SM id it is running on (`%smid`; 1,024 SM ids × 16 slots
× one slab each) instead of owning a private region per block in the grid. The pool is small
enough to stay L2-resident, so it is the direct test of whether R7's scratch write stream is
worth removing at all.

**R7b preregisters no closure threshold**, inheriting R7's ruling: every arm is a datapoint about
where the optimum lies, and nothing here declares a winner. The baseline is the same `hot16@128`
incumbent with the R6 carveout hint baked in (best-vs-best).

**Headline: no transplant lane beats the incumbent, and it loses by more than R7's segmented arm
did.** THE VERDICT row — `segb-hot16-g@128 − hot16@128`, paired per round on `eval + finalize` —
is **+2.766 ms on locality (96/96 sign-stable)** and **+2.212 ms on census (96/96)**, against
R7's own gmem arm at +1.909 ms. The cohort epilogues are gone and the walk floor still did not
drop: it is **+0.168 ms (locality) / +0.195 ms (census)** *above* R7's in the body, and
**+1.017 / +1.040 ms** above it once the 16× finalize the transplant creates is paid. The cost
did not disappear; it moved into block count and finalize.

Provenance, stated once. Every **timing** table below is copied cell-by-cell from the emitter
record `.agents/sdd/2026-08-11-v3-r7b/r7b-tables.md`; the **configuration, profiler and counter**
tables come from the measurement report `.agents/sdd/2026-08-11-v3-r7b/task-4-report.md`. No
timing number here was assembled by hand. Four timed processes (two 2-lane re-anchors, the 8-lane
SEGB rotation at both term orders, 96 rounds × warmup 8) plus one soaked repeat, all on one
frozen binary (`0e89690e…` at tip `172edebb`), all under `.agents/bin/with_gpu_lock.sh`, all
using R7's soak procedure (80 s of discarded work in the same lock hold).

### The arms — per-lane medians (`eval`, `finalize`, `eval + finalize`, ms)

| position | lane | eval | finalize | eval+finalize |
| --- | --- | --- | --- | --- |
| segb-locality | `control@256` | 16.548 | 0.033 | **16.581** |
| segb-locality | `control_lb@128` | 16.252 | 0.061 | **16.312** |
| segb-locality | `hot16@128` | 14.599 | 0.063 | **14.663** |
| segb-locality | `segb-recompute@128` | 18.436 | 0.908 | **19.344** |
| segb-locality | `segb-cache0-g@128` | 18.287 | 0.910 | **19.199** |
| segb-locality | `segb-hot16-g@128` | 16.504 | 0.914 | **17.420** |
| segb-locality | `segb-k40-g@128` | 16.240 | 0.916 | **17.155** |
| segb-locality | `segb-hot16-g-slotted@128` | 16.691 | 0.909 | **17.600** |
| segb-census | `control@256` | 16.673 | 0.033 | **16.706** |
| segb-census | `control_lb@128` | 16.335 | 0.061 | **16.397** |
| segb-census | `hot16@128` | 15.088 | 0.063 | **15.151** |
| segb-census | `segb-recompute@128` | 18.559 | 0.908 | **19.470** |
| segb-census | `segb-cache0-g@128` | 18.424 | 0.908 | **19.334** |
| segb-census | `segb-hot16-g@128` | 16.453 | 0.916 | **17.369** |
| segb-census | `segb-k40-g@128` | 16.307 | 0.916 | **17.223** |
| segb-census | `segb-hot16-g-slotted@128` | 16.509 | 0.908 | **17.416** |

`segb-recompute` is the machinery floor (empty plan, nothing captured, nothing published),
`segb-cache0-g` publishes a slab with zero sources admitted, `segb-hot16-g` captures R5's
frontier set (16 admitted sources, C = 28 slab units), `segb-k40-g` captures 40 (C = 52) and
`segb-hot16-g-slotted` is the same capture on the slotted pool. The `census` rows are the
dealing-damage diagnostic and are never pooled with `locality`.

### The decision rows — paired per round, inside one process

Sign-stability is the count of rounds on the median's own side, against ceil(0.9 · 96) = 87.

| position | contrast | isolates | median Δ (ms) | per removal | sign-stability |
| --- | --- | --- | --- | --- | --- |
| segb-locality | `segb-cache0-g` − `segb-recompute` | publish machinery at zero capture | **−0.149** | — | 95/96 neg (≥ 87) |
| segb-locality | `segb-hot16-g` − `segb-cache0-g` | capture at hot16 | **−1.786** | — | 96/96 neg (≥ 87) |
| segb-locality | `segb-hot16-g` − `hot16@128` | **THE VERDICT** — transplant vs incumbent | **+2.766** | — | 96/96 pos (≥ 87) |
| segb-locality | `segb-k40-g` − `segb-hot16-g` | the capture slope | **−0.266** | −5.55 µs (48 removals) | 96/96 neg (≥ 87) |
| segb-locality | `segb-recompute` − `control_lb@128` | the walk floor | **+3.037** | — | 96/96 pos (≥ 87) |
| segb-locality | `segb-hot16-g-slotted` − `segb-hot16-g` | slotted-slab footprint / L2 | **+0.178** | — | 96/96 pos (≥ 87) |
| segb-census | `segb-cache0-g` − `segb-recompute` | publish machinery at zero capture | **−0.144** | — | 96/96 neg (≥ 87) |
| segb-census | `segb-hot16-g` − `segb-cache0-g` | capture at hot16 | **−1.969** | — | 96/96 neg (≥ 87) |
| segb-census | `segb-hot16-g` − `hot16@128` | **THE VERDICT** | **+2.212** | — | 96/96 pos (≥ 87) |
| segb-census | `segb-k40-g` − `segb-hot16-g` | the capture slope | **−0.144** | −3.00 µs (48 removals) | 96/96 neg (≥ 87) |
| segb-census | `segb-recompute` − `control_lb@128` | the walk floor | **+3.074** | — | 96/96 pos (≥ 87) |
| segb-census | `segb-hot16-g-slotted` − `segb-hot16-g` | slotted footprint / L2 | **+0.044** | — | **84/96 pos (< 87)** |

The publish machinery at zero capture is *negative* and small (−0.144/−0.149), so on this body
the publish path costs nothing measurable before anything is captured.

### The walk floor, in both currencies (A4)

The floor lane runs the transplant body with an empty plan, so floor − `control_lb@128` is what
the restructured walk costs over the uncached control. It is reported twice because the
transplant's finalize is 16× the slots: `eval` alone is the body floor, `eval + finalize` is what
a transplant would actually pay. Every row is paired inside its own session.

| rung | position | currency | median Δ (ms) | sign-stability |
| --- | --- | --- | --- | --- |
| R7b | segb-locality | body floor (eval only) | **+2.188** | 96/96 pos (≥ 87) |
| R7b | segb-locality | transplant floor (eval + finalize) | **+3.037** | 96/96 pos (≥ 87) |
| R7b | segb-census | body floor (eval only) | **+2.229** | 96/96 pos (≥ 87) |
| R7b | segb-census | transplant floor (eval + finalize) | **+3.074** | 96/96 pos (≥ 87) |
| R7 | r7-gmem-locality | body floor (eval only) | **+2.020** | 99/99 pos (≥ 90) |
| R7 | r7-gmem-locality | transplant floor (eval + finalize) | **+2.020** | 99/99 pos (≥ 90) |
| R7 | r7-gmem-census | body floor (eval only) | **+2.034** | 99/99 pos (≥ 90) |
| R7 | r7-gmem-census | transplant floor (eval + finalize) | **+2.034** | 99/99 pos (≥ 90) |

R7's two currencies are identical because its floor lane and its control both publish one slot
per block; only the transplant separates them. The rung-over-rung comparison is the difference of
the two in-session differentials — never a raw cross-session subtraction:

| order | currency | R7b Δ | R7 Δ | R7b − R7 |
| --- | --- | --- | --- | --- |
| `locality` | body floor (eval only) | +2.188 | +2.020 | **+0.168** |
| `locality` | transplant floor (eval + finalize) | +3.037 | +2.020 | **+1.017** |
| `census` | body floor (eval only) | +2.229 | +2.034 | **+0.195** |
| `census` | transplant floor (eval + finalize) | +3.074 | +2.034 | **+1.040** |

**Removing the cohort epilogues did not lower the floor.** In the body it rose slightly
(+0.17/+0.20 ms — the same math over 4× as many blocks), and the 16× finalize adds the rest.
That finalize costs a **flat ≈ +0.85 ms** on every transplant lane (0.908–0.916 ms against
0.061–0.065 ms on a 16-row lane, see the arms table — identical whichever carrier or capture the
eval used). The profiler agrees exactly: the finalize kernel reads **33,554,432 L1 load sectors
and 536.88 MB from DRAM in every transplant arm** against 2,097,152 sectors / 33.56 MB on a
16-row lane — **16.0× on both counters** — and ncu measures it at 897–919 µs, matching the
session medians. It is a pure bandwidth stage (1.2 % SM SOL, ~37 % DRAM SOL, 16.7 % occupancy):
a fixed tax of the four-rows-per-block geometry, not of any carrier choice.

### Capture economics — the slope inverted, on two points

Capture is still worth a lot on this body: admitting R5's 16 sources refunds **−1.786 ms**
(locality) / **−1.969 ms** (census) against the same body with nothing admitted. What changed is
the direction past that point. R7 measured a *positive* capture slope on both its carriers
(+8–12 µs per additional removal, i.e. `hot16` was the frontier optimum); on the transplant,
`segb-k40-g − segb-hot16-g` is **−0.266 ms = −5.55 µs per removal on locality** and −0.144 ms =
−3.00 µs on census, both 96/96 — more capture is now *cheaper* on this body. State it for what it
is: a **two-point claim**. R7b's matrix carries only `hot16` and `k40`; k24 and allrepeat were
not run here, and K17–23 remains unmeasured in every rung. It is a hint about where the optimum
would sit if this geometry were pursued, not a law — and it rescues nothing, since `k40` is still
+2.500 ms above the incumbent.

### The slotted lane — the footprint fix works, and buys nothing here

`segb-hot16-g-slotted` runs the identical admitted set and the identical publishes; only the
region map changes (a claimed pool slot per resident block instead of a private region per grid
block). Kernel-wide `--metrics` differentials, one round each:

| counter | `segb-hot16-g` | `segb-hot16-g-slotted` | differential |
| --- | --- | --- | --- |
| `dram__bytes_op_write.sum` | 2.38 GB | 531.98 MB | **−1.848 GB (−98.3 % of the slab floor)** |
| `dram__bytes_op_read.sum` | 6.18 GB | 6.18 GB | **0** |
| `l1tex__t_sectors_…_op_st.sum` | 75,497,472 | 75,497,472 | **0** |
| `l1tex__t_sectors_…_op_ld.sum` | 1,107,296,256 | 1,107,296,256 | **0** |
| `lts__t_sectors_op_write.sum` | 75,508,274 | 75,515,417 | +7,143 |
| `lts__t_sectors_op_read.sum` | 684,167,359 | 672,170,700 | −11,996,659 |
| L2 hit rate (Full Picture) | 64.64 % | **71.93 %** | +7.29 pp |
| DRAM SOL (Full Picture) | 33.92 % | **26.11 %** | −7.81 pp |

The L1 traffic is **bit-identical** — same loads, same stores, to the sector — and the scratch
stream's DRAM writes essentially vanish: 531.98 MB is within **1.08 MB (0.057 % of the slab
floor)** of the `segb-recompute` lane that publishes nothing at all. The pool touches at most
21.6 MB (16 slots × 188 SMs × 7,168 B) of the 117.4 MB allocated, small enough that every slab
line is overwritten before it can be evicted; that 21.6 MB is a bound rather than a measured
residency, because `%smid` is virtualized. **And it costs +0.178 ms** (96/96 locality; +0.044 and
below the sign threshold on census). The Full Pictures say why nothing came back: every
transplant arm is **SM-bound — 72–80 % SM SOL against 23–41 % DRAM SOL** — so the scratch write
stream was never the binding resource in this kernel family. The allocator itself works as
designed and is the reusable artifact: claim and release verified on hardware at the measurement
tip (no trap, slot mask all-clear, occupancy hard-gated at exactly 7 blocks/SM against 16 slots).

### Scratch accounting — the grid slab closes at the arithmetic floor

Arithmetic floor = slab bytes per block × blocks, with **no cohort factor** (each region is
written once, within one block's four-row pass); slab = C units × 256 B over 262,144 blocks:

| capture point | C | slab / block | blocks | write floor | in 32-B sectors |
| --- | --- | --- | --- | --- | --- |
| hot16 | 28 | 7,168 B | 262,144 | 1,879,048,192 B = **1.879 GB** | 58,720,256 |
| k40 | 52 | 13,312 B | 262,144 | 3,489,660,928 B = **3.490 GB** | 109,051,904 |

Measured on the eval kernel, minus the `segb-recompute` floor lane:

| counter | hot16 − recompute | vs floor | k40 − recompute | vs floor |
| --- | --- | --- | --- | --- |
| `l1tex__t_sectors_…_op_st.sum` | 75,497,472 − 16,777,216 = **58,720,256** | **1.0000×** | 125,829,120 − 16,777,216 = **109,051,904** | **1.0000×** |
| `lts__t_sectors_op_write.sum` | 75,508,274 − 16,781,210 = 58,727,064 | 1.00012× | 125,841,009 − 16,781,210 = 109,059,799 | 1.00007× |
| `dram__bytes_op_write.sum` | 2.38 GB − 530.90 MB = **1.849 GB** | **0.984×** | 3.98 GB − 530.90 MB = **3.449 GB** | 0.988× |
| `dram__bytes_op_read.sum` | 6.18 GB in **every** arm | unchanged | 6.18 GB | unchanged |

The write differential equals the arithmetic floor **to the sector, 1.0000×**, with no cohort
factor — the direct confirmation that a transplant block publishes its slab once and reads it
back inside its own four-row pass. The number that changed versus R7 is where those bytes go:
**98.4 % of the published bytes reach DRAM here** (1.849 GB of 1.879 GB; 98.8 % at k40), against
**24.4 % in R7**. R7's four-cohort reuse rewrote each block's slab four times into the same
region and L2 absorbed three quarters of it; R7b's 4-row regions, spread over 4× the blocks, are
written once and there is nothing left to absorb. The transplant converted an L2-resident write
stream into a DRAM write stream of the same nominal size — which is exactly what the slotted lane
then removed again, for no time.

### Portable finding — the carveout ladder is body-dependent a third time

The realized-configuration gate (G0) requires every arm on a decision row to run the same
shared-memory/L1 partition, so a partition difference cannot masquerade as a carrier or capture
effect. The pre-freeze probe found the slotted symbol was **not** equalized with its siblings,
despite carrying the same hint percentage:

| hint | `segb-g` / `segb-recompute` (0 B static shared) | `segb-g-slotted` (4 B static shared) |
| --- | --- | --- |
| 0 | 32.77 KB | **8.19 KB** |
| 1 | — | 16.38 KB |
| **2** | — | **32.77 KB** |
| 4 | — | 65.54 KB |
| 6 | — | 65.54 KB |
| 8 | 32.77 KB | 102.40 KB |
| **16** | **32.77 KB** | 102.40 KB |
| 33 | 65.54 KB | 102.40 KB |
| 50 | 65.54 KB | 102.40 KB |
| 66 | 102.40 KB | — |
| 100 | 102.40 KB | 102.40 KB |

**Four bytes of static shared memory compress the whole ladder by roughly 8×.** At the
placeholder hint of 16 the slotted body realized **102.40 KB** where its zero-shared sibling
realizes **32.77 KB** — a ~77 KB partition difference sitting directly under the slotted decision
row. Equal *percentages* did not equalize the *configuration*. The fix (commit `172edebb`, taken
before the freeze) pins the slotted symbol at hint 2, the same 32.77 KB tier; G0 then passed 4/4
at one equalized configuration, all four arms register-bound at 7 blocks/SM. This is the third
independent datapoint that the hint→configuration ladder belongs to the body, not to the kernel
family: R6 mapped it on a static-shared body, R7 found it did not transfer to a dynamic-shared
one, and R7b finds four static bytes are enough to move it again. Nothing in-process observes the
realized partition, so the probe has to be re-run per rung — and the pin is a measured percent
for this driver on this part, not a derivable one.

### Instrument notes

- **The flank rule was rescaled for this rung, and nothing trips it.** The flank check compares
  the first and last full rotation cycle of each anchor lane; R7's flat 0.05 ms threshold is
  replaced by max(0.05 ms, 0.5 % of that lane's session median). Under it, all ten anchor lanes
  hold, the two decision-carrying SEGB rotations by an order of magnitude (0.004–0.037 ms against
  thresholds of 0.073–0.084). The emitter still carries R7's flat constant and prints
  `REPEAT TRIGGER FIRED` for one lane at Δ 0.058 — that line is a cosmetic lag in the tool, not a
  finding; the numbers in its table are the ones the scaled rule was applied to.
- **The 2-lane anchor rotation's flank artifact reproduced exactly.** That session was re-run in
  full, soaked, anyway: its session medians reproduce the original to **0.002 ms / 0.001 ms**
  while its flank came out *worse* (0.095 against 0.058). Same conclusion as R7 — the short
  anchor rotation cannot hold a tight flank on this part, and it is an instrument property, not a
  data problem. The two emitter outputs differ only in the re-anchor and flank sections; every
  decision row and walk floor is byte-identical.
- **Absolutes on the census order are session-scoped.** `control@256` came in **+2.25 %** off its
  frozen R4 anchor (out of the ±2 % band); the locality order — the headline — is in band on both
  anchor lanes. Every decision row is paired inside one process and is unaffected.
- **Full Pictures are lineinfo-free**, unavoidable under the build freeze (the recipe wants a
  rebuild). Per-line attribution of the transplant walk needs its own lineinfo build.

### Follow-ups this opens

- **Chunking is a corpus-wide MUST for any production segmented dealer** (RR's ruling, carried
  from R7). The imbalance this rung's dealer shows is single-circuit, single-layer, single-round
  evidence; a real dealer has to chop expensive groups into still-valid chunks, and production's
  seg-VM already has that mechanism.
- **K17–23 remains unmeasured on the capture axis**, in this rung as in R5/R6/R7 — and the
  transplant's inverted slope makes it more interesting, not less, if this geometry is ever
  pursued. Two points do not locate an optimum.
- **The slotted allocator is available to any future lane whose scratch really is DRAM-bound.**
  It removes ~98 % of a scratch stream's DRAM writes for ~0.18 ms of claim work, with L1 traffic
  untouched. It bought nothing here only because this kernel family is SM-bound.

### Addendum: the slotted allocator's machinery, record-only (A9b)

Carried from this rung's two build reports — `.agents/sdd/2026-08-11-v3-r7b/task-1-report.md`
(the Task 1b sections) and `task-2-report.md`. None of it changes a figure above; all of it is
inside what the `segb-hot16-g-slotted` lane measured (one exception: the k40 pool figure below
is a projection — the slotted lane is pinned hot16-only), which is why it is recorded rather
than chased.

- **The pool sizes at two tiers.** 16,384 regions (1,024 SM ids × 16 slots) × the arm's
  slab stride: **117.4 MB at hot16** (7,168 B, the tier the lane ran — measured/allocated) and
  a projected **218.1 MB at k40** (13,312 B; never allocated — the slotted lane supports hot16
  only), plus the 4 KB mask; the host prints the pool figures on the prepare path. The **≈21.6 MB touched**
  (16 slots × 188 SMs × 7,168 B) is a BOUND on what the hot16 tier can reach, not a measured
  residency — it counts `multiProcessorCount`, and the id it is keyed to is virtualized.
- **`%smid` lowers to `SR_VIRTUALSMID`.** Under MPS/MIG that is the virtualized id. It stays
  unique per resident SM within the process, which is all the allocator needs, but the mask's
  occupied bits are a residency bound and NOT an SM-utilization readout.
- **The claim CAS lowers to `.SYS` scope** (`ATOMG.E.CAS.STRONG.SYS`, generic addressing) while
  the release keeps `.GPU` with global-descriptor addressing. An nvcc lowering artifact, not a
  correctness issue — SYS is the stronger scope. `__restrict__` on the mask pointer did not
  move it; only a PTX-level `atom.global.cas` would. One SYS atomic per block sits inside every
  slotted timing here.
- **The release is a returning `ATOMG.E.AND.STRONG.GPU`, not a `RED` reduction.** The kernel
  binds the `atomicAnd` result (the owned-bit assert reads it), so the returning form is emitted
  in the shipped build too. Two atomics per block total, both part of the +0.178 ms the slotted
  row prices.
- **`SHARED:8` for a 4-byte publish variable.** The body declares exactly one `__shared__ u32`;
  8 B is ptxas's shared allocation granularity and is what the SASS gate pins. Those four bytes
  are also what moved the carveout ladder — see the portable finding above.
- **Region arithmetic is 32-bit-safe by construction.** Largest region index × slab stride =
  16,383 × 5,632 ≈ **92.3 M words**, 46.5× (2.15 % of 2³²) below the u32 wrap that the
  grid-indexed `segb_g` has to reason about; the host adds a `prepare_seg` assert on top.

### Artifacts

`.agents/sdd/2026-08-11-v3-r7b/`: the emitter records `r7b-tables.md` (primary) and
`r7b-tables-repeat.md`; the sessions `segb-{reanchor-census,reanchor-locality,locality,census}.log`
plus `segb-reanchor-census-repeat.log`, each with `.telemetry` / `.warm` / `.mark` sidecars;
`segb-binary.sha`, `prefreeze-gates.log`, `diag-slotted-validation.log`; G0 and the hint-ladder
probes (`g0b-*`, `g0-*`, `g0probe-*`, `g0diag*-*`); `full-*.log` and `counters-*.log`; the ledger
`progress.md` and the measurement report `task-4-report.md`. Profiler captures under
`target/profiling/ncu/` as `*_v3r7b_*`. The frozen session binary is `0e89690e…` at tip
`172edebb`.
