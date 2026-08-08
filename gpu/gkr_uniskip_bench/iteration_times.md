# gpu_gkr_uniskip_bench — measurements

## Register gate (Task 4; refreshed in Task 5 for fold, in v2 Task 0 for row-shape LDE, in v2 Task 1 for the fused eval)

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
| `ab_gkr_uniskip_eval_fused_kernel` | 64 | 68 | 64 | 64 | 0 / 0 / 0 |
| `ab_gkr_uniskip_eval_fused_interleave_kernel` | 125 | 202 | 134 | 134 | 0 / 0 / 0 |
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

### Occupancy (corrects the Task 4 entry)

The Task 4 text claimed 55 registers "still reaches full occupancy on every listed
architecture". That is **wrong**. Blocks are 256 threads, so a block costs
`256 × regs` of the SM's 65536-register file, and full occupancy needs
`regs <= 32` on sm_80/sm_90 (2048 threads/SM) — no kernel of this bench that
matters is there.

| kernel | sm_80 | sm_89 | sm_90 | sm_120 |
| --- | --- | --- | --- | --- |
| `eval` | 4 blk, ~50% | 5 blk, ~83% | 5 blk, ~62.5% | 4 blk, ~67% |
| `eval_fused` | 3 blk, ~37.5% | 4 blk, ~67% | 4 blk, ~50% | 4 blk, ~67% |
| `eval_fused_interleave` | **1 blk, ~12.5%** | **1 blk, ~17%** | **1 blk, ~12.5%** | **2 blk, ~33%** |
| `fold_e4` | 6 blk, ~75% | 5 blk, ~83% | **2 blk, ~25%** | **2 blk, ~33%** |
| `fold_bf` | ~100% | ~100% | ~100% | ~100% |
| `lde_e4_row` | 8 blk, ~100% | 6 blk, ~100% | 6 blk, ~75% | 6 blk, ~100% |
| `lde_bf_row` | 4 blk, ~50% | 4 blk, ~67% | 4 blk, ~50% | 4 blk, ~67% |

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
| `eval_fused` after | 11816 | **3626 (−38.8 %)** | **1836 (unchanged)** | 681 (unchanged) |
| `eval_fused_interleave` before | 18512 | 5596 | — | 517 |
| `eval_fused_interleave` after | 10760 | **3496 (−37.5 %)** | — | 517 (unchanged) |
| `eval_kernel` (unfused) | 2861 | 903 | — | 41 |

The unfused kernel's SASS is **byte-identical** across the two builds, so the change
is confined to the fused accessor. The wide-multiply count is unchanged and the load
count is unchanged: the −38 % is the reduction chain and nothing else, which is what
"chunking removes reductions, not multiplies" predicts.

**F9, checked while in the SASS: ptxas does NOT strength-reduce the per-tap address
chain.** Each tap load still recomputes `((plane + t) << log_rows) + row` in full —
`IADD` (plane+t), `SHF.L` (<< log_rows), `IADD` (+row), `IMAD.WIDE.U32` (×4, + base)
— instead of hoisting a base and stepping by the runtime stride `1 << log_rows`.
Measured in the shipped `eval_fused` body: 712 address-scaling `IMAD.WIDE` (one per
`LDG`) and 695 `SHF.L`, against 3626 total `IMAD`. So **~20 % of the remaining
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
