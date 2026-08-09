# gpu_gkr_uniskip_bench

Standalone CUDA benchmark for one **uniskip** sumcheck pass. It is off the `gpu/`
crate DAG: nothing depends on it, and it depends on no *prover* crate — its only
dependencies are `era_cudart`/`era_cudart_sys`, `clap` and `field`, plus `gpu_core`
as a **dev-dependency** (solely for the `force_serial_libtest!` guard the cluster's
testing contract requires at every GPU crate root) and `gpu_native_build` as a
build-dependency. Its CUDA lives in its own archive,
`gpu_gkr_uniskip_bench_native`, namespace `airbender::gkr_uniskip_bench`. Kernel
shapes can therefore be iterated on without building the prover stack.

## Execution shape

One pass, with the skip factor **k fixed at 4**, runs four stages on a single
stream:

| stage | kernels | what it does |
| --- | --- | --- |
| `lde` | `lde_bf`, `lde_e4` | extends every column's 16 taps on `H` to the 16 cells of the odd coset `gamma*H` |
| `eval` | `eval` | walks the term program at all 32 cells for every row, weights by `eq`, reduces to one `e4` per (block, cell) |
| `finalize` | `finalize` | sums the block partials into the 32 evaluations `q` |
| `fold` | `fold_bf`, `fold_e4` | collapses the 16 taps into the evaluation at the round challenge `r` |

`--mode` picks how the coset cells are produced. `unfused` (the default) is the
table above. `fused-recompute` deletes the `lde` stage and the coset backing
outright: the eval accessor extends the taps on read, so the pass is one kernel plus
`finalize` plus `fold`, and the device holds 1× the backing instead of 2×.
`fused-cached` keeps that and adds a fixed shared-memory assignment, so the hottest
sources' coset cells are produced once per row tile instead of once per reference.
All three modes produce the same `q`.

`lsb-recompute` (v3 R0), `lsb-compact` (v3 R1) and `lsb-pair` (v3 R2) are a different
architecture, not further points on that ladder — see [The LSB mode](#the-lsb-mode-v3-r0) below. Its `q` is
deliberately *not* the same as the other three modes': the same init generator over a
different element ordering gives different operand data, so it carries its own oracle
leg rather than a shared expected value.

`--term-order` reorders the record stream — `census` (the default) is emission order,
`locality` is the permutation that clusters records reading the same sources. It is a
program property, legal in every mode, and it changes only which order operands are
touched in; `q` is a sum of per-term contributions in `bf`/`e4`, so both orders give
bit-identical results.

### Modes, and which one to run

All numbers below are medians at `--log-trace 24` on an RTX PRO 6000 Blackwell over
`--warmup 10 --iterations 100`, from `iteration_times.md`; all 12 arms of the **v1/v2**
matrix pass `--validate` and `--validate-flat-eq` (that 24-cell matrix is what is
tabulated there). Counting the v3 modes the crate has **20** legal arms: 12 here, plus
`lsb-recompute` x 2 term orders (2), plus `lsb-compact` x 2 group counts x 2 term orders
(4), plus `lsb-pair` x 2 term orders (2) — 12 + 2 + 4 + 2 = 20, or 24 if `--bank-perm`'s
second value is counted as a shape rather than an A/B control. The v3 arms carry their own
validation records in the *v3 R0*, *v3 R1* and *v3 R2* sections. `--pair-arm`'s five
non-default values add **10** further legal combinations (5 x 2 term orders) on top of
those 20; they are R3 diagnostic arms rather than candidate shapes, and none of them beats
the default — see [The window arms](#the-window-arms-v3-r3--diagnostic-not-candidates).
`pass − fold` is `lde + eval + finalize` — the
part the modes actually change, since `fold` is identical work everywhere (its
challenge depends on `q` through the transcript, so it cannot be fused) and is already
running at its own bandwidth floor.

| mode flags | coset cells come from | resident backings | `pass − fold` | when to use it |
| --- | --- | --- | --- | --- |
| **`--mode fused-cached --cell-map interleave --term-order locality`** | a shared 32 KB pool (16 units) holding 10 planned sources' slabs; recompute for the rest | **5.75 GiB** | **23.078 ms** | **the recommendation** |
| `--mode fused-recompute --cell-map interleave` | recomputed on every read | 5.75 GiB | 28.101 ms | the no-shared-memory fallback |
| `--mode unfused --lde-shape row` (the CLI default) | a materialized coset buffer, row-shaped LDE | 11.50 GiB | 28.078 ms | the control arm; the recommended shape of the mode that carries a live LDE validation leg |
| `--mode unfused --lde-shape cell` | ditto, v1 grid (16× tap re-read) | 11.50 GiB | 90.462 ms | the v1 control, kept unaltered; same live LDE validation leg |

**Within the v1/v2 ladder the recommendation is `fused-cached` + `interleave` +
`locality`.** (The crate's fastest arm overall is v3's `--mode lsb-pair`; the v3 R0 and
R2 arms beat this one — see [The pair mode](#the-pair-mode-v3-r2--the-recommended-v3-arm).) It is
the fastest of the twelve arms below (3.92× the v1 pass on `pass − fold`, 3.42× on the full pass, 1.22× the
best unfused arm), on the smallest device footprint (half the backing, because no coset
is materialized), with issued DRAM traffic at 1.008× the compulsory floor — and within
the interleaved pair it is also the better register/occupancy point (66 registers, 3
blocks/SM, zero spills, against `fused-recompute --cell-map interleave`'s 125 / 2).
It is not best on *every* axis: the block-map `fused-recompute` kernel is 64 registers
and 4 blocks/SM, better on both, and 11.37 ms slower — occupancy is not what orders
these arms. `--cell-map block` and `--term-order census` are the v1-shaped settings of
those two knobs; both are measured and neither wins here.

**The CLI default is deliberately not the recommendation.** A bare run reports
`--mode unfused --lde-shape row`, which is the reference pass the ladder is measured
against *and* an arm of the unfused mode — the only mode that materializes a coset, so
the only one where `--validate`'s LDE check compares real buffers instead of reporting
`n/a`. Both `--lde-shape` arms carry that leg; `row` is the recommended shape, and the
default, because it is 8.2× faster on `lde` than `cell`.

The one reason to prefer `fused-recompute` is shared memory: the cached kernels need
33792 B per block to fit three blocks on an sm_120 SM, and 17 pool units would already
drop that to two. A heavier census or a part with a smaller shared budget can put the
cached mode over that cliff, which `iteration_times.md` measures.

### The LSB mode (v3 R0)

```bash
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench \
    --log-trace 24 --warmup 10 --iterations 100 --mode lsb-recompute --term-order locality
```

`--mode lsb-recompute` implements the R0 rung of the v3 LSB lane-striped design (spec
dated 2026-08-08, not committed — `iteration_times.md` restates every number this mode
is measured against). It shares the program,
the census, the coefficient bank, the `eq` tables and the `finalize` kernel with the
modes above and changes everything else:

- **Layout.** A column's element offset is `(logical_row << 4) | tap` instead of
  `row + (tap << log_rows)`, so the 16 taps of one logical row are 16 *adjacent*
  elements — a **group**. Window packing, backing sizes and the addressing bound are
  unchanged; only the within-column ordering differs. There is no coset backing.
  `abi::lsb_source_offset` is the host mirror, reached through
  `Layout::source_offset`, and asking it for a coset cell is a panic, not a fallback.
- **Lane map.** 256 threads = 8 warps; a **16-lane half-warp is one group** with
  **lane = tap**, so a warp owns two groups and a block covers 16 logical rows (grid
  `rows / 16`, twice the other modes'). Lane `t` owns two cells: `H` cell `t`, which is
  the tap it already loaded, and coset cell `16 + t`, which it produces. Two `e4`
  accumulators per lane against the other modes' four. The map is fixed at this rung,
  so `--cell-map` is rejected — as is `--lde-shape`, since there is no LDE stage.
- **Producer.** Every reference loads its group (one coalesced 64 B half-warp run for
  `bf`, one `v4.u32` per lane = 256 B for `e4`) and runs a **shuffle-NTT** across the
  half-warp: iDIF with `omega^-1` → folded normalize+twist → DIT with `omega`, 8
  `shfl_xor` exchange stages and 7 generic multiplies per component pass. `e4` sources
  run the identical code path limb-sequentially. The 7 lane-indexed twiddle tables live
  in `__constant__` and are preloaded into per-lane registers at kernel entry in
  source; ptxas rematerializes some of the lane-indexed loads inside the record loop
  under register pressure, so divergent constant reads are reduced, not eliminated
  (this is the ADU signal in the profiles — see `iteration_times.md`, 2026-08-09 audit
  round). Host mirror and derivation:
  `domain::ntt_twiddles` / `domain::coset_from_taps`, pinned bit-for-bit against the
  dense `domain::lde_matrix()` apply by `cpu_factorized_coset_matches_matrix`.
- **W = 0.** Nothing is retained across references — the whole point of the rung is to
  measure the architecture with no scheduler at all. The one exception is a repeated
  operand *inside* one term (`x * x`), which is produced once.

  The default census emits **no** self-product, so that rule is unreachable on a bare
  run; `--self-products <N>` rewrites `N` same-class binary products into `x * x` for
  exactly this purpose and is wired into `--validate`. It is a **validation** knob, not
  a census knob, and it rewrites the *program* only: the census and the cache plan are
  measured once at generation and neither tracks it, so under this knob they are
  **stale** — one reference per rewritten record has migrated from `source_b` to
  `source_a` and the printed figures describe a program that no longer runs. The config
  block labels both `STALE` for exactly that reason, and a timing taken under the knob
  is not comparable with the recorded arms. It also makes the v2/v3 A/B
  **non-work-matched** — `uniskip_eval_body` resolves both operands unconditionally, so
  on a self-product census v2 does two resolutions where this mode does one. That does
  not touch the recorded R0 comparison, which runs the default census at
  `--self-products 0`.
- **Reduction.** Within a half-warp the lanes hold different cells, so a half-warp tree
  would mix them. One `shfl_xor(16)` merges the warp's two groups per cell-slot, then
  eight warps meet in a 4 KB shared plane and write v2's unchanged
  `partials[block][32]` layout.
- **No fold.** The pass is one kernel plus `finalize`. The fold kernels address
  plane-major taps and a low-bit fold is a separate design (the v3 design's R4 rung —
  it reads 16 adjacent inputs and writes one, so it must not fold in place across
  blocks), so `fold` reports
  `0.000` and `fold validate` reports `n/a` — and the mode allocates no fold output
  buffer.

### The compact mode (v3 R1)

`--mode lsb-compact --compact-groups {4,8}` is R0 with a restructured producer: a warp
owns `groups` groups instead of 2, a lane holds `groups / 2` elements (all at one tap),
and the group vectors are staged in **shared memory** so the lane-to-element binding
dissolves. A static, host-built schedule (`src/compact.rs`, uploaded and copied to shared
memory once per block) then packs only the **50 real multiplies** of a group's chain into
`ceil(groups * m / 32)` rounds per stage, instead of the 112 R0 must issue because its
unity twiddles are lane-divergent. Everything else — LSB backing, W = 0, `eq`, `finalize`,
no fold — is R0's.

It is **measured and kept as a control arm, not a recommendation**: the multiply cut is
real (chain multiplies per row −43 % at `groups = 4`, −50 % at 8; `fmaheavy` 81.5 % →
68.7 %) and the pass is **14–15 % slower** than `lsb-recompute`, because the staging moves
the work onto the narrower LSU pipe, which becomes the whole SM speed-of-light at 87 %.
`iteration_times.md`'s *v3 R1* section carries the full record, including the
single-variable bank-permutation A/B that removed 69 % of the conflicts and moved the
wall +0.08 % — the
measurement that identifies the bound as LSU *instruction* issue rather than wavefronts.
Its `q` is bit-exact equal to `lsb-recompute`'s, checked device-to-device with `--dump-q`.

### The pair mode (v3 R2) — the recommended v3 arm

`--mode lsb-pair` is R0 with the butterfly's two halves **in the same lane**. R0 binds
lane = tap, so a stage's two halves are lane-divergent and it must be written as a select
plus an unconditional multiply — unity on half the lanes, unskippable. Pair-resident, the
stage is `lo = u + v; hi = (u - v) * w`, and the low output's unity multiply **is never
written**: no shared memory, no schedule table, no predication.

A group's 16 taps live on 8 lanes at 2 per lane, a warp holds 4 groups, and a block covers
**32 logical rows** (twice R0's decode amortization). Between stages each lane keeps one
output and trades the other — one `shfl_xor` per re-pair, masks 4, 2, 1, 1, 2, 4 — and the
chain ends on the map it started on, so `H` and the coset share one layout. Derivation,
the host executor and its mutation checks: `src/pair.rs`.

**It is the fastest arm this crate has measured**: **16.283 ms** `eval + finalize`
(locality) against R0's 20.596 (**−20.9 %**) and v2's best 23.078 (**−29.4 %**), at 64
issued multiplies per group against R0's 112, 0.375× R0's producer shuffles, −22.3 %
executed instructions, 1.000× the DRAM floor, and byte-identical issued load sectors to
R0. It costs 72 registers against R0's 40 — 3 blocks/SM against 6 — and wins anyway. Its
`q` is bit-exact equal to `lsb-recompute`'s. Full record, including the ncu comparison
against R0 and R1, in `iteration_times.md`'s *v3 R2* section.

`iteration_times.md` carries the R0 gate record: at `--log-trace 24` it is
**20.713 ms** (`census`) and **20.596 ms** (`locality`) on `eval + finalize` against
v2's matched 23.272 / 23.078, at 1.000× the DRAM floor (a distinct-bytes measure), with
loads perfectly coalesced — 1.000× the sector *minimum for the requests it issues*,
which is a coalescing ratio and not a traffic one; the W = 0 stream itself re-reads the
backing 3.54×, absorbed by L1/L2 — on 40 registers, zero spills and 100 % theoretical
occupancy.

### The window arms (v3 R3) — diagnostic, not candidates

`--pair-arm {control,t,w,wt,wnone,wtnone}` selects an R3 window arm of `--mode lsb-pair`.
The **window** is a coset-only top-4-BF register window: the four most-referenced `bf`
sources are retained across records in named registers behind warp-uniform switches, so a
reuse skips the shuffle-NTT chain. A slot holds the source's `c[2]` only — `h[2]` is still
loaded — which is why it costs 8 registers rather than 16 and skips the chain but not the
resolve loads. The schedule is planned on the host per (program, term order, census knobs),
validated by an always-on state machine, and shipped in a **window-only side descriptor**
with one two-operand nibble-tag byte per record; the control wire is untouched, so a bare
`--mode lsb-pair` run is unchanged by any of this.

| `--pair-arm` | kernel | descriptor | regs, blocks/SM | what it isolates |
| --- | --- | --- | --- | --- |
| `control` (default) | R2 pair | none | 72, 3 | the recommended arm, unchanged |
| `t` | R2 pair + `__launch_bounds__(256, 3)` | none | 79, 3 | the launch bound alone |
| `w` | window | planned | 82, **2** | the window alone |
| `wt` | window + launch bound | planned | 80, 3 | both |
| `wnone` | window | all-`none` tags | 82, **2** | the machinery with none of the saving |
| `wtnone` | window + launch bound | all-`none` tags | 80, 3 | the same at 3 blocks |

`w` and `wnone` are **2-block arms** — 82 registers is 88 allocated at 8-register
granularity, over the 80-register/3-block cliff — so a contrast against the 3-block control
is not occupancy-neutral. `wtnone` exists so that `wt − t` splits into machinery
(`wtnone − t`) and removal (`wt − wtnone`) without crossing an occupancy class.

**All six arms are slower than the control**; the rung is a MISS and the arms are kept as
the measurement that priced it. `iteration_times.md`'s *v3 R3* section carries the record:
best window arm 17.173 ms against the control's 16.287, machinery +1.207 ms against a
−0.879 ms removal, and the rung-2 calibration slope of **18.70 µs per removed production**.
Every arm's `q` is bit-exact equal to the control's — **40/40 cells**, five arms x 2 term
orders x 2 `eq` forms x 2 censuses, run on both the shipped and the diagnostic build.

```bash
# one arm
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench \
    --log-trace 24 --warmup 10 --iterations 100 --mode lsb-pair --pair-arm wt \
    --term-order locality

# the balanced factorial: all six arms in ONE process against shared allocations, in a
# generated cyclic rotation each round so no arm keeps a fixed position in the order
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench \
    --log-trace 24 --warmup 10 --iterations 100 --mode lsb-pair --factorial \
    --term-order locality > /tmp/factorial.log
python3 gpu/gkr_uniskip_bench/tools/factorial_table.py /tmp/factorial.log
```

`--factorial` requires `--mode lsb-pair`, is mutually exclusive with `--pair-arm`, and
rejects `--validate`/`--validate-flat-eq`/`--dump-q` (it is a timing run; those would print
a verdict and check nothing). It emits one `SAMPLE` line per (round, arm) plus a
`FACTORIAL schedule` line recording the planned reuses. **Use a round count that is a
multiple of 6** so every arm starts an equal number of rounds: **use `--iterations 102`**,
the smallest multiple of 6 at or above 100. The recorded run used 100, which left starting
positions at 16/16/17/17/17/17; the residual imbalance is ≤ 0.005 ms, below every contrast
in the record, so that data stands — but there is no reason to repeat it.

`tools/factorial_table.py` turns that log into the per-arm medians, the paired contrasts
with their occupancy labels, the decomposition identity, the interaction and the three
slopes. **All of its guards are hard errors, and each order is checked against its own
metadata** — an order never borrows another order's `ARM` block or trailer. It rejects: a
duplicate sample; a duplicate `ARM` line or a duplicate trailer for one order; an `ARM`
line that precedes any `FACTORIAL schedule` line, so occupancy facts cannot float free of
a term order; an order with no `ARM` block or no trailer; any round that does not carry the
full declared arm set; an `ARM` count that disagrees with the trailer's `arms=`; and a
round count that disagrees with the trailer's `rounds=`. A truncated or two-session log
therefore cannot be summarized as though it were whole — the R1 and R2 records each lost
review rounds to hand-assembled tables, and no R3 number is transcribed.

#### Diagnostic build and its probes

The production-count gate and the device-side mutations need symbols a shipped build does
not carry, so they live behind a compile gate:

```bash
GPU_GKR_UNISKIP_BENCH_WINDOW_DIAG=1 cargo build --release -p gpu_gkr_uniskip_bench
```

That sets the `window_diag` cfg on the Rust side and `AB_UNISKIP_WINDOW_DIAG` in CMake, and
enables three test-only flags: `--window-count` (reads a device counter of chain executions
per warp-program walk — **279** under `w`/`wt` against **326** under
`control`/`wnone`/`wtnone`),
`--window-poison` (corrupts every slot's retained copy after its fill, so a later reuse must
change `q`), and `--window-mutate {retarget,…}` (perturbs the schedule to prove the gates
discriminate slot identity and retention). The define is passed as an explicit `ON`/`OFF`
rather than only when set, because a CMake cache that keeps the last value will otherwise
leave the counter atomic compiled into a build you believe is shipped.

`--cache-factorial` runs the R4 primary rotation: **eleven lanes** in one process — at 256
`control`, `cache0`, `hot4`, `hot16`, `allrepeat`; at 128 the same five plus `control128_lb`,
the bounded no-cache baseline that makes the cache contrast bound-to-bound. Use
`--iterations` a multiple of 11 (the record uses 99 per term order). It owns both block
sizes internally and rejects anything that would change what the rotation runs —
`--cache-arm`, `--block-threads`, `--prologue-order`, the launch-bounds flags, the diag
probes, `--profile` and the validation flags. `all59`, `e4rich`, `e4top2`, the BF-first
prologue order and the unbounded cached-128 body are excluded by construction and run as
separate single-arm diagnostics.

`tools/r4_table.py` emits the table from that log. The arm schema is data-driven from the
log's `ARM` lines, which the runner writes from Rust, so the emitter carries no arm list, no
occupancy fact and no kernel name of its own. `eval` and `finalize` are summarized
separately (the 128 lanes run twice the grid, so finalize is not the same work), every
contrast names its baseline, and the guards — duplicate sample, missing or duplicate
trailer, `ARM` before a schedule line, wrong arm set, lane-count mismatch — are hard errors.

`tools/r4_gates.sh {matrix|counts|diag|all}` is the R4 wall: `matrix` is 112 `q`-parity
cells (7 cached arms x 2 block sizes x 2 term orders x 2 `eq` forms x 2 censuses) plus both
128 launch-bounds sibling pairs and a CPU-oracle cell per arm per size; `counts` re-derives
the spec's local-traffic table with ncu — instruction counts, sector minima and prologue H
bytes, with the metric list in the script; `diag` needs the diagnostic build and runs the
exact chain-count gate plus the mutations. Cell counts are asserted, so a dropped loop
dimension fails instead of passing quietly.

`--cache-mutate retarget` points a cached reference at a different LIVE same-width slot and
uploads it UNCHECKED — the always-on validator would reject it, which is the point: `q` must
change. `--window-poison` now corrupts the R4 coset frame as well as R3's register slots, so
a cached arm that does not diverge under it is not reading the frame it filled.

`tools/r3_gates.sh {matrix|blocks|diag|all}` runs the R3 gates rather than describing them — `matrix`
is the 40-cell `q`-parity sweep and runs on either build; `diag` and `all` need the
diagnostic build. Its exit status is the verdict, and it rejects the empty digest, because
an empty `--dump-q` hashes identically on both sides and would pass every parity cell
vacuously.

> **Before any timed run, wipe the native build dir and rebuild shipped.** Diagnostic and
> shipped objects share one build directory, so a stale diagnostic object can survive an
> env-unset rebuild. Verify `GLOBAL:0`, zero `ATOM`/`RED`, and per-function SASS identical
> to the frozen control before taking a timing. Every R3 timing in `iteration_times.md` ran
> that ritual first.

### Block size (v3 R4) — `--block-threads {256,128}`

`--block-threads 128` runs a **distinct kernel**, not a launch-parameter change: the shared
reduction plane and the epilogue's cross-warp sum are static, so a 4-warp block needs its
own entry point. Per-warp geometry, the lane map and the program walk are the 256 control's
exactly — only the block shape moves, so a block covers **16** logical rows instead of 32
and the grid doubles.

It is the **no-cache baseline of the 128 axis** and is source-frozen from R4 Task 1A, which
is why it composes with `--pair-arm control` only: the R3 window bodies exist at 256 threads
alone. Measured on sm_120, both kernels compile to **72 registers**, and the finer block
granularity is worth resident warps:

| kernel | threads | static smem | blocks/SM | warps/SM | theoretical occupancy |
| --- | --- | --- | --- | --- | --- |
| `..._lsb_pair_kernel` | 256 | 4096 B | 3 (register-bound) | 24 | 50.00 % |
| `..._lsb_pair_128_kernel` | 128 | 2048 B | 7 (register-bound) | 28 | 58.33 % |

`q` is bit-exact against the 256 control across both term orders x both `eq` forms x
{default, `--self-products`}.

### The coset cache (v3 R4) — host machinery only today

`--cache-arm control|cache0|hot4|hot16|allrepeat|all59|e4rich|e4top2` selects an R4 arm of
`--mode lsb-pair`. The design caches **cosets only** — `h` is still loaded at every
reference — produced once per thread by a prologue into a per-thread local frame, with the
disposition riding the source record's existing `cache_slot` byte. Because admission is
**source-global**, a `PRODUCT`'s two operands each carry their own disposition on their own
record, so R3's two-operand tag problem cannot recur.

Admission is one canonical list: references descending, cut at **refs >= 2** (a once-used
source would cost a store and a load to save nothing), ties **E4 before BF** then lower
source id. `hot4` / `hot16` / `allrepeat` are prefixes of it; `e4top2` is the two highest-ref E4
sources (the family-stop lane, small enough to separate E4 value from capacity) and
`e4rich` the full E4-only coverage set; `all59` is every live source including refs = 1 — a capacity-stress diagnostic that
buys **zero** extra removals over `allrepeat` and is never a candidate. Slot assignment is
decoupled from admission: all E4 spans first (4 units, 16-byte aligned, c-object-major),
then one 8-byte unit per BF source.

At the default census, per warp-program walk:

| arm | admitted | C (units / B) | chains | stores | loads | removals |
| --- | --- | --- | --- | --- | --- | --- |
| `control` / `cache0` | 0 | 0 / 0 | 326 | 0 | 0 | 0 |
| `hot4` | 4 bf | 4 / 32 | 279 | 4 | 51 | 47 |
| `hot16` | 12 bf + 4 e4 | 28 / 224 | 181 | 20 | 133 | 145 |
| `e4top2` | 2 e4 | 8 / 64 | 278 | 4 | 28 | 48 |
| `e4rich` | 11 e4 | 44 / 352 | 234 | 22 | 68 | 92 |
| `allrepeat` | 44 bf + 11 e4 | 88 / 704 | 92 | 66 | 254 | 234 |
| `all59` | 48 bf + 11 e4 | 92 / 736 | 92 | 70 | 258 | 234 |

`hot4` is R3's register window with a different carrier — same four sources, same
13/13/13/12 references, same 47 removals — which is what makes the two rungs directly
comparable.

A cached arm runs a prologue that produces every admitted source once into a **736 B
per-thread local frame**, sized at `C_max` for every arm so all arms share one kernel body
and differ only in uploaded state. Consume-side access is `LDL.64` for BF and two `LDL.128`
over the 16-byte-aligned E4 span. At 128 threads the cached body needs
`__launch_bounds__(128, 7)` to hold control128's 7 blocks/SM (unbounded it is 75 registers
= 6); `--no-cache-launch-bounds` runs the stepped variant so the bound can be priced, and
`--control-launch-bounds` gives the matching bounded NO-CACHE baseline so the contrast can
be taken bound-to-bound. `--prologue-order bffirst` reorders the uploaded table on the
capacity arms — a different upload, not a different kernel.

Every `--mode lsb-pair` run builds and validates the plan for all eight arms and prints a
`coset cache (v3 R4)` block plus the exact `eval kernel` it will launch; arms a census
pushes past the frame are reported `unavailable` rather than failing runs that never select
them. Admission is recomputed from the live resolver stream, so unlike the shared-memory
cache plan it does **not** go stale under `--self-products`.

### Geometry

- 16 taps of a logical row live on the multiplicative subgroup `H` of order 16;
  the pass also evaluates the 16 cells of the odd coset `gamma*H` (`gamma^16 = -1`,
  so the two are disjoint), giving `UNISKIP_CELLS = 32` cells per logical row.
- `log_rows = log_trace - 4`; `log_rows` must be in `[5, 21]`. The upper bound is
  the device accessor's 32-bit element index (an `addr` names up to 128 columns of
  16 planes, so `11 + log_rows` bits), the lower bound is one block's row tile.
- The LDE stage has two interchangeable grid shapes, `--lde-shape {cell,row}`, which
  write the same bytes. `cell` (`lde_bf`/`lde_e4`) is one thread per (column, coset
  cell, row), so a row's 16 taps are re-read once per cell. `row`
  (`lde_bf_row`/`lde_e4_row`, the default) is one thread per (column, row) — per
  (column, row, limb) for `e4`, since the extension is `bf`-linear per limb — which
  reads each tap once and emits all 16 cells, keeping the reuse in registers. Both are
  measured in `iteration_times.md`.
- `--mode lsb-recompute` uses none of the geometry in the rest of this section: its
  group is a 16-lane half-warp, its block covers 16 logical rows, and it has no LDE
  stage, no cell map and no fold. See [The LSB mode](#the-lsb-mode-v3-r0).
- The eval kernel is **cell-slab**: 256 threads = 8 warps, lane = row inside a
  32-row tile, warp `w` owns cells `4w..4w+3`. Warps 0–3 take the tap cells and
  warps 4–7 the coset cells, so the `H`-vs-coset choice is warp-uniform. The four
  accumulators are only ever indexed by fully unrolled loops, so they stay in
  registers (zero spills — see `iteration_times.md`).
- Fused modes add `--cell-map interleave`, which gives warp `w` the cells
  `{w, w+8, w+16, w+24}` — two `H` and two coset each, so the recompute spreads over
  all eight warps instead of sitting on warps 4–7. Both maps are bijections onto the
  32 cells and `q` is cell-indexed, so the oracle is unaffected. The map is a
  compile-time template argument, hence one kernel per (mode, map).
- `fused-cached` adds a **32 KB shared pool per block**, its only shared allocation
  (the cell reduction is `shfl`-only). The pool is 16 fixed *units* of 2 KB; a unit
  holds one `bf` plane of one source's coset slab for the block's tile —
  `UNISKIP_TAPS` coset cells × `UNISKIP_ROWS_PER_BLOCK` rows — so a `bf` source takes
  one unit and an `e4` source four, one per limb. 16 units is the largest pool that
  still fits three blocks on an sm_120 SM; `iteration_times.md` measures the cliff.
- `eq` is factored into three tables: the low `low` bits of a row index a device
  table, the next `high[1]` bits and the top `high[0]` bits index two
  `__constant__` tables of at most 256 entries each. High tables fill first.
- **k is fixed at 4 across both languages, and changing it is not a one-line
  change.** Nothing is parameterized on k; the dependent taps/cells/warp geometry
  and the domain generator indices are hard-coded separately on each side. Moving
  to k=3/5 means touching, independently:
  - `native/uniskip_abi.cuh` — `UNISKIP_TAPS` (16), `UNISKIP_CELLS` (32),
    `UNISKIP_WARPS_PER_BLOCK` (8), `UNISKIP_CELLS_PER_WARP` (4), the
    `static_assert`s tying them together, and `UNISKIP_LOG_ADDRESSABLE_PLANES`
    (11 = 7 column bits + log2(taps)) with the max-row assertion beside it;
  - `src/abi.rs` — the same four constants (`UNISKIP_LOG_TAPS` is derived from
    `UNISKIP_TAPS` and follows on its own);
  - `src/domain.rs` — the subgroup and coset generator indices, `omega16()` =
    `TWO_ADICITY_GENERATORS[4]` and `gamma()` = `TWO_ADICITY_GENERATORS[5]`, the
    `omega16` name itself, and the production arithmetic `F::new(16)` (the
    `inv16` sites) and `r.pow(16)` in `fold_weights`;
  - the tests that pin the k=4 values — the bare `16` literals in `src/domain.rs`'s
    tests, the addressable-plane/element-index pins in `src/abi.rs`'s layout
    tests, and `UNISKIP_MAX_LOG_ROWS == 21` plus the eq-tuple pins in
    `src/geometry.rs`'s.

  This list enumerates the k-dependent sites known at this commit; before
  trusting it exhaustive after further changes, grep for `UNISKIP_TAPS` and the
  bare `16`/`11`/`21` literals.

  Deriving all of that from one constant per language is deliberately **not** done:
  v2 restructures these kernels anyway, and v1's scope fixes k at 4 on purpose.

### Addressing contract

- **Plane-order layout.** Tap `t` of logical row `r` sits at element offset
  `r + (t << log_rows)` inside its column; a column is `16 << log_rows` elements.
  `--mode lsb-recompute` replaces this ordering with `(r << 4) | t` and nothing else —
  see [The LSB mode](#the-lsb-mode-v3-r0). `abi::SourceLayout` names the two and
  `Layout::source_offset` dispatches, so the oracle and the accessor cannot disagree
  about which one a run is using.
- **One backing per field class.** All `bf` windows share one tap allocation and
  one identically shaped coset allocation, packed in window order; the `e4`
  windows likewise. Windows are field-homogeneous by construction — one typed base
  per window, so mixed columns would have incompatible strides.
- **Cell numbering.** Tap `t` is cell `t`; row `c` of the coset LDE matrix is cell
  `16 + c`. Host and device both hang off `abi::{cell_for_tap, cell_for_coset_row}`.
- **`addr = window << 7 | column`.** The fold output is indexed by *source id*
  (`source * rows + row`), not by job id, so both class kernels share one buffer.

### The accessor seam

Every operand read **in the eval kernel** — that is, all term execution — goes
through one function, `uniskip_source_value<T>(desc, source_id, cell, row)` in
`native/uniskip_abi.cuh`. It resolves the source record, picks the tap or coset base
from the cell, and issues one typed load. **v2 (LDE-on-read, published sources) only
swaps this body** — the term execution above it does not change.

`--mode lsb-recompute` does not go through this seam at all: its lane map, its
accumulator count and its element ordering all differ, so it carries its own accessor
(`uniskip_lsb_resolve` in `native/uniskip_lsb.cuh`) and its own term walk. The seam
below describes the v1/v2 kernels, which that mode leaves byte-for-byte alone.

That swap is an **overload**, selected by the descriptor type. `uniskip_fused_desc`
is an empty class derived from `uniskip_vm_desc` — same members, same size, same
`__grid_constant__ ` parameter, so the host wire struct is shared and only overload
resolution differs. The term loop is `uniskip_eval_body<Desc, INTERLEAVE>`; each
`__global__` entry point instantiates it with one descriptor type, so the call sites
inside it are spelled identically for every mode and neither arm pays for the
other's code. The fused overload reads no coset base at all: an `H` cell is the
direct tap load, and coset cell `UNISKIP_TAPS + c` is the 16-tap dot with row `c` of
the coset LDE matrix, per `bf` limb. The dot accumulates **four taps wide before one
Montgomery reduction** (`UNISKIP_DOT_CHUNK`): `bf::red_wide` takes inputs to ~4p² and
reduction is linear mod p, so this is bit-identical to a per-tap `fma` chain at a
quarter of the reductions.

The fused-cached overload adds one branch in front of that: a coset cell of a source
the host gave a slot reads the block's shared slab instead, and everything else keeps
the recompute. The slot travels in `uniskip_source_record.cache_slot` — v1's
`reserved` byte, so the 4-byte record is unchanged — and the *inverse* plan
(unit → source and limb) travels in the `ab_gkr_uniskip_cache_fill` `__constant__`
array, so the tile-start fill iterates 16 units rather than the whole source table.
The fill is row-shaped like `--lde-shape row`: one lane owns (unit, row), loads that
row's 16 taps once and emits all 16 coset cells from registers, so a slab costs 16 tap
loads per row and not 256. Lane is the row inside the tile, which makes both the tap
loads and the slab stores warp-contiguous; a `__syncthreads` separates fill from use.
The plan itself is host lowering (`src/cache.rs`): rank by net saving per shared byte,
assign the top ones to fixed units, no eviction.

The LDE and fold kernels deliberately do *not* go through it: they are bulk
per-column plane sweeps that inline their own tap addressing
(`native/uniskip.cu`), because they walk whole planes rather than resolving
individual operands. In v2 the LDE sweep is what the accessor absorbs, so it is
the seam's counterpart, not one of its users.

`abi::source_offset` is the host mirror of exactly that arithmetic, and the CPU
oracle addresses every cell through it, so an accessor/kernel disagreement surfaces
as a validation failure rather than as silently matching wrong data.

## Build and run

```bash
# build (unlocked)
cargo build --release -p gpu_gkr_uniskip_bench
target/release/gpu_gkr_uniskip_bench --help

# any run that touches the GPU (locked)
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench --log-trace 20

# the recorded baseline (add `--lde-shape cell` for the v1 LDE control arm)
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench \
    --log-trace 24 --warmup 10 --iterations 100

# the fused pass (add `--cell-map interleave` for the spread-recompute arm)
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench \
    --log-trace 24 --warmup 10 --iterations 100 --mode fused-recompute

# the recommended arm (also the fastest recorded)
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench \
    --log-trace 24 --warmup 10 --iterations 100 \
    --mode fused-cached --cell-map interleave --term-order locality
```

Building and `--help` do not need the lock; every execution does.

**The shape flags are an explicit matrix, not free-floating knobs:** `--lde-shape`
applies to the unfused mode only (no other mode has an LDE stage to shape) and
`--cell-map` to the two fused modes only — `unfused` keeps the v1 block map and
each LSB mode fixes its own (`lsb-recompute` lane = tap at two groups per warp,
`lsb-pair` pair-resident at eight lanes per group and four groups per warp). `--compact-groups`
and `--bank-perm` apply to `lsb-compact` alone, `--pair-arm`, `--factorial`,
`--cache-arm` and `--block-threads` to `lsb-pair` alone (see [The window arms](#the-window-arms-v3-r3--diagnostic-not-candidates)
and [The coset cache](#the-coset-cache-v3-r4--host-machinery-only-today)), and
`--compact-groups 8` additionally
needs `--log-trace >= 10` (a compact block is 8 warps × `groups` rows and must tile the
trace — rejected with a message, not an assert). The inapplicable knob prints as `n/a` in
the config block and the summary line, so a recorded measurement can never name a shape
the run did not use. `--term-order` is not in the matrix: it
reorders records, which every mode executes.

The cache plan — `C`, `Ru`, the mul-pipe op split and the slot assignment — prints at
startup in **every** mode, since it is derived from the program rather than from the
mode; a non-caching mode labels it `(not applied in this mode)` and ships the wire
with every `cache_slot` at the uncached sentinel.

### Validation

```bash
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench --log-trace 10 --validate
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench --log-trace 10 --validate-flat-eq
```

Both apply to every mode; add `--mode {fused-recompute,fused-cached} --cell-map
{block,interleave}` and `--term-order {census,locality}` to validate the fused arms,
or `--mode lsb-recompute --term-order {census,locality}` for the v3 R0 arm. There the
LDE check reports `n/a` — no mode but `unfused` has a coset buffer to compare — and
the `q` oracle, which addresses all 32 cells through `Layout::source_offset`, is what
pins the recomputed, the cached and the shuffle-NTT-produced ones. `lsb-recompute`
additionally reports `fold validate: n/a`, since it runs no fold stage.

```bash
# the v3 R2 arm (the recommended v3 mode)
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench --log-trace 10 --validate \
    --mode lsb-pair --term-order {census,locality}

# the v3 R1 arm
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench --log-trace 10 --validate \
    --mode lsb-compact --compact-groups {4,8} --term-order {census,locality}

# cross-mode oracle: lsb-compact's q must be BIT-EXACT equal to lsb-recompute's, compared
# device-to-device with no host oracle in the loop
B=target/release/gpu_gkr_uniskip_bench
$B --log-trace 12 --iterations 0 --dump-q --mode lsb-recompute --term-order locality | grep '^q\[' > /tmp/a
$B --log-trace 12 --iterations 0 --dump-q --mode lsb-compact --compact-groups 4 \
    --term-order locality | grep '^q\[' > /tmp/b
$B --log-trace 12 --iterations 0 --dump-q --mode lsb-pair \
    --term-order locality | grep '^q\[' > /tmp/c
diff /tmp/a /tmp/b && diff /tmp/a /tmp/c        # both empty
```

`--dump-q` prints the 32 evaluations as raw hex words, one cell per line, and applies to
every mode; it is how two arms are compared without going through the host oracle.

`--self-products <N>` applies to every mode and is validation-only: it rewrites `N`
same-class binary products into `x * x`, which is the only way to reach the LSB mode's
W = 0 duplicate rule (see [The LSB mode](#the-lsb-mode-v3-r0)). It changes `q`, and the
census and cache plan do not track it — they go stale (see the mode contract above) —
so never take a recorded timing under it.

`--validate` runs three bit-exact checks against a host oracle that regenerates the
operand data from the init formula rather than reading it back: **LDE** (first and
last used column of every window, taps and all 16 coset cells), **q** (all 32 cells,
full oracle), and **fold** (sampled rows at the first and last used column of both
field classes). `--validate-flat-eq` forces every `eq` entry to ONE on both sides,
isolating the term VM from the `eq` composition.

The q oracle costs `O(rows · sources · 256)` — about 18 s at `--log-trace 22` and
~70 s at 24. Validate at small `--log-trace`; benchmark at large.

### Profiling

```bash
mkdir -p target/uniskip-prof
.agents/bin/with_gpu_lock.sh nsys profile --trace=cuda,nvtx --force-overwrite=true \
    -o target/uniskip-prof/pass0 \
    target/release/gpu_gkr_uniskip_bench --log-trace 20 --warmup 3 --iterations 5 --profile
nsys stats --report nvtx_sum --format csv target/uniskip-prof/pass0.nsys-rep
```

`--profile` wraps the **first timed iteration** (so warmup is excluded) in the NVTX
range `gkr_uniskip_pass0`; it needs `--iterations >= 1`. NVTX comes from a two-call
shim in this crate's own archive — `gpu_core` owns the cluster's wrapper but is only
a dev-dependency here. Keep profiler output under `target/` (gitignored).

### Timing model

Each pass records CUDA events around the four stages; every pass records them,
warmup included, so a timed pass and an untimed one do identical work. The reported
`min GB/s` column divides each stage's **compulsory** traffic — every distinct byte
it must read or write at least once, from `Harness::pass_bytes` — by its median time.
That is a *lower* bound on achieved bandwidth, not a measurement of it: real DRAM
traffic is never below the floor and is usually above it (`--lde-shape cell` re-reads
its input once per coset cell, ~16×; `row` reads it once, so there the two coincide),
so the true GB/s is at least the number printed and can be many times it. Measured
numbers and their interpretation live in `iteration_times.md`.

Two rules that any recorded timing depends on. **Wipe the native build dir and rebuild
shipped before timing** — diagnostic and shipped objects share one build directory, so
verify `GLOBAL:0`, zero `ATOM`/`RED` and unchanged per-function SASS first (see [the window
arms](#the-window-arms-v3-r3--diagnostic-not-candidates)). And **compare arms within a
session**: absolute medians drift ~1 % between sessions on this part, so a contrast is only
trustworthy if both sides ran in the same process — which is what `--factorial` is for.

## Census defaults and provenance

Instead of consuming a real GKR layout, the bench runs a **deterministic synthetic
program** whose census is pinned to the shape of the **round-0, layer-0 add/sub
circuit**:

| quantity | default | note |
| --- | --- | --- |
| program records | 175 | = 150 semantic terms + 25 group headers |
| semantic terms | 150 | ungrouped + grouped atoms |
| groups | 25 | one header record each |
| grouped atoms | 72 | semantic terms living inside a group |
| coefficient applications | ~103 | one per ungrouped term + one per group |
| sources | 59 | distinct columns; one source per column |
| live coefficient ids | ~80 | distinct coefficient-bank slots referenced |

All are overridable from the CLI (`--sources`, `--semantic-terms`, `--groups`,
`--grouped-atoms`); the generator recomputes and prints the achieved census at
startup, so a scaled run reports what it actually built.

**Match quality, stated precisely: the group COUNT and the coefficient-application
count are matched to the real circuit; the group-TYPE mix is synthetic.** Every
group is modeled as a variable-arity BF group. The real wire also carries
fixed-arity E4 groups, and their round-0 count is **unverified** — confirming it is
Task 6 work. Read the totals as representative, not as a transcript of the real
program.

## Deliberate limitations

None of these is an oversight; each is a scoping decision to be revisited. The v2
ladder discharged one outright and one in part — both marked below — and the rest
stand. `iteration_times.md` carries the numbers behind every claim here.

- **Synthetic program.** *(stands)* Groups are modeled because they shape the
  coefficient-FMA count. *Procedural synthesis* is not: its 4 known occurrences are
  emitted as ordinary BF terms reading a dedicated setup-like window. Natural-index
  synthesis is Task 6.
- **Global coset materialization — DISCHARGED in the fused modes.** v1 wrote the coset
  to memory and read it back, ~2× the traffic of extending on read, and that was
  measured on purpose as the baseline the LDE-on-read accessor had to beat.
  `--mode fused-recompute` and `--mode fused-cached` delete both the LDE stage and the
  coset backing: 5.75 GiB resident instead of 11.50 GiB, with issued DRAM traffic at
  1.00–1.008× the compulsory floor. The materialization survives only in the unfused
  modes, which are kept as the control arm and as the live LDE validation leg. (The
  separate 16× tap re-read that made `lde` dominate the v1 pass was fixed earlier, by
  `--lde-shape row`.)
- **No shared-memory operand cache — PARTIALLY DISCHARGED.** `--mode fused-cached`
  adds one for the coset cells (see above), and it is worth −17.9 % on `pass − fold`.
  But it is a **fixed** assignment with no eviction, it holds only the top 16 units of
  a 92-unit total — 16 units is the largest pool that keeps three blocks on an sm_120
  SM, so the limit is the shared budget and not the plan — and the `H` cells are still
  direct tap loads. The remaining operand reuse (~3.8 references per source) is left to
  L1/L2.
- **No NTT-form producer — DISCHARGED, in a different architecture, and not because the
  transform is cheaper.** *(the v2 gate below still stands as a statement about v2)*
  `--mode lsb-recompute` ships one: a radix-2 shuffle-NTT across a 16-lane group. Stated
  **per output cell**, which is the only honest comparison: v2's dot costs 16 `mad_wide`
  + 4 `red_wide` = 28 mul-pipe ops for **one** cell; the shuffle-NTT costs 7 `bf::mul`
  per lane = 28 mul-pipe ops for **one** cell (112 per 16-cell group, of which only 50
  are non-unity — the rest are lane-divergent under lane = tap and still issue). **The
  multiply work is a wash.** What the LSB layout actually buys is the load side: one
  coalesced group load per reference serves all 16 coset cells *and* the `H` cell, where
  v2 reloads 16 taps per coset cell — 17× fewer load instructions per (record, row), and
  their address chains with them. The v2 rung-3 record is kept verbatim so the two
  decisions stay distinguishable:

  > Rung 3 of the v2 ladder was to produce the coset cells with a length-16
  > transform instead of the 16×16 matrix apply. It was gated on materiality and the
  > gate failed: only the *cached* share of resolution is eligible, that share is 16
  > of 205 dot units (7.8 %), and the resulting whole-stage bound is 0.30–0.65 ms of
  > 23.078 ms against a bar of ≥ 5 % **and** ≥ 1 ms. Even an infinitely fast fill
  > saves ≈ 0.55 ms. The gate record in `iteration_times.md` has the formula and the
  > re-run recipe.
- **No tensor cores.** *(stands)* The tap→coset extension is a 16×16 matrix apply per
  column and is an obvious MMA candidate; both the unfused and the fused modes do it
  with scalar FMAs. What is measured: the recommended mode is mul-pipe bound
  (`fmaheavy` accounts for the whole SM speed-of-light, DRAM sits at 16 %), and the
  pool sweep's fit puts ~45 % of the `eval` stage in the resolver, where that apply
  lives. Neither measurement isolates the apply itself, so this is a standing lever
  with a direction, not a sized one. The rung-3 skip above does not close it — an
  NTT-form producer and an MMA producer are not the same change.
- **Single pass, no telescoping.** *(stands)* One uniskip round in isolation; no
  round-to-round reuse of the folded output.
- **Synthetic `eq`.** *(stands)* The tables carry the production *factored shape* but
  are filled from the init generator, not from a transcript, so `q` is not a
  protocol-real claim.
- **Synthetic operand-reuse pattern.** *(stands, and it is the one that scopes every
  timing above)* Sources are picked from a deterministic hot-list (a fixed hot slice
  per pool taking ~40% of references), reported at startup under `hot sources`.
  Adequate for kernel validation and for v1↔v2 comparison; **not** an absolute
  production estimate until Task 6 replaces the synthetic program with the real one.
  The cache plan is derived from exactly this pattern, so the recommended mode's margin
  is the one number here most likely to move with a real program.
