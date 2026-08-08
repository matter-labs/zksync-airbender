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

`--term-order` reorders the record stream — `census` (the default) is emission order,
`locality` is the permutation that clusters records reading the same sources. It is a
program property, legal in every mode, and it changes only which order operands are
touched in; `q` is a sum of per-term contributions in `bf`/`e4`, so both orders give
bit-identical results.

### Modes, and which one to run

All numbers below are medians at `--log-trace 24` on an RTX PRO 6000 Blackwell over
`--warmup 10 --iterations 100`, from `iteration_times.md`; all 12 legal arms pass
`--validate` and `--validate-flat-eq` (the 24-cell matrix is tabulated there too).
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

**The recommendation is `fused-cached` + `interleave` + `locality`.** It is the fastest
arm measured (3.92× the v1 pass on `pass − fold`, 3.42× on the full pass, 1.22× the
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
is rejected in a fused mode (there is no LDE stage to shape) and `--cell-map` is
rejected in an unfused one (which keeps the v1 block map). The inapplicable knob
prints as `n/a` in the config block and the summary line, so a recorded measurement
can never name a shape the run did not use. `--term-order` is not in the matrix: it
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
{block,interleave}` and `--term-order {census,locality}` to validate the fused arms.
There the LDE check reports `n/a` — a fused mode has no coset buffer to compare — and
the `q` oracle, which addresses all 32 cells through `abi::source_offset`, is what
pins the recomputed and the cached ones.

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
- **No NTT-form producer.** *(stands — skipped against a measured gate, not overlooked)*
  Rung 3 of the v2 ladder was to produce the coset cells with a length-16 transform
  instead of the 16×16 matrix apply. It was gated on materiality and the gate failed:
  only the *cached* share of resolution is eligible, that share is 16 of 205 dot units
  (7.8 %), and the resulting whole-stage bound is 0.30–0.65 ms of 23.078 ms against a
  bar of ≥ 5 % **and** ≥ 1 ms. Even an infinitely fast fill saves ≈ 0.55 ms. The gate
  record in `iteration_times.md` has the formula and the re-run recipe.
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
