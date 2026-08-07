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

### Geometry

- 16 taps of a logical row live on the multiplicative subgroup `H` of order 16;
  the pass also evaluates the 16 cells of the odd coset `gamma*H` (`gamma^16 = -1`,
  so the two are disjoint), giving `UNISKIP_CELLS = 32` cells per logical row.
- `log_rows = log_trace - 4`; `log_rows` must be in `[5, 21]`. The upper bound is
  the device accessor's 32-bit element index (an `addr` names up to 128 columns of
  16 planes, so `11 + log_rows` bits), the lower bound is one block's row tile.
- The eval kernel is **cell-slab**: 256 threads = 8 warps, lane = row inside a
  32-row tile, warp `w` owns cells `4w..4w+3`. Warps 0–3 take the tap cells and
  warps 4–7 the coset cells, so the `H`-vs-coset choice is warp-uniform. The four
  accumulators are only ever indexed by fully unrolled loops, so they stay in
  registers (zero spills — see `iteration_times.md`).
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

# the recorded baseline
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench \
    --log-trace 24 --warmup 10 --iterations 100
```

Building and `--help` do not need the lock; every execution does.

### Validation

```bash
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench --log-trace 10 --validate
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench --log-trace 10 --validate-flat-eq
```

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
traffic is never below the floor and is usually above it (the LDE re-reads its input
once per coset cell, ~16×), so the true GB/s is at least the number printed and can
be many times it. Measured numbers and their interpretation live in
`iteration_times.md`.

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

## Deliberate v1 limitations

None of these is an oversight; each is a scoping decision to be revisited.

- **Synthetic program.** Groups are modeled because they shape the
  coefficient-FMA count. *Procedural synthesis* is not: its 4 known occurrences are
  emitted as ordinary BF terms reading a dedicated setup-like window. Natural-index
  synthesis is Task 6.
- **Global coset materialization.** The coset is written to memory and read back,
  which is ~2× the traffic of extending on read. That is measured **on purpose** —
  it is the v1 baseline that v2's LDE-on-read accessor has to beat, and it is why
  `lde` dominates the recorded pass.
- **No shared-memory operand cache.** Operand reuse (~3.8 references per source)
  is left to L1/L2.
- **No tensor cores.** The tap→coset extension is a 16×16 matrix apply per column
  and is an obvious MMA candidate; v1 does it with scalar FMAs.
- **Single pass, no telescoping.** One uniskip round in isolation; no round-to-round
  reuse of the folded output.
- **Synthetic `eq`.** The tables carry the production *factored shape* but are
  filled from the init generator, not from a transcript, so `q` is not a
  protocol-real claim.
- **Synthetic operand-reuse pattern.** Sources are picked from a deterministic
  hot-list (a fixed hot slice per pool taking ~40% of references), reported at
  startup under `hot sources`. Adequate for kernel validation and for v1↔v2
  comparison; **not** an absolute production estimate until Task 6 replaces the
  synthetic program with the real one.
