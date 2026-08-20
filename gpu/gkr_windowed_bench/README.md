# Windowed GKR GPU experiment

This crate is a standalone CUDA benchmark for the first three-variable
window of add/sub layer 0. It is intentionally outside the production GKR
crate: the default build consumes a checked-in compiler artifact and does not
compile or link the circuit compiler stack.

This is a throughput experiment, not a correctness implementation. The
harness makes the production-sized allocations and initializes them with
deterministic, nonzero field values, but it does not compare the 27 output
cells with a CPU oracle.

## Execution shape

- Each compact row owns one contiguous eight-element Boolean cube in LSB
  layout, and one CUDA block covers 32 compact rows.
- The VM block has 3 warps (96 threads). Three CTAs cover each compact-row
  tile, and each warp owns one of the nine `(x0, x1)` output pairs.
- Each warp evaluates the same segmented layer-0 VM program and accumulates
  its 3 `x2` values independently. For fixed `(x0, x1)`, the `bit2` endpoint
  pair occupies adjacent trace elements. There is no K split and no block
  barrier in the VM kernel.
- Each thread keeps twelve 96-bit BF-phase accumulators in registers, reduces
  them once at the checked BF/E4 boundary, and executes the seven E4 atoms in
  canonical E4 registers. The selected kernel uses 79 registers per thread,
  zero stack/local/shared memory, a zero shared-memory carveout, and
  `__launch_bounds__(96, 8)` on the benchmark's RTX PRO 6000 Blackwell Server
  Edition.
- The two infinity-selector predicates are formed once with full-warp votes
  and carried by value through the inlined VM evaluator. This preserves the
  nine-selector block and its shared L1 working set while avoiding repeated
  endpoint reconvergence scaffolding.
- Equality is factored into low and high tables. Each warp recomputes its own
  low factor; the high factor is read from constant memory.
- Lane 0 writes 3 E4 partials per warp, so the VM kernel writes 27 E4 values
  per block rather than `27 * warp_size` values.
- A separate 27-block finalizer reduces the block partials to the final 27 E4
  cells. Their linear order is `((x0 * 3) + x1) * 3 + x2`.
- For each `x`, indices `0`, `1`, and `2` mean the `0`, `1`, and infinity
  coefficients. The infinity coefficient is `f(1) - f(0)`; index `2` is not
  evaluation at the field element 2.
- Challenges are deliberately not consumed by this benchmark. Binding a
  challenge and shrinking 27 cells to 9 belongs after this first-window
  kernel.

The VM input comes from
`artifacts/add_sub_layer0.bin`. It retains the incoming compiler's segment,
group, source-binding, coefficient, and immediate structure, while replacing
compiler-owned Rust types with a small stable benchmark ABI.

The program wire is specialized for round 0. Every instruction is one
`align(8)` record with separate `u16` class, factor, source-A, and source-B
fields. The class low bit selects a complete BF or E4 atom path. BF groups may
use banked immediates and carry their arity in the header; E4 groups are fixed
two-member add/sub pairs. Mixed products are encoded in canonical BF-then-E4
source order. The decoder rejects programs outside these compiler-derived
invariants instead of falling back to a generic group path.

The complete control descriptor is passed by value as a 1,552-byte
`__grid_constant__` kernel argument. Its 175 aligned program records, 6
host-resolved window bases, and 7 immediates are inline; only the
input/equality/output data remains pointer-backed. Each ordinary source
operand directly packs a 7-bit relative column and a 6-bit window into its
existing `u16` instruction field. Because all sources share the trace domain,
the kernel computes `log_trace` once and uses typed pointer arithmetic for
`window_base + (column << log_trace)`. There is no source-ID table or device
source-metadata indirection. With the LSB-contiguous layout, direct BF and E4
sources load adjacent Boolean pairs and full eight-corner cubes through aligned
packed loads; the host debug path asserts the required 32-byte base alignment.
The host validates that 65 BF atoms occupy records `[0, 164)` and that the
seven E4 atoms occupy records `[164, 175)`. The retained VM uses
`__launch_bounds__(96, 8)`, 79 registers per thread, and zero stack, local, or
shared memory. Three CTAs per compact-row tile preserve the nine-selector
mapping, and eight CTAs can reside per SM under the selected register envelope.

The two virtual-setup windows are addressless and allocate no storage. The
four terms that consume them use two explicit cold BF classes: procedural
linear-A and direct-BF-by-procedural-B. Their source field stores one of the
four procedural kinds, and a small CUDA source synthesizes the requested trace
point before reusing the common triplet interpolation. Ordinary BF classes are
rejected if they name a virtual window, so the hot direct resolver contains no
procedural discriminator. Real input families remain independent allocations.

Procedural values consume the same LSB-composed physical trace index as direct
sources, so their implementation is unchanged while their logical
`(row, corner)` association follows the new layout.

## Build and run

Build only this crate:

```text
cargo build --release -p gpu_gkr_windowed_bench
```

Run GPU commands under the repository lock:

```text
.agents/bin/with_gpu_lock.sh \
  target/release/gpu_gkr_windowed_bench \
  --log-trace 24 --warmup 10 --iterations 100
```

`--profile` emits the NVTX range
`gkr_windowed_add_sub_l0_first_window` and executes one measured iteration:

```text
.agents/bin/with_gpu_lock.sh ncu \
  --nvtx \
  --nvtx-include gkr_windowed_add_sub_l0_first_window \
  --set basic \
  --kernel-name-base demangled \
  --kernel-name 'regex:^ab_gkr_windowed_vm_kernel$' \
  --target-processes all \
  target/release/gpu_gkr_windowed_bench \
  --log-trace 20 --warmup 1 --profile
```

The CUDA event timing covers both the VM kernel and the 27-cell finalizer. It
does not include allocation, deterministic initialization, artifact upload,
or the final host copy.

## Regenerating the layer artifact

Artifact generation is behind an optional feature so ordinary kernel edits do
not rebuild the compiler stack:

```text
cargo run --release -p gpu_gkr_windowed_bench \
  --features artifact-gen \
  --bin generate_add_sub_layer0 -- \
  --schedule source \
  --lazy-bf-reduction \
  --layout cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json \
  --output gpu/gkr_windowed_bench/artifacts/add_sub_layer0.bin
```

The generator lowers layer 0 through the incoming segmented VM compiler and
then serializes the round-0 benchmark form. The checked-in artifact uses the
`source` schedule, which preserves atom/group semantics while improving source
locality, plus `--lazy-bf-reduction`. The lazy option places direct BF products
before a group's linear tail and marks intermediate reduce-and-rebase boundaries
after at most four products; the VM reduces the final window unconditionally
after the loop. Omitting it regenerates the eager-reduction comparison artifact.
`compiler`, `control-atoms`, and `control` are available for A/B experiments.
This experimental artifact is replaced in place rather than migrated through
format versions. Drift is acceptable for this crate; regeneration is an
explicit operation.

## Corpus census and compact-program research tooling

The optional `artifact-gen` feature also contains GPU-free tooling used to
study program decoding without changing the retained kernel. It enumerates all
57 layers in the 12 primary circuits under both continuation regimes, for 114
canonical `(circuit, layer, pass)` coordinates. Each row keeps three views
separate: semantic structure, the compiler's real source binding, and the
benchmark's tighter encoding limits. Binding or capacity failures are typed
outcomes and never erase the semantic row.

The checked-in census and workload weights are deterministic:

```text
cargo run --release -p gpu_gkr_windowed_bench \
  --features artifact-gen \
  --bin generate_windowed_corpus_census -- --check
```

`artifacts/windowed_workload_weights_v1.json` records the current-branch base
layer and the development-branch recursion proxy independently. The missing
current-branch recursion profile remains explicitly unavailable; it is not
filled from the proxy. The compact codec and host evaluator are likewise
feature-gated research tools. They validate canonical-record/physical-slot
bijections, malformed streams, typed overflow, and lean/legacy/compact
semantic equality, but no compact decoder is enabled by the default build.

The 2026-08-13 investigation found that the direct compact prototype reduced
uniform program loads but added enough unpack and control work to remain about
6% slower than the selected VM. A denser same-window form regressed by a
further 8.17% against its direct compact parent. Legal reordering moved only
eight records (four adjacent swaps) in the retained add/sub schedule and was
timing-neutral after repeat, so it is a small-perturbation result rather than a
general verdict on scheduling. The complete evidence and corpus projections
are summarized in `iteration_times.md`; the retained CUDA/ABI/harness source
is unchanged by this tooling.

## R0 prototype bank

The feature-gated R0 prototype bank is a broad-search harness, not a production
kernel selection. It cross-combines eight by-value program encodings, the legal
inner/outer canonical, u64, and u96 accumulation policies, five selector
geometries, and ordinary versus cooperative materialized-source resolution.
Materialized configurations have independently measured tile capacities 8, 16,
and 32. The full bank contains 245 linked symbols and 425 runtime
configurations; the default build remains unchanged.

The expensive CUDA bank is built explicitly for Blackwell and then selected at
runtime:

```text
CARGO_TARGET_DIR=target/windowed-gkr-r0-prototype-bank/build/target \
GPU_GKR_WINDOWED_R0_PROTOTYPE_NATIVE=full CUDAARCHS=120 \
cargo build --release -p gpu_gkr_windowed_bench \
  --features r0-prototype-bank \
  --bin run_windowed_r0_prototype_bank
```

`run_windowed_r0_prototype_bank` accepts runtime `--repo-root`, `--corpus`,
`--artifact-root`, `--output-root`, `--candidate`, `--coordinate`, and `--mode`
arguments. Their `AB_R0_PROTOTYPE_*` environment variables are fallbacks;
explicit CLI values take precedence. Changing a corpus path, candidate subset,
coordinate, materialized capacity, or output destination does not rebuild the
fat executable. Defaults are resolved from a validated repository discovered at
runtime from the working directory or executable, never from a build-worktree
path embedded by `CARGO_MANIFEST_DIR`; the controller passes the binary corpus
path explicitly.
`--mode device-info` emits the same active device/runtime/clock record used by
the execution modes; controllers bind that fresh record before accepting a
Complete checkpoint.

The coordinate-major controller builds and hashes one input, constructs all 32
encoding/capacity descriptors, stages one device input, and then runs every
configuration in-process:

```text
python3 scripts/r0/run-prototype-bank.py correctness
python3 scripts/r0/derive-prototype-sanitizer.py \
  --output ../../target/windowed-gkr-r0-prototype-bank/sanitizer/cover.json
python3 scripts/r0/run-prototype-sanitizer.py
python3 scripts/r0/derive-prototype-screen.py
python3 scripts/r0/run-prototype-bank.py screen
python3 scripts/r0/report-prototype-screen.py
```

The execution controllers default to the post-review schema-v2 replacement
runner/artifact package and distinct `campaign-v4-schema2` output roots. The
offline audit and report commands intentionally retain the immutable v1
`campaign-v3` defaults. Passing the historical runner to a v2 controller fails
because it lacks the required live `device-info` binding.

Correctness uses all 57 R0 coordinates at log 3 and log 12. A physical
per-CTA shared-memory excess is retained as a typed `unlaunchable_capacity`
fact and is never presented as a correctness or performance result. The
production screen uses real log-20-to-log-24 domains and reports raw event
samples plus explicitly named baseline ratios. It intentionally emits no
automatic implementation disposition or tuning decision. Evidence is under
`target/windowed-gkr-r0-prototype-bank/`.

The completed broad screen contains 5,525 typed dispositions: 4,895 launchable
exact-cell/checksum passes and 630 pre-launch shared-capacity facts. Its main
mechanism result is an interaction rather than a universal geometry: ordinary
sources favor the partitioned 96-thread form overall, while capacity-8 source
materialization favors the wide 288-thread form because one staged tile is
shared across all nine warps. The detailed controlled comparisons and Pareto
inputs are summarized in `iteration_times.md` and the report directory above;
they remain descriptive and do not select a production kernel.

That screen is immutable schema-v1 exploratory evidence produced by runner SHA
`9c8f615c...6472`. Independent review found that v1 did not preserve its raw
pilot events, complete device/runtime/clock provenance, or coordinate-level wall
accounting. The source is hardened for future schema v2 runs: observations bind
the complete device record; pilot and retained samples are separate rotated
cross-candidate passes; and CPU/setup, candidate, coordinate, and runner-work wall
intervals are retained. The controller also binds the exact lock-wrapper
path/hash and executed command, hashes the driver transcript, and distinguishes
the controller command wall (which includes lock wait) from runner-reported work
executed inside the proven lock lifecycle. No v2 GPU campaign has been collected, and the v1 rows
must not be attributed to a replacement binary or treated as an approved final
selection campaign.

### Sectioned R0 executor family

The sectioned follow-up keeps the program by value but narrows the hot loops to
four checked sections: BF-wide accumulation, homogeneous linear-E4 wide
accumulation, E4 singleton products, and fixed two-member E4 products. The
generated manifest contains the universal shape plus the 14 shapes occurring
in the 57-coordinate R0 corpus, each under four ownership geometries:
`wide9`, `split3`, `serial3_low`, and deliberately high-register
`serial3_high`. This is still search-space evidence, not a production choice.

Sectioned execution requires the same explicit full native build shown above.
An off/canary runner now rejects `sectioned-correctness` and
`sectioned-screen` before allocating an input. The production screen command
accepts multiple `--coordinate` values, constructs one prepared input and one
device harness per coordinate, and reuses them across the dedicated reference
and all four sectioned geometries. It records CPU construction, H2D/harness
setup, raw pilot/retained CUDA-event samples, and deterministic pass rotation
separately.

The final five-coordinate screen is intentionally descriptive. `split3` was
fastest among the sectioned variants for add/sub, bigint, Blake2, and shift,
while the tiny four-term initialization program slightly preferred `wide9`.
Add/sub L0 reached 10.473920 ms, only 0.190% behind the historical 10.454048 ms
prototype while evaluating the real production program. The largest-memory
shift program remained slower than the frozen current dedicated baseline under
every sectioned geometry. Full raw evidence and explicit faster/slower
comparisons live under
`target/windowed-gkr-r0-sectioned-kernel/review-fix-5/`; these five points must
not be generalized into a universal geometry or treated as launch-bound
tuning.

### Coarse sectioned launch-bound sweep

The follow-up coarse sweep supersedes the earlier no-launch-bounds restriction
only for experimental sectioned kernels. Schema v2 contains 15 corpus shapes
and 15 candidates per shape: fixed `wide9` at `__launch_bounds__(288, 3)`, plus
natural and 7/8/9/10/12/16-block forms of `split3` and `serial3_low`. The
high-register three-warp form remains canary-only and is not a runtime
candidate. All 225 sectioned entry points and the unchanged generic reference
were built once into executable SHA-256
`1d0698657e82b0819a85a4880be0c1cfe0cc6913dc1444de3a062e87acc55260`.

Compiler-differential correctness passed 1,710 exact-shape rows (all 57 R0
coordinates at log 3 and log 12) plus 30 universal-shape compatibility rows.
The descriptive production screen used five coordinates, one prepared input
and one harness per coordinate, and retained 80 arm rows, 240 pilot samples,
and 4,000 interleaved CUDA-event samples. The in-session generic interpreter is
the primary denominator; Task 10 and the historical 10.454048 ms add/sub
prototype are cross-session context only.

The coarse result is deliberately non-universal. Fixed wide-9 is 44.809%,
49.930%, and 24.580% faster than generic on add/sub L0, bigint L0, and Blake2
extended-control L0 respectively, but essentially tied on the four-record
initialization case. Split-3 at 12 blocks is 3.772%, 12.607%, and 28.716%
faster than the same-shape natural split-3 arm on add/sub, bigint, and shift;
it also introduces small stack frames on four of the five shapes. The 16-block
forms force 40 registers, spill on every measured shape, and are much slower,
but remain recorded as data rather than rejected by a hard gate. Low-3 gains
little from 7/8-block bounds and generally slows once constrained further.

The fixed 50-sample ceiling is dominated by setup rather than GPU sampling. On
the shortest frozen coordinate, CPU construction was 11.704424708 s, harness
setup was 0.838764917 s, and the median 16-arm pilot duration was
1.322928011 ms. Even CPU setup alone corresponds to roughly 553 samples per
arm, well above the 50-sample ceiling. No sanitizer campaign was added for this
compile-parameter sweep; correctness and static resource/SASS audits cover all
generated symbols. Complete per-coordinate rows and per-bound summaries are in
`target/windowed-gkr-r0-sectioned-launch-bounds/report/`.

### Active sectioned v4 domain

Schemas v1-v3 and their measurements remain immutable historical evidence.
The active schema-v4 build retires the split/serial geometries and keeps only
`wide9` at `__launch_bounds__(288, 3)` and `__launch_bounds__(288, 4)`. It
compiles the universal executor plus 12 specialized executor shapes, for 26
entry points total. The 14 observed corpus shapes resolve through an explicit
checked dispatch table; two measured supersets remove singleton translation
units: `0x9bf -> 0xbff` and `0xc78 -> 0xc7a`. All other shapes dispatch
exactly.

The live sectioned matrix therefore measures exactly two sectioned arms and no
generic arm. The optional bracketed screen retains the generic reference but
contains only those same two sectioned arms. Both paths preserve the original
50 retained samples per arm. The generator defaults to the merged dispatch;
setting `GPU_GKR_WINDOWED_R0_SECTIONED_SHAPE_POLICY=exact` emits the 14-shape,
30-entry comparison build instead.

After rebasing onto `av_gkr_compiler` at `df8e87756be59887be093382058394ed5aa83bc3`,
the exact and merged policies were built separately and compared on all five
coordinates affected by the three aliases. Each policy passed ten log-3
correctness rows and ten Compute Sanitizer rows. Production-log timing used 50
retained samples for both b3 and b4, with exact and merged executions paired
under one GPU lock and policy order alternated by coordinate. Negative deltas
mean the merged policy was faster:

| coordinate | role | b3 merged delta | b4 merged delta |
| --- | --- | ---: | ---: |
| `unsigned_mul_div:0` | `0x3fb -> 0xbff` donor | -1.226% | +3.606% |
| `bigint_with_extended_control:0` | `0x9bf -> 0xbff` donor | +0.253% | -0.235% |
| `unified_reduced_machine:0` | `0xbff` receiver | -0.278% | -0.144% |
| `mem_subword_only:1` | `0xc78 -> 0xc7a` donor | -0.009% | -0.529% |
| `mem_word_only:1` | `0xc7a` receiver | -0.149% | -0.250% |

The `0x9bf` and `0xc78` aliases are neutral at this resolution, as are both
receivers. The initial `0x3fb -> 0xbff` alias had a launch-bound-dependent
tradeoff: b3 improved slightly, while b4 regressed 3.606%. Because b4 is a
retained arm, the final default restores exact `0x3fb` specialization. A final
same-lock recheck measured b4 at 11.041792 ms versus 11.036912 ms for the exact
control (+0.044%), eliminating the regression; b3 was 1.535% faster in the
final linked binary. Strict replay output is under
`target/windowed-gkr-r0-shape-merge-ab/`.

### Arbitrary-union shape bank

The follow-up union-bank experiment measures incomparable shape merges as well
as donor-to-superset aliases. Setting
`GPU_GKR_WINDOWED_R0_SECTIONED_SHAPE_POLICY=union_bank` expands the 14 observed
shape masks to their complete nonzero bitwise-OR closure: 33 compiled masks and
66 `wide9` entry points (`b3` and `b4`). The generated schema-v4 dispatch stays
exact for normal execution; the measurement runner's checked `compatible`
policy may invoke a compiled mask only when it is a semantic bit superset of
the coordinate's lowered mask. The default generated tree remains the smaller
merged policy after the experimental binary is frozen.

All 2,212 compatible coordinate/mask/bound arms pass at log 3 and log 12, and
the same 2,212 log-3 arms pass Compute Sanitizer with zero reported errors. A
single production-domain timing session constructs one input and one GPU
harness per coordinate, then rotates every compatible arm through 3 pilot and
50 retained CUDA-event samples. This avoids multiplying the dominant CPU
setup cost by the number of merge candidates.

The descriptive result strongly favors a small bank but does not select one.
Allowing each retained compiled mask to use its better measured b3/b4 arm, a
single universal `0xfff` mask is 0.882% slower than 14 exact masks by the
unweighted sum of the 57 coordinate medians. Exact partition optimization over
all observed-shape subsets reaches a broad plateau at 3-8 specializations; the
best six-specialization partition is 0.524% faster than the exact bank in this
single session. The universal b3 arm is not uniformly cheap: relative to the
same-bound exact arm it is 28.755% slower for native `0x001` and 19.062% slower
for `0x1b7`. Full 2,212-row timing, 360 native-to-compiled summaries, all 66
static resource/SASS rows, per-coordinate choices, and the 1-14 specialization
frontier are under `target/windowed-gkr-r0-union-bank/report/`. Sub-percent
ordering is search guidance, not a production selection.

## Deliberate limitations

- No CPU/GPU result comparison or transcript integration.
- No challenge binding after the 27-cell output.
- No reuse of source loads across the 9 warps.
- No shared-memory staging or communication between warps; the shared
  accumulator cells are thread-private.
- The checked-in artifact is specific to add/sub layer 0.

These choices keep the first version easy to change while exposing the real
allocation sizes, address geometry, instruction mix, and memory-access shape.
