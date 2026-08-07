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

- One CUDA block owns one 8-row Boolean cube.
- The block has 9 warps (288 threads), one warp for each `(x0, x1)` output
  pair.
- Each warp evaluates the same segmented layer-0 VM program and accumulates
  its 3 `x2` values independently. There is no K split and no block barrier in
  the VM kernel.
- Each thread's three long-lived E4 accumulators use private cells in a
  cell-major 13,824-byte block-shared allocation. The kernel uses 56 registers
  per thread and requests a 60% shared-memory carveout, which selects the 64
  KiB partition and permits four resident blocks on the benchmark's RTX PRO
  6000 Blackwell Server Edition. The percentage is a device-tuned hint, not a
  portable partition guarantee.
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

The complete control descriptor is passed by value as a 1,536-byte
`__grid_constant__` kernel argument. Its 175 aligned program records, 6
host-resolved window bases, and 7 immediates are inline; only the
input/equality/output data remains pointer-backed. Each ordinary source
operand directly packs a 7-bit relative column and a 6-bit window into its
existing `u16` instruction field. Because all sources share the trace domain,
the kernel computes `log_trace` once and uses typed pointer arithmetic for
`window_base + (column << log_trace)`. There is no source-ID table or device
source-metadata indirection.

The two virtual-setup windows are addressless and allocate no storage. The
four terms that consume them use two explicit cold BF classes: procedural
linear-A and direct-BF-by-procedural-B. Their source field stores one of the
four procedural kinds, and a small CUDA source synthesizes the requested row
before reusing the common triplet interpolation. Ordinary BF classes are
rejected if they name a virtual window, so the hot direct resolver contains no
procedural discriminator. Real input families remain independent allocations.

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
before a group's linear tail and marks reduction boundaries of at most four
products; omitting it regenerates the eager-reduction comparison artifact.
`compiler`, `control-atoms`, and `control` are available for A/B experiments.
This experimental artifact is replaced in place rather than migrated through
format versions. Drift is acceptable for this crate; regeneration is an
explicit operation.

## Deliberate limitations

- No CPU/GPU result comparison or transcript integration.
- No challenge binding after the 27-cell output.
- No reuse of source loads across the 9 warps.
- No shared-memory staging or communication between warps; the shared
  accumulator cells are thread-private.
- The checked-in artifact is specific to add/sub layer 0.

These choices keep the first version easy to change while exposing the real
allocation sizes, address geometry, instruction mix, and memory-access shape.
