# gpu_prover

## How to add a new circuit

The active GPU path has two circuit families:

- unrolled execution circuits, described by `CircuitType::Unrolled(...)` in `src/circuit_type.rs`
- delegation circuits, described by `CircuitType::Delegation(...)` in `src/circuit_type.rs`

### Adding a new unrolled execution circuit

- under `native/witness/circuits`, add a new `name_of_the_circuit.cu` file by copying the closest existing unrolled kernel
- adjust the `NAME` inside the new file
- add the new file to `native/CMakeLists.txt` so it is built into `gpu_prover_native`
- add or extend the matching enum variant in `src/circuit_type.rs`
  - use `UnrolledMemoryCircuitType` for load/store-style families
  - use `UnrolledNonMemoryCircuitType` for arithmetic and control-flow families
  - update `UnrolledCircuitType::Unified` only if you are changing the unified reduced recursion circuit itself
- wire the witness kernel in `src/witness/witness_unrolled.rs`
- update `src/witness/memory_unrolled.rs` if the circuit needs different RAM or lookup-layout handling
- add the corresponding precomputation handling in `src/execution/precomputations.rs`
- update `src/execution/tracing.rs` and `src/execution/prover.rs` so the new circuit can be scheduled and traced by the active replay pipeline

### Adding a new delegation circuit

- under `native/witness/circuits`, add a new `name_of_the_circuit.cu` file by copying the closest existing delegation kernel
- adjust the `NAME` inside the new file
- add the new file to `native/CMakeLists.txt` so it is built into `gpu_prover_native`
- add a new `DelegationCircuitType` variant in `src/circuit_type.rs`
- add the mapping to and from the delegation type id in `src/circuit_type.rs`
- wire the witness kernel in `src/witness/witness_delegation.rs`
- update `src/witness/memory_delegation.rs` if the delegation ABI changes the RAM access layout
- add the corresponding precomputation handling in `src/execution/precomputations.rs`
- update `src/execution/tracing.rs` so replay emits the right trace payload for the new delegation

## GPU memory sweep

`gpu_memory_sweep` tries every supported circuit and all 16 coset-cache policies against exact
device-arena sizes. Setup and proof trees always use partial caching. The sweep records a simple
fit result, the allocator's existing high-water mark, and proof timing. It does not trace
individual allocations.

Build the release binary with deterministic proof-of-work:

```bash
RUST_MIN_STACK=33554432 CARGO_BUILD_JOBS=2 \
  cargo build -p gpu_prover --release --bin gpu_memory_sweep \
  --features "memory_sweep,deterministic_pow"
```

Run a sweep while holding the machine's GPU lock. Adapt the lock path to the machine-wide
convention:

```bash
mkdir -p target/gpu-memory
flock /tmp/zksync-airbender-gpu.lock \
  target/release/gpu_memory_sweep \
  --arena-gib 21.5 --rounds 5 --output-csv target/gpu-memory/21.5-gib.csv
```

The runner uses 80-bit security, warms every setup cache, and performs one untimed all-recompute
proof before timing. Timing rounds are the outer loop, so every fitting configuration is run once
before the next round starts. Synthetic inputs have maximum supported shapes but arbitrary values;
the resulting proofs are intentionally not verified.

Every case overlaps the target proof with the supported circuit having the largest device-input
footprint as the next pipeline request. Thus `fits` and `peak_bytes` include the single worst-case
next-input overlap.

The CSV fields are:

- `arena_bytes`: exact root device-arena reservation, including the nested small pool.
- `circuit`: stable circuit name.
- `configuration`: stable name of the four coset choices.
- `setup`, `witness`, `memory`, `stage_two`: `CacheFull` or `CacheSingle`.
- `fits`: whether the proof completed without exhausting the root arena.
- `input_bytes`: the current circuit's statically rounded setup evaluations, cached partial setup
  trees, decoder, trace, and init/teardown device input size.
- `peak_bytes`: root allocator high-water mark for a fitting discovery run.
- `timing_samples`: number of timed proofs.
- `median_ms`, `min_ms`, `max_ms`: proof-stage timing summary.
- `preferred`: fastest fitting configuration for this arena and circuit by median time, with the
  stable configuration name breaking ties.

Generate a candidate Rust table from one arena's CSV:

```bash
target/release/gpu_memory_sweep \
  --generate-policy \
  --input-csv target/gpu-memory/21.5-gib.csv \
  --output-rust target/gpu-memory/generated-low-vram-policy.rs

rustfmt --edition 2021 target/gpu-memory/generated-low-vram-policy.rs
diff -u gpu_prover/src/prover/low_vram_policy.rs \
  target/gpu-memory/generated-low-vram-policy.rs
```

Replacing the production table is a manual, reviewed copy. A result CSV may be committed when
the policy changes, but normal and reproducible builds never consume measurement artifacts.
