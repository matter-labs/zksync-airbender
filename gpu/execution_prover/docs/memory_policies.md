# Offline memory policies

The execution prover uses offline-generated presets for device-memory arenas.
Automatic initialization selects a preset after reserving slack, context
allocations and NTT tables. When at least 31 GiB remains available, it allocates
30 GiB with the calibrated 29 GiB policy, leaving at least 1 GiB unclaimed in
addition to the reserved slack. This is a workaround for allocation placement
failures observed with the 29 GiB arena. Smaller devices retain the 21/29 GiB
selection. Callers can select an explicit preset
through `ExecutionProverConfiguration::memory_preset`; it allocates that arena or
fails. The default is `MemoryPreset::Auto`. Explicit `MemoryPreset::GiB29` retains
the exact 29 GiB arena and does not receive Auto's extra placement space.

```rust
use gpu_execution_prover::{ExecutionProver, ExecutionProverConfiguration, MemoryPreset};

let config = ExecutionProverConfiguration {
    memory_preset: MemoryPreset::GiB21,
    ..Default::default()
};
let prover = ExecutionProver::with_configuration(config)?;
```

An advanced explicit arena block count can be used with `Auto`; it remains exact
and selects the largest policy preset no larger than that arena. Combining an
explicit preset with an explicit block count is rejected. An arena below the
smallest preset is rejected. Each preset must cover every circuit with the
largest follower's complete inputs resident. Context, driver allocations and NTT tables are outside the arena.

The sweep compares supported policy combinations, including retained-monomial
and in-place recomputation. It uses maximum-capacity synthetic inputs, warmup
proofs and interleaved timing rounds. Its proof fingerprints must agree across
policies; CPU-proof parity is checked separately.

Peak allocation counters are reset by the sweep before each complete case,
including target and follower input staging. Production proving does not reset
them. Older measurements taken while `prove()` reset the counter exclude
earlier staging peaks and must be remeasured before comparison. The committed
policy table predates this correction; its allocation-fit results are unchanged,
but its historical peak measurements are not comparable with the corrected ones.

GKR policies select how many early value layers and cache layers to omit.
The forward pass uses bounded temporary storage to materialize the retained tail;
the backward pass replays the dependencies of missing inputs before consuming them.
Required carries remain materialized. `Materialize` keeps the full forward output.

Witness has three choices: commitment strategy (`AllCosets`, `PerCoset`,
`InPlace`), storage after commitment (`RawEvaluations`, `RawAndMonomials`,
`RawAndCosets`), and opening strategy (`ReuseCosets` or reconstruction via
`AllCosets`, `PerCoset`, `InPlace`). Raw evaluations remain until initial WHIR
batching. Setup and memory each have only an opening strategy. `PerCoset` uses
monomials plus one reusable coset workspace; it does not imply retaining
monomials between commitment and WHIR.

## Measure and install a preset

Set `ARENA_GIB` to the budget to qualify and `ROUNDS` to the number of timed rounds.
Build with default features plus `memory_sweep`, outside the GPU lock:

```sh
cargo check -p gpu_execution_prover --features memory_sweep --bin gpu_memory_sweep
cargo build -p gpu_execution_prover --features memory_sweep --release --bin gpu_memory_sweep
mkdir -p target/memory-policy
.agents/bin/with_gpu_lock.sh target/release/gpu_memory_sweep \
  --arena-gib "$ARENA_GIB" --rounds "$ROUNDS" \
  --output-csv target/memory-policy/sweep.csv

target/release/gpu_memory_sweep --generate-policy \
  --input-csv target/memory-policy/sweep.csv \
  --output-rust target/memory-policy/generated.rs
```

Use `--configuration` to restrict the policy candidates. Budgets accept fractional
GiB aligned to the allocator block size. Use `--circuit` for shorter lock
acquisitions and merge CSV rows before generation. `--fit-only` skips
timing for diagnostics.
Generation requires a timed, fitting winner for every circuit at each included
budget. Include only the budgets intended for installation.

Review the results, then copy the generated Rust to `gpu/circuit_prover/src/proof/memory_policy/presets/generated.rs`,
format and rebuild. Its arena list determines policy budgets (with the Auto
placement workaround described above); its exhaustive
circuit matches select each policy. Validate each installed preset with
`--replay-presets` and the same budget/circuit/output arguments. Replay exercises
installed preset selection and produces no preferred rows. Compare fingerprints,
peaks and paired proof times before shipping.

Keep measurements and captures outside git. Regenerate from one frozen build
when circuit geometry, allocator configuration, features, or scheduling change;
presets carry no runtime geometry fingerprint.
