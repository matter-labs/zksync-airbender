# Offline memory policies

The execution prover uses offline-generated presets for device-memory arenas.
Automatic initialization selects the largest preset that fits after reserving
slack, context allocations and NTT tables. Callers can select an explicit preset
through `GpuBackendConfiguration::memory_preset`; it allocates that arena or
fails. The default is `MemoryPreset::Auto`.

```rust
use gpu_execution_prover::{
    ExecutionProver, ExecutionProverConfiguration, GpuBackendConfiguration, MemoryPreset,
};

let config = ExecutionProverConfiguration {
    backend: GpuBackendConfiguration {
        memory_preset: MemoryPreset::GiB21,
        ..Default::default()
    },
    ..Default::default()
};
let prover = ExecutionProver::with_configuration(config);
```

An advanced explicit arena block count can be used with `Auto`; it remains exact
and selects the largest policy preset no larger than that arena. Combining an
explicit preset with an explicit block count is rejected. An arena below the
smallest preset is rejected. Each preset must cover every circuit with the
largest follower's complete inputs resident. Context, driver allocations and NTT tables are outside the arena.

Presets select defaults; they are not a capability allowlist. Direct proof calls
may use any policy satisfying the representation and backend constraints below,
within the currently admitted commitment geometry and the actual arena capacity.
There is no preset-membership check or estimated-memory rejection.

The sweep compares valid policy combinations, including retained-monomial
and in-place recomputation. It uses maximum-capacity synthetic inputs, warmup
proofs and interleaved timing rounds. Its proof fingerprints must agree across
policies; CPU-proof parity is checked separately.

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

## Policy compatibility

The same preflight validates direct proofs and execution worker/sweep requests
before constructing H2D transfers. It checks the actual setup, memory and witness
representations, including empty roles. The immutable config, artifact, setup-cache
and cap geometry must agree; choosing a different memory policy cannot change that
identity or the proof protocol.

For `GkrMemoryPolicy::Recompute`, at least one omission count must be nonzero,
`value_layers` must be smaller than the runtime circuit's MAIN layer count, and
`cache_layers` must not exceed that count. One validator is shared by preflight
and the replay plan. The final MAIN value layer and required carry/producer
closure must remain available. These requirements apply to legacy, physical,
virtual and merged commitments alike; they do not depend on preset membership.
See [`GkrMemoryPolicy`](../../gkr/src/forward/recompute.rs) and
[`RecomputePlan`](../../gkr/src/forward/recompute_plan.rs).

The witness representation contract is:

| Commitment | Storage after commitment | Opening |
| --- | --- | --- |
| AllCosets | RawAndCosets | ReuseCosets |
| AllCosets | RawEvaluations or RawAndMonomials | Recompute(AllCosets, PerCoset or InPlace) |
| PerCoset | RawEvaluations or RawAndMonomials | Recompute(AllCosets, PerCoset or InPlace) |
| InPlace | RawEvaluations | Recompute(AllCosets, PerCoset or InPlace) |

ReuseCosets needs retained cosets. PerCoset does not retain all cosets, and InPlace
restores raw evaluations without retaining monomials. Recomputed openings require
no materialized cosets at the destructive handoff; therefore RawAndCosets with
Recompute is outside the current representation contract, even though a different
lifecycle could compute it. These are storage dependencies, not statements of
algebraic impossibility or measured dominance. The source of truth is
[`WitnessMemoryPolicy::is_valid`](../../circuit_prover/src/proof/memory_policy.rs).

Setup and memory independently accept AllCosets, PerCoset or InPlace openings.
Witness commitment and opening may use different strategies according to the
table. A merged proof concatenates memory then witness before packing; its
combined oracle uses the memory opening strategy, and its separate witness oracle
is empty. No transform is required for an empty role. GKR continues reading
logical columns while WHIR batches the padded physical columns. InPlace
commitment restores the raw backing before logical readers; destructive query
reconstruction runs only after those readers and initial WHIR batching release
the raw owner. The same ownership checks apply to merged aliases.

### Backend and direct-holder constraints

These limits describe the current implementation, independently of memory-policy
selection. They do not add a policy allowlist to an admitted geometry.

| Constraint | Reason and source |
| --- | --- |
| InPlace transform domain log 20..24 | The existing exact-aliasing transform family supports that range. The shared `gpu_ntt::ntt::log_size_supports_in_place` predicate is checked at the BabyBear boundary before cap/workspace allocation or taking the raw owner. |
| Packed retained-monomial PerCoset domain log 20..24 | The retained transform dispatch has that existing range; it checks aligned whole columns and root order. See [`retained_monomials.rs`](../../ntt/src/ntt/retained_monomials.rs). |
| Packed base transform message log at most 24, codeword log at most 27 and at most the live twiddle capacity | Natural-order coefficient labeling and the BabyBear root order must match the committed domain. The small legacy MSB route is not a substitute. All currently admitted packed/virtual domains have message log 22 or 24. |
| Cap at least LDE; Partial trees require room for the fixed 32-leaf boundary | Per-coset cap arithmetic and the cached partial-tree layout require these dimensions. The field-free holder validation owns them. |
| Recomputed direct-holder queries require None or Partial trees | The current gather reconstructs paths through partial-tree boundary roots; a Full tree needs a different gather. Current proof policies never construct Full trees. |
| Direct packed retained commit requires None cosets and Partial trees | Its outer entry selects the partial-tree representation; None/Full tree variants need other transient/tree handling. The inner Full-coset/Partial branch does not make the outer packed entry callable in that state. Current stage1 starts with None cosets and Partial trees. |
| Raw take requires a unique owner and the required retained source | Destructive transforms cannot race logical readers or merged aliases. RawAndMonomials/RawAndCosets require their producer to have retained that source; assertions remain in the holder. |

See [`holder`](../../trace/src/trace/holder/mod.rs) and
[`openings`](../../trace/src/trace/holder/openings.rs) for these direct-holder
checks. BabyBear capability checks stay at the instantiated backend boundary;
structural holder and geometry interfaces remain field-generic.

### Geometry and protocol scope

Memory-policy compatibility does not widen geometry admission. Current separate
packed proof shapes are physical `(n,k,f)=(20,2,1),(20,4,1),(23,1,1)` and virtual
`(22,0,0),(20,2,0)`. The virtual schedule uses message log 22, base LDE 2, cap 16
and fold ladder `[0,6,5,5,5]`. Merged packed proof admission remains Blake
compression `(20,4,1)`, LDE 2, cap 16. These are the existing geometry/circuit
qualification lists, preserved separately from policy compatibility; they are
not proofs that other geometries are impossible. Existing legacy routes remain.

The current base batching implementation supports fold log 0 or 1. Recursive
oracle dispatch, partial-tree dimensions, field/root order and context capacity
remain independently validated. Physical claim merging supports k1..4; k0 bypasses
the merge kernel. The memory-only producer remains separate-only; merged jobs use
the concatenating producer instead.

Schedules with multiple OOD samples, OOD PoW or folding PoW remain rejected. The
GPU proof layout/scheduler handles one OOD tuple per oracle and does not implement
the additional transcript/nonce steps for those schedules. These protocol limits
are outside memory-policy compatibility. See
[`recursive schedule admission`](../../whir/src/lib.rs) and
[`proof layout inputs`](../../gkr/src/proof_layout/build_inputs.rs).

### Verification scope and fit

The positive policy suites compare full serialized GPU proofs with fresh CPU
proofs, keep two GPU jobs pending, and require the allocator to return to baseline
after every pair. They vary setup×memory openings, witness representations and GKR
omission counts using the existing candidate families. Primitive tests separately
compare caps, leaves, paths, restored raw data and zero tails. This is family
coverage, not the complete Cartesian product. GKR replay on physical Blake
`(20,2,1)` has the same logical views and k2 padded backing as virtual Blake
`(20,2,0)`; only WHIR's base fold differs. That is a source-level equivalence
argument, not a measured physical-f1 GKR candidate run.

A paired-proof allocation failure describes that exact arena and pending work;
it does not establish a single-proof incompatibility. In particular, the measured
BigInt Materialize/AllCosets pair exceeds a 30 GiB arena. Its opening/witness
family tests use the existing 30 GiB preset GKR policy while varying those
families. Materialize remains callable. Allocation failures must retain the
policy tuple, arena, stage and requested bytes; parity, dispatch or ownership
failures must not be classified as non-fit. No policy is pruned as dominated.

Preset replay checks fit and stable GPU fingerprints with the largest follower's
inputs resident, in both allocation directions. It is separate from the
independent CPU-byte oracle. A Cartesian `--fit-only` map is tuning work, not a
prerequisite or a claim of this compatibility change. Regenerating presets still
requires the per-circuit CPU policy parity and exact-arena replay checks.

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
format and rebuild. Its arena list determines automatic allocation; its exhaustive
circuit matches select each policy. Validate each installed preset with
`--replay-presets` and the same budget/circuit/output arguments. Replay exercises
installed preset selection and produces no preferred rows. Compare fingerprints,
peaks and paired proof times before shipping.

Keep measurements and captures outside git. Regenerate from one frozen build
when circuit geometry, allocator configuration, features, or scheduling change;
presets carry no runtime geometry fingerprint.
