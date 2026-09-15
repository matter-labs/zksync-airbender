# Offline memory policies

The execution prover uses an offline-generated preset for an exact device-memory
arena. A preset must cover every circuit with the largest follower's complete
inputs resident. Context, driver allocations and NTT tables are outside the arena.

The sweep compares supported policy combinations, including retained-monomial
and in-place recomputation. It uses maximum-capacity synthetic inputs, warmup
proofs and interleaved timing rounds. Its proof fingerprints must agree across
policies; CPU-proof parity is checked separately.

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
acquisitions and merge same-budget CSV rows before generation. `--fit-only` skips
timing for diagnostics.
Generation requires a timed, fitting winner for every circuit at one budget.

Review the results, then copy the generated Rust to `src/memory_policy/generated.rs`,
format and rebuild. Its arena constant sets the default allocation; its exhaustive
circuit match selects each policy. Validate the installed preset with
`--replay-presets` and the same budget/circuit/output arguments. Replay exercises
normal worker selection and produces no preferred rows. Compare fingerprints,
peaks and paired proof times before shipping.

Keep measurements and captures outside git. Regenerate from one frozen build
when circuit geometry, allocator configuration, features, or scheduling change;
presets carry no runtime geometry fingerprint.
