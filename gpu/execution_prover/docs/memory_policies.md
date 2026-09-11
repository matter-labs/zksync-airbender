# Offline memory policies

The execution prover defaults to an exact **30 GiB arena**. Witness cosets stay
materialized through WHIR; setup and memory materialize at their separate
openings. This preset fits all 12 circuits with the largest follower's complete
inputs resident. Context, driver allocations and NTT tables are outside the arena.
The target is RTX 5090; measurements used RTX PRO 6000 Blackwell.

The Rust sweep retains all 90 policy candidates, including retained-monomial
and in-place recomputation. It uses maximum-capacity synthetic inputs, two warm
proofs and interleaved timing rounds. Its proof fingerprints must agree across
policies; CPU-proof parity is checked separately.

## Measure and install a preset

Build with default features plus `memory_sweep`, outside the GPU lock:

```sh
cargo check -p gpu_execution_prover --features memory_sweep --bin gpu_memory_sweep
cargo build -p gpu_execution_prover --features memory_sweep --release --bin gpu_memory_sweep
mkdir -p target/memory-policy
.agents/bin/with_gpu_lock.sh target/release/gpu_memory_sweep \
  --arena-gib 30 --rounds 5 \
  --configuration setup_full-memory_full-witness_full-opening_keep_cosets \
  --output-csv target/memory-policy/30-gib.csv

target/release/gpu_memory_sweep --generate-policy \
  --input-csv target/memory-policy/30-gib.csv \
  --output-rust target/memory-policy/generated.rs
```

Omit `--configuration` to compare all candidates. Budgets accept fractional GiB
in multiples of 1 MiB. Use `--circuit` for shorter lock acquisitions and merge
same-budget CSV rows before generation. `--fit-only` skips timing for diagnostics.
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
