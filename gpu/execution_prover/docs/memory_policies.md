# Offline memory policies

Current memory measurements: [PR #434 remeasurement](memory_requirements_pr434.md).
Previous implementation and timing checkpoint: [September 8](memory_policy_checkpoint.md).

The execution prover selects measured policies from a generated table. It does
not search or dry-run on production inputs. This is the v3 port of the v2
`gpu_prover/src/memory_sweep` harness on `dev`.

A budget is the device-arena capacity, including its small-allocation pool.
CUDA context allocations, NTT tables and driver overhead are outside this
capacity. An accepted budget must fit **every supported circuit**, including
bigint, with the largest next circuit's inputs resident. A partial circuit set
cannot produce a deployment preset.

## Policy choices

Setup and memory always defer coset generation until their separate base-layer
openings. Each can materialize all cosets, retain monomials and use a coset
workspace, or transform the source in place between cosets. Witness, memory and
setup openings run separately, so their coset workspaces do not add up.

Witness commitment has three strategies:

- Full materialization: retain cosets through WHIR, or drop them after commitment
  and choose any of the three opening strategies.
- Retain evaluations and monomials: stream commitment cosets through a workspace,
  keep no cosets afterwards, and choose any opening strategy.
- In-place commitment: restore raw evaluations after building the commitment,
  keep no monomials or cosets afterwards, and choose any opening strategy.

Proof and memory-commitment jobs release device input reservations once their
last readers are enqueued. Their host input owners and transfer callbacks remain
alive through completion, so an uncollected preceding job does not retain
another device input bundle. This requires no D2D copy or host synchronization.

Raw evaluations remain available for sumchecks and initial WHIR batching. The
choices produce 3 setup × 3 memory × 10 witness transitions = 90 policies.
The default uses full materialization at the deferred setup/memory openings and
retains witness cosets. Recomputation is a measured memory/time tradeoff.

## Run the sweep

Build without holding the GPU lock, then freeze the binary for the whole sweep:

```sh
cargo check -p gpu_execution_prover --features memory_sweep --bin gpu_memory_sweep
cargo build -p gpu_execution_prover --features memory_sweep --release --bin gpu_memory_sweep
mkdir -p target/memory-policy/sweep
cp target/release/gpu_memory_sweep target/memory-policy/sweep/gpu_memory_sweep
python3 gpu/execution_prover/scripts/memory_sweep.py \
  --binary target/memory-policy/sweep/gpu_memory_sweep \
  --output-dir target/memory-policy/sweep/results \
  --emit-rust target/memory-policy/sweep/measured.rs
```

The coordinator acquires the shared GPU lock separately for each circuit. Its
default grid is 16–48 GiB in 2 GiB steps, descending, with 0.5 GiB refinement
near fit boundaries and policy changes. It tests bigint first and rejects a
budget as soon as one circuit has no fitting policy. Five measured rounds
follow two warm runs per fitting policy, with rounds outside the policy loop.
The target's inputs use normal placement; the largest follower uses reversed
placement, matching the production worker's overlap.

The factory uses maximum-size synthetic traces, production setup builders and
GPU-generated memory caps. These are allocation/performance probes, not valid
VM execution proofs. Every successful policy must produce the same proof
fingerprint for a circuit. Functional CPU-proof parity remains a separate gate.

`--fit-only` collects per-circuit fit and peak diagnostics, including failures,
and cannot generate presets. `--circuits` restricts a diagnostic run.
`--resume` checks the binary identity and revalidates complete result files;
incomplete timings are rerun. Raw CSV samples, logs, GPU/process snapshots and
artifact identities remain in the output directory. `accepted.csv` contains
only budgets that passed for all circuits.

## Install and use measured presets

Review the measurements and validate finalists before replacing
`src/memory_policy/generated.rs` with the generated Rust output. Rebuild and
replay the selected policies through the production worker. Generation rejects
incomplete budgets, invalid timing/fit evidence and duplicate thresholds.

For replay, rebuild the sweep binary with the candidate table, then run one
circuit per GPU lock acquisition:

```sh
.agents/bin/with_gpu_lock.sh target/release/gpu_memory_sweep \
  --replay-presets --arena-gib 38 --rounds 5 \
  --circuit delegation_big_int_with_control --output-csv target/replay-bigint.csv
```

Repeat for every circuit and emitted budget. Replay uses normal worker admission
and policy selection for both target and follower, with no overrides. It records
two warm proofs followed by timed rounds; compare its policy, proof fingerprint,
fit and time to the corresponding sweep winner. `--configuration` can assert the
expected policy. Replay rows are never marked as candidates for generation.

Set `ExecutionProverConfiguration::prover_context_config`'s
`device_arena_budget_bytes` to an accepted arena capacity in bytes. Exact arenas
never silently shrink. Explicitly budgeted workers require a measured device
and leaf-encoding profile at startup, and matching circuit geometry before
input transfers. Compatibility includes the compiled circuit artifact, full
proof configuration, allocator block/pool geometry, sweep schema, leaf encoding
and device geometry. Selection uses the largest measured threshold no greater than
the actual arena capacity. Recheck fit when moving between thresholds: arena
fragmentation can require more space than the recorded allocation peak.

Regenerate presets after changes to circuit geometry, scheduling, allocation
lifetimes or kernels that affect the policy tradeoff. The PR #434 base now
includes the bigint and mul/div trace reductions and eight-set standalone I&T;
use the new measurements linked above rather than the September 8 results.
