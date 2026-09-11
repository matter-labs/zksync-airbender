# Offline memory policies

The execution prover defaults to an exact **30 GiB arena**, using full witness
materialization with cosets retained through WHIR. Setup and memory materialize
at their separate openings. This preset covers all 12 circuits without coset
recomputation. Context, driver allocations and NTT tables are outside the arena.

Selection uses the largest measured threshold within the arena capacity and
requires matching circuit artifacts, proof configuration, allocator geometry
and leaf encoding. Unsupported profiles and smaller budgets fail admission.
GPU model is measurement provenance, not a compatibility key. The target is
RTX 5090; measurements were made on RTX PRO 6000 Blackwell, not RTX 5090.

The offline sweep retains 90 candidates for future budgets: three opening
strategies (full cosets, retained monomials with one coset workspace, in-place
conversion) for setup and memory, and ten witness commitment/opening transitions.
Witness commitment can keep cosets, keep evaluations plus monomials, or restore
only evaluations. Raw evaluations remain live through sumchecks and initial WHIR
batching. Witness, memory and setup openings run separately so their coset
workspaces do not add up.

## Measure and generate

Build outside the GPU lock and freeze the binary for the campaign:

```sh
cargo check -p gpu_execution_prover --features memory_sweep --bin gpu_memory_sweep
cargo build -p gpu_execution_prover --features memory_sweep --release --bin gpu_memory_sweep
mkdir -p target/memory-policy/sweep
cp target/release/gpu_memory_sweep target/memory-policy/sweep/gpu_memory_sweep
python3 gpu/execution_prover/scripts/memory_sweep.py \
  --binary target/memory-policy/sweep/gpu_memory_sweep \
  --output-dir target/memory-policy/sweep/results \
  --budgets-gib 30 \
  --configurations setup_full-memory_full-witness_full-opening_keep_cosets \
  --emit-rust target/memory-policy/sweep/measured.rs
```

Pass explicit budgets in GiB (multiples of 1 MiB); omit `--configurations` to
search all candidates. Each circuit runs under a separate GPU lock acquisition,
with two warm proofs and five timed rounds. A budget is accepted only when all
12 circuits fit with the largest follower's complete inputs resident.

Inputs are synthetic maximum-capacity probes, not valid VM execution proofs;
CPU-proof parity is a separate check. Every policy must reproduce the circuit's
proof fingerprint. `--fit-only` and restricted `--circuits` runs cannot emit
presets. `--resume` validates binary identity and saved results. CSV samples,
logs and device snapshots remain in the output directory.

Review accepted measurements before installing the generated Rust as
`src/memory_policy/generated.rs`. Rebuild, then replay each circuit through
normal worker admission and selection:

```sh
.agents/bin/with_gpu_lock.sh target/release/gpu_memory_sweep \
  --replay-presets --arena-gib 30 --rounds 5 \
  --configuration setup_full-memory_full-witness_full-opening_keep_cosets \
  --circuit delegation_big_int_with_control --output-csv target/replay-bigint.csv
```

Repeat for all circuits and budgets; compare fingerprints, peaks and paired
proof times with the measured winners. Replay rows cannot generate presets.
Regenerate after changes to geometry, allocation lifetimes or scheduling.
Arena fragmentation can require more capacity than the recorded peak.
