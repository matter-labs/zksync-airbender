# Fixed 30 GiB memory policy

The execution prover defaults to a **30 GiB device arena** (32,212,254,720 bytes),
including the small-allocation pool. The release targets RTX 5090. GPU model
geometry is measurement provenance, not an admission key; circuit artifacts,
proof configuration, allocator geometry, leaf encoding and sweep schema must
still match the installed measurements.

There is one threshold and one policy, covering all 12 circuits:

- Full witness commitment, retaining cosets through WHIR.
- Setup and memory cosets generated at their separate openings, with full
  materialization for each.
- No coset recomputation. The existing recomputation variants and offline
  multi-budget machinery remain available for later releases.

`ExecutionProverConfiguration::default()` sets the exact arena budget. It does
not allocate a smaller arena on failure. Context/driver allocations and NTT
tables remain outside the arena. Smaller budgets have no installed preset.

## Exact-budget evidence

All 12 circuits fit the exact 30 GiB arena with the largest follower's complete
inputs resident. The selected configuration was fixed before measurement:
`setup_full-memory_full-witness_full-opening_keep_cosets`. This release does
not claim that policy is the fastest of the 90 candidates.

Each circuit had two warm proofs and five timed proofs. All fingerprints
matched the prior PR434 measurements; all workers exited cleanly and released
their allocator reservations. The inputs are synthetic maximum-capacity probes,
not a valid VM-execution corpus.

| Circuit | Peak GiB |
| --- | ---: |
| Bigint | 21.1328 |
| Blake2 compression | 27.4619 |
| Blake2 G | 15.7275 |
| Keccak | 29.4443 |
| I&T | 11.5254 |
| Load/store subword | 25.9385 |
| Load/store word | 22.0693 |
| Add/sub/LUI/AUIPC/MOP | 23.9902 |
| Jump/branch/SLT | 27.6191 |
| Mul/div unsigned | 17.4639 |
| Shift/binary | 29.8115 |
| Unified | 23.3682 |

Shift/binary leaves 193 MiB of arena headroom. This excludes memory outside the
arena; it is not a measurement of total device memory use.

The baseline is merged `av_gkr_compiler` at `bc55aad87` (#434). Its tree is
identical to the previously measured PR head `4c8f0b739`, so the rebase does not
change those inputs or kernels. Measurements ran on an RTX PRO 6000 Blackwell
Server Edition, 188 SMs, 128 MiB L2, driver 610.57.04. Direct RTX 5090 execution
and timing are not measured here.

## Validation

The CPU policy tests cover portable selection, rejection below the installed
threshold, stale artifact rejection, complete circuit coverage at the default
budget, and duplicate portable thresholds from different measurement devices.
The Python coordinator supports `--configurations`, records the selected set
in resume identity, and continues to require every circuit for acceptance.

All 12 circuits passed replay through production admission, selection and phase
two, without policy overrides. Both the target and its largest follower used
normal selection. Their fingerprints matched the fixed-policy measurements.

The paired timing comparison used the previous memory-policy port with an
explicit full-policy override (A) and the installed production preset (B), both
at 30 GiB. Each circuit ran in A–B–B–A order, with two warmups and five timed
proofs per fresh process: ten retained samples per arm. The lock was released
after each pair. All 48 workers exited cleanly on the same GPU. No circuit
crossed the predeclared 3% slowdown gate, so no extension runs were needed.
This checks preset replay against the previous port, not the entire memory-policy
port against unmodified upstream.

| Circuit | Previous port median ms | Production replay median ms | Change |
| --- | ---: | ---: | ---: |
| Bigint | 163.276 | 163.277 | +0.00% |
| Blake2 compression | 221.476 | 221.441 | -0.02% |
| Blake2 G | 101.379 | 101.454 | +0.07% |
| Keccak | 220.996 | 221.028 | +0.01% |
| I&T | 104.932 | 104.890 | -0.04% |
| Load/store subword | 155.011 | 154.926 | -0.06% |
| Load/store word | 146.861 | 146.824 | -0.03% |
| Add/sub/LUI/AUIPC/MOP | 162.832 | 162.825 | -0.00% |
| Jump/branch/SLT | 165.769 | 165.727 | -0.03% |
| Mul/div unsigned | 95.140 | 95.004 | -0.14% |
| Shift/binary | 177.260 | 177.292 | +0.02% |
| Unified | 164.234 | 164.262 | +0.02% |

- 19 execution-prover CPU tests and 36 Python coordinator tests passed.
- `cargo check` passed with and without `memory_sweep`.
- The normal release `prover::tests::test_execution_prover_commit_then_prove`
  test passed with default configuration and without the sweep feature.
- Regenerating the table from accepted CSV produced identical formatted Rust.

Frozen baseline SHA256: `cc7444fb04d69212b2a028af51e2546c5ecea0682713ae0de121314098b30a22`.

Frozen replay SHA256: `5a8bae350ab012d8dd4edb497ebce0a1eaf74e63637ed57df95b06a6d46f132b`.

## Reproduction

See [the sweep and replay commands](memory_policies.md). The exact-budget
CSV, device snapshots, logs and frozen binaries are under the ignored local
`target/memory-policy/preset30-20260911/` directory. `measurements/accepted.csv`
feeds the generator; `validation-plan.json` records the paired timing protocol.

The older [checkpoint](memory_policy_checkpoint.md) and
[all-policy inventory](memory_requirements_pr434.md) retain historical status.
