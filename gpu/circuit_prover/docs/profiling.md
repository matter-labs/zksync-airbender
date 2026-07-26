# `circuit_prover` Profiling

The generic kernel-profiling methodology lives at the cluster level:

- [`../../docs/profiling.md`](../../docs/profiling.md) — overview + parameters
- [`../../docs/profiling_ncu.md`](../../docs/profiling_ncu.md) — `ncu` per-kernel profiling
- [`../../docs/profiling_nsys.md`](../../docs/profiling_nsys.md) — `nsys` timeline / NVTX capture

This doc supplies the prover-specific values to plug into those guides. Apply the
generic GPU workflow from [`../../../.agents/gpu_work.md`](../../../.agents/gpu_work.md) first.

## Parameters for the generic guides

| Parameter | Prover value |
|---|---|
| `$TEST_BINARY` | the `run_basic_unrolled_proof_job_profile_test` binary (built below) |
| `$NVTX_RANGE` | `gpu_circuit_prover.tests@test.gpu.prove.profiled_call` |
| `$SOURCE_FOLDERS` | `gpu/circuit_prover/native` |
| lineinfo env | `GPU_PROVER_ENABLE_LINEINFO` |
| test-selection args | `--exact prover::tests::smoke::run_basic_unrolled_proof_job_profile_test --nocapture` |

## Profiling Test

- Exact libtest name: `prover::tests::smoke::run_basic_unrolled_proof_job_profile_test`
- The test runs by default (`#[test]` + `#[serial]`, not `#[ignore]`); do not pass `--ignored` — it matches zero tests.
- When using `--exact`, do not pass a suffix such as `run_basic_unrolled_proof_job_profile_test` or `tests::run_basic_unrolled_proof_job_profile_test`. Use the full libtest name above.
- The current top-level registered NVTX capture range in [`../src/prover/tests/proof_matrix.rs`](../src/prover/tests/proof_matrix.rs) uses:
  - domain `gpu_circuit_prover.tests`
  - message `test.gpu.prove.profiled_call`
  - so the `--nvtx-include` expression is `gpu_circuit_prover.tests@test.gpu.prove.profiled_call` (domain first)
- That range is intended to capture only the profiled `prove()` call after warmup.
- `prove()` is enqueue-only, so a CPU NVTX range measures enqueue time — use
  `nsys stats --report nvtx_gpu_proj_sum` for GPU-projected phase cost (see the
  generic `nsys` guide).

## Build The Test Binary

Build unlocked and capture the test binary path for profiler wrappers:

```bash
TEST_BINARY="$(
  cargo test -p gpu_circuit_prover run_basic_unrolled_proof_job_profile_test --release --no-run --message-format=json \
    | python3 .agents/bin/cargo_test_executables.py
)"
```

If you want the helper to validate the full test name and print the locked direct-run command, use:

```bash
cargo test -p gpu_circuit_prover run_basic_unrolled_proof_job_profile_test --release --no-run --message-format=json \
  | python3 .agents/bin/cargo_test_executables.py \
      --print-run-command \
      --test-name prover::tests::smoke::run_basic_unrolled_proof_job_profile_test
```

## Backward Coefficient-ISA Executors

The backward coefficient-term executors
(`ab_gkr_bwd_coeff_{r0,ext_d0,ext_d1,ext_d2,ext_d3}_{const,ptr}_kernel`) have
their own profiling setup, because a whole-proof range cannot isolate one
sumcheck round's evaluator.

| Parameter | Backward coefficient value |
|---|---|
| `$TEST_BINARY` | the `bwd_coeff_add_sub_profile` binary (built below) |
| `$NVTX_RANGE` | `circuit_prover.tests@test.gpu.bwd_coeff.add_sub_l0_r0` |
| `$SOURCE_FOLDERS` | `gpu/circuit_prover/native` |
| lineinfo env | `GPU_PROVER_ENABLE_LINEINFO` |
| test-selection args | `--exact prover::gkr::backward::vm::gpu_tests::bwd_coeff_add_sub_l0_r0_profile --ignored --nocapture` |
| kernel filter | `--kernel-name-base demangled --kernel-name 'regex:ab_gkr_bwd_coeff_.*r0.*'` |

Two things about that string are easy to get wrong, and both silently produce
`==WARNING== No kernels were profiled.` rather than an error:

- **`--nvtx-include` takes `Domain@Range`, not `Range@Domain`.** The range
  message goes AFTER the `@`. Verified empirically against this kernel:
  `circuit_prover.tests@test.gpu.bwd_coeff.add_sub_l0_r0` matches;
  `test.gpu.bwd_coeff.add_sub_l0_r0@circuit_prover.tests` matches nothing.
- The domain here is `circuit_prover.tests`, which is NOT the
  `gpu_circuit_prover.tests` domain the whole-proof range in
  [`../src/prover/tests/proof_matrix.rs`](../src/prover/tests/proof_matrix.rs)
  uses. Both are live; use the one from the table for this kernel group.

`ncu` reports which ranges it saw under "NVTX Start/End Ranges" in
`--page details`, so a run that matched nothing can be diagnosed by dropping
`--nvtx-include` and reading that list.

### Tests

All three are `#[ignore]`d GPU-timing tests: build unlocked, run the executable
under `.agents/bin/with_gpu_lock.sh`, and pass `--ignored`.

- `prover::gkr::backward::vm::gpu_tests::bwd_coeff_add_sub_l0_r0_profile` — the
  profiler selector. After warmup it runs ONE incumbent launch sequence and ONE
  new launch sequence, and only the new one sits inside the registered NVTX
  range.
- `prover::gkr::backward::vm::gpu_tests::bwd_coeff_add_sub_l0_r0_head_to_head` —
  the same comparison without a profiler, at `c2`, the selected budget and the
  `c16` diagnostic.
- `prover::gkr::backward::vm::gpu_tests::bwd_coeff_focused_layer0_budget_sweep`
  and `..::bwd_coeff_corpus_budget_sweep` — the `c2`–`c16` budget sweeps. They
  write CSVs plus the selection metadata under `target/gkr/` and index
  themselves in `target/gkr/bwd_coeff_profile_summary.md`.

The **persisted selection is the authority** for which budget is profiled:
`target/gkr/bwd_coeff_selected_budgets.json`, written by the corpus sweep, holds
the production choice per `(circuit, layer, round class)`.
`report.rs`'s `PROFILE_DEFAULT_CELLS` is only a compiled mirror of that file's
`add_sub` layer-0 R0 entry, and both profiling tests assert the two agree
whenever the sidecar exists — so a stale pin fails the test instead of quietly
profiling a different budget than the one production would select. Re-run the
corpus sweep, read the entry, re-pin. `BWD_COEFF_PROFILE_CELLS=c<n>` overrides
both for an ad-hoc session.

### Build and profile

```bash
TEST_BINARY="$(
  GPU_PROVER_ENABLE_LINEINFO=1 \
  cargo +nightly-2026-02-10 test -p gpu_circuit_prover bwd_coeff_add_sub_profile --features bench --release --no-run --message-format=json \
    | python3 .agents/bin/cargo_test_executables.py
)"

.agents/bin/with_gpu_lock.sh /usr/local/cuda/bin/ncu \
  --nvtx \
  --nvtx-include 'circuit_prover.tests@test.gpu.bwd_coeff.add_sub_l0_r0' \
  --import-source yes \
  --source-folders gpu/circuit_prover/native \
  --section ComputeWorkloadAnalysis \
  --section InstructionStats \
  --section LaunchStats \
  --section MemoryWorkloadAnalysis \
  --section Occupancy \
  --section SchedulerStats \
  --section SourceCounters \
  --section WarpStateStats \
  --kernel-name-base demangled \
  --kernel-name 'regex:ab_gkr_bwd_coeff_.*r0.*' \
  --launch-count 1 \
  -o target/profiling/ncu/bwd_coeff_add_sub_l0_r0 \
  "$TEST_BINARY" \
  --exact prover::gkr::backward::vm::gpu_tests::bwd_coeff_add_sub_l0_r0_profile \
  --ignored \
  --nocapture
```

The `--features bench` flag is required: the whole coefficient-ISA GPU test
module is `#[cfg(all(test, feature = "bench"))]`. `--ignored` is required too —
the test is `#[ignore]`d, and libtest exits 0 when a filter matches nothing, so
omitting it profiles an empty run that looks successful.

To profile the INCUMBENT side of the comparison, drop `--nvtx*` (its launch is
deliberately outside the range) and filter on its own symbol, skipping the
correctness launch and the three warmups:

```bash
  --kernel-name 'regex:ab_gkr_main_round0_flat_constant_compact_e4_kernel' \
  --launch-skip 4 --launch-count 1
```

The skip is `INCUMBENT_PROFILE_LAUNCH_SKIP` = one untimed correctness launch plus
`WARMUP_ITERS`, and the head-to-head test counts its own incumbent launches and
asserts that relationship — so changing the warmup count fails the test rather
than silently profiling a cold warmup launch. The generated
`target/gkr/bwd_coeff_profile_summary.md` section prints the current value.
