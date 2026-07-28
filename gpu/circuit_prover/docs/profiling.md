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

## Backward Segmented Lean VM Executors

The segmented lean VM's executors
(`ab_gkr_bwd_seg_{r0,cont}_{const,ptr}_epi_{staged,plane,wide}_kernel`, plus the
`progptr` A/B twins) have their own profiling setup, because a whole-proof range
cannot isolate one sumcheck round's evaluator.

| Parameter | Segmented lean VM value |
|---|---|
| `$TEST_BINARY` | the `gpu_circuit_prover` unittest binary (built below) |
| `$NVTX_RANGE` | `gpu_circuit_prover.tests@test.gpu.bwd_seg.spike` |
| `$SOURCE_FOLDERS` | `gpu/circuit_prover/native` |
| lineinfo env | `GPU_PROVER_ENABLE_LINEINFO` |
| test-selection args | `--exact prover::gkr::backward::vm::seg_report::bwd_seg_add_sub_l0_r0_profile --ignored --nocapture` |
| kernel filter | `--kernel-name-base demangled --kernel-name 'regex:ab_gkr_bwd_seg_.*r0.*'` |

The incumbent side of the paired comparison registers its OWN range,
`gpu_circuit_prover.tests@test.gpu.bwd_seg.incumbent`, so the two evaluators are
selected by NVTX rather than by kernel name. The three constants are
`seg_report::{SEG_NVTX_DOMAIN, SEG_NVTX_MESSAGE, SEG_NVTX_INCUMBENT_MESSAGE}`.

Two things about the range string are easy to get wrong, and both silently produce
`==WARNING== No kernels were profiled.` rather than an error:

- **`--nvtx-include` takes `Domain@Range`, not `Range@Domain`.** The range
  message goes AFTER the `@`. (`nsys --nvtx-capture` takes the opposite order.)
- The domain here is `gpu_circuit_prover.tests`, the same one the whole-proof
  range in [`../src/prover/tests/proof_matrix.rs`](../src/prover/tests/proof_matrix.rs)
  uses, so a range message that does not match selects the whole proof instead of
  one evaluator.

`ncu` reports which ranges it saw under "NVTX Start/End Ranges" in
`--page details`, so a run that matched nothing can be diagnosed by dropping
`--nvtx-include` and reading that list.

### Tests

All of these are `#[ignore]`d GPU-timing tests: build unlocked, run the executable
under `.agents/bin/with_gpu_lock.sh`, and pass `--ignored`.

- `prover::gkr::backward::vm::seg_report::bwd_seg_add_sub_l0_r0_profile` — the
  profiler selector. After the matrix has warmed and measured, it runs ONE
  candidate launch and ONE incumbent launch, each inside its own NVTX range.
- `..::bwd_seg_add_sub_l0_r0_matrix` and `..::bwd_seg_add_sub_l0_cont_matrix` —
  the same paired comparison without a profiler, over the `(epilogue, K)` matrix.
- `..::bwd_seg_k_axis_census`, `..::bwd_seg_stage_b_acc_ladder`,
  `..::bwd_seg_keccak_l0_monster` — the `K` axis, the AccPlacement smem ladder and
  the monster-layer behaviour.
- `..::bwd_seg_corpus_sweep`, `..::bwd_seg_corpus_k_policy`,
  `..::bwd_seg_corpus_d2_policy` — the whole-corpus sweeps. **These are long
  runs**, not part of a per-task gate.

Every one of them writes its CSV and metadata under `seg_report::SEG_OUTPUT_DIR`
(`target/gkr/seg`). There is no compiled budget pin to keep in sync any more: the
segmented VM has no cell budget, and `K` is a launch parameter the caller
supplies, so the profiled shape comes from `profile_shape()` alone.

### Build and profile

```bash
TEST_BINARY="$(
  GPU_PROVER_ENABLE_LINEINFO=1 \
  cargo +nightly-2026-02-10 test -p gpu_circuit_prover --lib --features bench --release --no-run --message-format=json \
    | python3 .agents/bin/cargo_test_executables.py
)"

.agents/bin/with_gpu_lock.sh /usr/local/cuda/bin/ncu \
  --nvtx \
  --nvtx-include 'gpu_circuit_prover.tests@test.gpu.bwd_seg.spike' \
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
  --kernel-name 'regex:ab_gkr_bwd_seg_.*r0.*' \
  --launch-count 1 \
  -o target/profiling/ncu/bwd_seg_add_sub_l0_r0 \
  "$TEST_BINARY" \
  --exact prover::gkr::backward::vm::seg_report::bwd_seg_add_sub_l0_r0_profile \
  --ignored \
  --nocapture
```

The `--features bench` flag is required: the whole segmented-lean-VM GPU test
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
