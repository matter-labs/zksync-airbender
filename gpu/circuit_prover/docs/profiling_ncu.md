# `circuit_prover` Profiling with `ncu`

Start from [`profiling.md`](./profiling.md) for the shared profiling test details and the `TEST_BINARY` setup.

## Quick Kernel Mode

Use the default/basic set for fast turnaround and filter to the kernel of interest:

```bash
.agents/bin/with_gpu_lock.sh ncu \
  --nvtx \
  --nvtx-include 'test.gpu.prove.profiled_call@circuit_prover.tests' \
  --set basic \
  --kernel-name-base demangled \
  --kernel-name 'regex:<kernel_regex>' \
  --launch-skip <matching_launches_to_skip> \
  --launch-count <matching_launches_to_collect> \
  -o "target/profiling/ncu/$(date +%Y%m%d_%H%M%S)_gpu_prover_kernel" \
  "$TEST_BINARY" \
  --exact prover::tests::smoke::run_basic_unrolled_proof_job_profile_test \
  --ignored \
  --nocapture
```

## Full Picture And Source Correlation

When you need the broader picture, rebuild with line info enabled:

```bash
GPU_PROVER_ENABLE_LINEINFO=1 cargo test -p circuit_prover run_basic_unrolled_proof_job_profile_test --release --no-run --message-format=json \
  | python3 .agents/bin/cargo_test_executables.py
```

Then profile with source import enabled and the explicit full-section list:

```bash
.agents/bin/with_gpu_lock.sh ncu \
  --nvtx \
  --nvtx-include 'test.gpu.prove.profiled_call@circuit_prover.tests' \
  --import-source yes \
  --source-folders gpu/circuit_prover/native \
  --section ComputeWorkloadAnalysis \
  --section InstructionStats \
  --section LaunchStats \
  --section MemoryWorkloadAnalysis \
  --section MemoryWorkloadAnalysis_Chart \
  --section MemoryWorkloadAnalysis_Tables \
  --section Occupancy \
  --section SchedulerStats \
  --section SourceCounters \
  --section SpeedOfLight \
  --section SpeedOfLight_HierarchicalDoubleRooflineChart \
  --section SpeedOfLight_HierarchicalHalfRooflineChart \
  --section SpeedOfLight_HierarchicalSingleRooflineChart \
  --section SpeedOfLight_HierarchicalTensorRooflineChart \
  --section SpeedOfLight_RooflineChart \
  --section WarpStateStats \
  --section WorkloadDistribution \
  -o "target/profiling/ncu/$(date +%Y%m%d_%H%M%S)_gpu_prover_full" \
  "$TEST_BINARY" \
  --exact prover::tests::smoke::run_basic_unrolled_proof_job_profile_test \
  --ignored \
  --nocapture
```

## Dependency-Sensitive Sessions

If the existing ranges are too coarse and cache or inter-kernel dependencies matter, add a temporary raw registered NVTX range near the host-side launch site of the dependent kernel group you want to study. Reuse the `circuit_prover.tests` domain and give the message a session-specific name.

Use the same raw range helper as the profiling test in [`src/prover/tests/smoke.rs`](../src/prover/tests/smoke.rs):

```rust
let ncu_capture_domain = std::ffi::CStr::from_bytes_with_nul(b"circuit_prover.tests\0").unwrap();
let ncu_capture_message =
    std::ffi::CStr::from_bytes_with_nul(b"profile.tmp.<kernel_group>\0").unwrap();
let _range = start_registered_range(ncu_capture_domain, ncu_capture_message);

// enqueue the dependent kernel group here
```

For this mode, use the same lineinfo-enabled rebuild as the full-picture flow so the range report also includes correlated CUDA source:

```bash
GPU_PROVER_ENABLE_LINEINFO=1 cargo test -p circuit_prover run_basic_unrolled_proof_job_profile_test --release --no-run --message-format=json \
  | python3 .agents/bin/cargo_test_executables.py
```

Then profile that temporary range with range replay, cache flushing disabled, source import enabled, and the explicit full-section list:

```bash
.agents/bin/with_gpu_lock.sh ncu \
  --nvtx \
  --nvtx-include 'profile.tmp.<kernel_group>@circuit_prover.tests' \
  --replay-mode range \
  --cache-control none \
  --import-source yes \
  --source-folders gpu/circuit_prover/native \
  --section ComputeWorkloadAnalysis \
  --section InstructionStats \
  --section LaunchStats \
  --section MemoryWorkloadAnalysis \
  --section MemoryWorkloadAnalysis_Chart \
  --section MemoryWorkloadAnalysis_Tables \
  --section Occupancy \
  --section SchedulerStats \
  --section SourceCounters \
  --section SpeedOfLight \
  --section SpeedOfLight_HierarchicalDoubleRooflineChart \
  --section SpeedOfLight_HierarchicalHalfRooflineChart \
  --section SpeedOfLight_HierarchicalSingleRooflineChart \
  --section SpeedOfLight_HierarchicalTensorRooflineChart \
  --section SpeedOfLight_RooflineChart \
  --section WarpStateStats \
  --section WorkloadDistribution \
  -o "target/profiling/ncu/$(date +%Y%m%d_%H%M%S)_gpu_prover_range" \
  "$TEST_BINARY" \
  --exact prover::tests::smoke::run_basic_unrolled_proof_job_profile_test \
  --ignored \
  --nocapture
```

Remove the temporary raw NVTX instrumentation once the profiling session is complete.
