# Profiling GPU kernels with `ncu`

Generic Nsight Compute methodology for any `gpu/` crate. Start from
[`profiling.md`](./profiling.md) for the parameter conventions; supply
`$TEST_BINARY`, `$NVTX_RANGE`, and `$SOURCE_FOLDERS` (plus the crate's
`GPU_<X>_ENABLE_LINEINFO` for source correlation) from your crate's profiling
doc. Invoke `$TEST_BINARY` with whatever libtest args select + run the
kernel-exercising test (e.g. `--exact <test> --nocapture`, adding `--ignored`
only if that test is marked `#[ignore]`).

> Concrete example (the prover): see
> [`../circuit_prover/docs/profiling.md`](../circuit_prover/docs/profiling.md) —
> `$NVTX_RANGE = test.gpu.prove.profiled_call@circuit_prover.tests`,
> `$SOURCE_FOLDERS = gpu/circuit_prover/native`, lineinfo env
> `GPU_PROVER_ENABLE_LINEINFO`.

## Quick Kernel Mode

Use the default/basic set for fast turnaround and filter to the kernel of interest:

```bash
.agents/bin/with_gpu_lock.sh ncu \
  --nvtx \
  --nvtx-include "$NVTX_RANGE" \
  --set basic \
  --kernel-name-base demangled \
  --kernel-name 'regex:<kernel_regex>' \
  --launch-skip <matching_launches_to_skip> \
  --launch-count <matching_launches_to_collect> \
  -o "target/profiling/ncu/$(date +%Y%m%d_%H%M%S)_kernel" \
  "$TEST_BINARY" --exact <test> --nocapture
```

## Full Picture And Source Correlation

When you need the broader picture, rebuild with line info enabled (the crate's
`GPU_<X>_ENABLE_LINEINFO`), then re-capture `$TEST_BINARY`:

```bash
GPU_<X>_ENABLE_LINEINFO=1 cargo test -p <crate> <filter> --release --no-run --message-format=json \
  | python3 .agents/bin/cargo_test_executables.py
```

Then profile with source import enabled and the explicit full-section list:

```bash
.agents/bin/with_gpu_lock.sh ncu \
  --nvtx \
  --nvtx-include "$NVTX_RANGE" \
  --import-source yes \
  --source-folders "$SOURCE_FOLDERS" \
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
  -o "target/profiling/ncu/$(date +%Y%m%d_%H%M%S)_full" \
  "$TEST_BINARY" --exact <test> --nocapture
```

## Dependency-Sensitive Sessions

If the existing ranges are too coarse and cache or inter-kernel dependencies
matter, add a temporary raw registered NVTX range near the host-side launch site
of the dependent kernel group you want to study. Give the message a
session-specific name; `start_registered_range` is `gpu_core`'s
`primitives::nvtx` helper (re-exported in-crate where used):

```rust
let ncu_capture_domain = std::ffi::CStr::from_bytes_with_nul(b"<your.domain>\0").unwrap();
let ncu_capture_message =
    std::ffi::CStr::from_bytes_with_nul(b"profile.tmp.<kernel_group>\0").unwrap();
let _range = start_registered_range(ncu_capture_domain, ncu_capture_message);

// enqueue the dependent kernel group here
```

Rebuild with the same lineinfo env as the full-picture flow so the range report
also includes correlated CUDA source, then profile that temporary range with
range replay, cache flushing disabled, and the same full-section list:

```bash
.agents/bin/with_gpu_lock.sh ncu \
  --nvtx \
  --nvtx-include 'profile.tmp.<kernel_group>@<your.domain>' \
  --replay-mode range \
  --cache-control none \
  --import-source yes \
  --source-folders "$SOURCE_FOLDERS" \
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
  -o "target/profiling/ncu/$(date +%Y%m%d_%H%M%S)_range" \
  "$TEST_BINARY" --exact <test> --nocapture
```

Remove the temporary raw NVTX instrumentation once the profiling session is complete.
