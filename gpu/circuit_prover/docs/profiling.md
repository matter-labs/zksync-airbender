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
| `$TEST_BINARY` | the `run_add_sub_profile_test` binary (built below) |
| `$NVTX_RANGE` | `test.gpu.prove.profiled_call@gpu_circuit_prover.tests` |
| `$SOURCE_FOLDERS` | `gpu/trace/native gpu/gkr/native gpu/whir/native` (the apex has no native tree of its own) |
| lineinfo env | `GPU_TRACE_ENABLE_LINEINFO` / `GPU_GKR_ENABLE_LINEINFO` / `GPU_WHIR_ENABLE_LINEINFO` |
| build-diag env | `GPU_TRACE_ENABLE_BUILD_DIAG` / `GPU_GKR_ENABLE_BUILD_DIAG` / `GPU_WHIR_ENABLE_BUILD_DIAG` |
| test-selection args | `--exact tests::proof_matrix::run_add_sub_profile_test --nocapture` |

## Profiling Test

- Exact libtest name: `tests::proof_matrix::run_add_sub_profile_test`
- The profile tests (e.g. `run_add_sub_profile_test`) are `#[ignore]`d; you MUST pass `--ignored` to run them. (The binary self-serializes via the pre-main `gpu_core::force_serial_libtest!()` guard — no `#[serial]` annotations exist anymore — and profiling runs a single test via `--exact` anyway.)
- When using `--exact`, do not pass a suffix such as `run_add_sub_profile_test` or `tests::run_add_sub_profile_test`. Use the full libtest name above.
- The current registered NVTX capture range in [`../src/tests/proof_matrix.rs`](../src/tests/proof_matrix.rs) (`run_profile`) uses:
  - domain `gpu_circuit_prover.tests`
  - message `test.gpu.prove.profiled_call`
- That range is intended to capture only the profiled `prove()` call after warmup.
- `prove()` is enqueue-only, so a CPU NVTX range measures enqueue time — use
  `nsys stats --report nvtx_gpu_proj_sum` for GPU-projected phase cost (see the
  generic `nsys` guide).

## Build The Test Binary

Build unlocked and capture the test binary path for profiler wrappers:

```bash
TEST_BINARY="$(
  cargo test -p gpu_circuit_prover run_add_sub_profile_test --release --no-run --message-format=json \
    | python3 .agents/bin/cargo_test_executables.py
)"
```

If you want the helper to validate the full test name and print the locked direct-run command, use:

```bash
cargo test -p gpu_circuit_prover run_add_sub_profile_test --release --no-run --message-format=json \
  | python3 .agents/bin/cargo_test_executables.py \
      --print-run-command \
      --test-name tests::proof_matrix::run_add_sub_profile_test
```

## MAIN R0 endpoint recomputation

Default builds reconstruct MAIN R0 endpoint contributions from the input
expressions. They do not read the transition's materialized roots for R0.
Forward publication and allocation lifetimes are unchanged by this path.

The runtime selects one of four kernels from each layer's compiled program.
It uses the original program's BF/E4 record counts for the launch bound:
more than four BF records per E4 record selects b4; otherwise b3. Among b4
programs, shape eligibility selects the unit-factor kernel first, then the
grouped linear-tail kernel when its lowering contains linear tails, and the
packed general kernel otherwise. Shape-subset and descriptor-capacity checks
run before binding. These empirical weights are independent of circuit names.

Programs carry an 8192-word descriptor and a scalar seed in the coefficient
bank. A whole-atom permutation places shared source references near E4
section boundaries while preserving group membership and member order. The
selected lowering, coefficient plans, scalar seed and kernel stay together.

Use the default profile tests above to capture `ab_gkr_r0_recomputed_*`
launches. Report proof CUDA-event intervals or GPU-projected timeline ranges;
CPU range duration is enqueue time. The retired materialized MAIN R0
`r0_diagnostics` feature and its `AB_R0_*` test overrides are no longer
available.

## Optional MAIN Continuation Diagnostics

Production uses a fused b2 continuation kernel when row tiles cover two resident
waves: `2 * SM_count * b2_blocks_per_SM`, using the generated b2 residency target
of two blocks per SM. Large programs (at least 5500 words) reading canonical
folded storage instead require one row-tile block per SM; first continuations
retain the two-wave minimum. The split publication/evaluation pair handles
smaller grids. On the measured 188-SM GPU these cutoffs are 752 and 188 tiles.
Both margins are empirical and have not been validated on other GPU models. The non-default
`continuation_diagnostics` feature adds unpacked fused b1/b2/b3 and split reference kernels and
validation/timing hooks. Production fused and split evaluators read adjacent corners
in 256-bit pairs with `.ca`; fold inputs use `.cs` and folded stores use `.wb`.
Fused folding uses bounded u96 accumulators to defer reductions. Standalone
publication keeps its original narrow arithmetic and four-lane pair geometry.
Static-X0 fused and split evaluators share the Boolean X0=0/1 body with a runtime address
selection and retain a separate infinity body. The existing static-X0 selection
rule is unchanged; dynamic-X0 retains its gated 16-record pacing.

To validate that compact evaluator against the original split tensor oracle,
set `AB_CONT_FUSION_VALIDATE=1 AB_CONT_COMPACT_X0=1`. To compare complete
proofs against the retained fully specialized static evaluator, set
`AB_CONT_FUSION_POLICY=large AB_CONT_EVALUATOR_POLICY=compact` with the
`AB_CONT_POLICY_PAIRS`, `AB_CONT_POLICY_SESSION`, and `AB_CONT_POLICY_OUTPUT`
variables shown below. Both arms retain current wide folding, dynamic kernels,
and original standalone publication. Add `AB_CONT_POLICY_IDENTICAL=1` for
identical-arm noise controls. The compact mode records each actual kernel arm
and checks that the existing SM-scaled and static-X0 dispatch rules are followed.

For the split static-X0 evaluator, use
`AB_CONT_FUSION_VALIDATE=1 AB_CONT_SPLIT_COMPACT_X0=1`. This validates both
publication folds (0 and 3); optional resident timing encloses the complete
publication/evaluation pair. Use
`AB_CONT_FUSION_POLICY=large AB_CONT_EVALUATOR_POLICY=split_compact` for a
whole-proof comparison against the retained fully specialized split evaluator.
Both arms keep the current fused evaluators, original publisher, and dispatch
rules. This mode supports the same pairing and identical-arm controls above.

Fused evaluators and static-X0 split evaluators also share the Boolean X1=0/1
body; X1 infinity remains specialized. Dynamic-X0 split evaluation is unchanged.
Use `AB_CONT_FUSION_VALIDATE=1 AB_CONT_COMPACT_X1=1` for the full arena/tensor
oracle at folds 0/3, or
`AB_CONT_FUSION_POLICY=large AB_CONT_EVALUATOR_POLICY=x1` for whole-proof
comparison against the retained X0-only evaluators. The `compact` and
`split_compact` comparison modes above retain their X0-only reference bodies.

```bash
cargo nextest run -p gpu_circuit_prover --release --features continuation_diagnostics --no-run
mkdir -p target/profiling/continuations
```

To compare the complete published arena and all tensor limbs against the original split
path for every add/sub continuation, including poison and injected-mismatch
checks:

```bash
AB_CONT_FUSION_VALIDATE=1 .agents/bin/with_gpu_lock.sh cargo nextest run \
  -p gpu_circuit_prover --release --features continuation_diagnostics \
  -E 'test(=tests::proof_matrix::run_add_sub_profile_test)' \
  --run-ignored only --no-capture
```

Validation checks unpacked b1/b2/b3, the packed unpaced and gated narrow-fold
references, and production packed b2 with wide folding. The production fused
arm feeds subsequent windows and the proof.
The resulting proof must match the warmup proof. This mode adds copies and
comparison kernels, so its whole-proof time is not performance evidence.
Add `AB_CONT_SPLIT_PACKED=1` to validate the production split evaluator instead.
This also compares both evaluators on depth-zero projections of the input
columns, then restores the actual depth-three output before the proof proceeds.

For paired whole-proof CUDA-event timing of the fused/split grid policy with pacing disabled against
the split path, unset `AB_CONT_FUSION_VALIDATE` and run:

```bash
AB_CONT_FUSION_POLICY=large AB_CONT_POLICY_PAIRS=10 AB_CONT_POLICY_SESSION=0 \
AB_CONT_POLICY_OUTPUT="$PWD/target/profiling/continuations/add-sub.csv" \
  .agents/bin/with_gpu_lock.sh cargo nextest run -p gpu_circuit_prover \
    --release --features continuation_diagnostics \
    -E 'test(=tests::proof_matrix::run_add_sub_profile_test)' \
    --run-ignored only --no-capture
```

The harness uses a reference proof, two warmup pairs, then balanced AB/BA order.
It checks proof equality, allocation balance, and selected fused/packed-launch counts.
The baseline uses the original 128-bit split evaluator at every window;
the candidate uses the retained narrow-fold, unpaced fused policy, including
packed split reads. These older flags preserve their historical comparison arms.
`AB_CONT_POLICY_IDENTICAL=1` runs the original split path in both arms as a timing control.
To isolate the packed-read increment, add `AB_CONT_PACKED_POLICY=1`: both arms
use the same fusion cutoff, with unpacked b2 as baseline and packed b2 as
candidate; both use packed split reads below the cutoff. With both this flag and
`AB_CONT_POLICY_IDENTICAL=1`, both arms use
unpacked b2 above the cutoff. Unset `AB_CONT_PACKED_POLICY` when comparing the
retained narrow-fold policy against the split path.
To isolate the split-read increment, use `AB_CONT_SPLIT_PACKED=1` instead:
both arms use production packed fused kernels above the cutoff; below it the
baseline uses 128-bit split reads and the candidate uses packed split reads.
With `AB_CONT_POLICY_IDENTICAL=1`, both use the baseline policy. The two
packed-comparison flags are mutually exclusive.
Retain fresh-process sessions, device/artifact identity, coverage, and raw CSVs
for comparative claims. These hooks are excluded from default builds.

Production dynamic-X0 fused kernels pace selector warps every 16 program records
when `program_words >= 1024`. Static-X0 and split kernels remain unpaced. This
empirical program-length cutoff is separate from the SM-scaled fusion threshold;
it adds no production kernel variants.

Use `AB_CONT_PACING_GATED=1` with `AB_CONT_FUSION_VALIDATE=1` to check the
production gated evaluator against the split reference across the full arena and
tensor. Use it with `AB_CONT_FUSION_POLICY=large` to compare whole-proof CUDA-event
time against the retained packed unpaced reference. Both proof arms use the same
fused/split and X0 policies; short dynamic programs execute the real runtime gate.
The CSV reports `gated_launches` (the selected kernel) and `paced_launches` (its
program meets the cutoff). `AB_CONT_POLICY_IDENTICAL=1` selects the unpaced
reference for both arms as a noise control. These modes require
`continuation_diagnostics`; raw timing and profiler evidence belong under `target/`.

Use `AB_CONT_CROSSOVER=1` with `AB_CONT_FUSION_VALIDATE=1` and the existing
`AB_CONT_FUSION_TIMING=layer:round,...` coordinates to compare the current packed
publication-plus-split arm (`packed_split`) against the current fused kernel
(`packed_gated`). Each interval includes all continuation work for that arm.
Both arms undergo full arena/tensor validation; the fused result feeds the
remaining proof. This resident diagnostic forces both paths regardless of the
production SM cutoff and is mutually exclusive with the other validation modes.
It does not provide a whole-proof policy override or a whole-proof timing claim.

`AB_CONT_CANONICAL_FUSION=1` with `AB_CONT_FUSION_POLICY=large` compares the
current packed/gated policy against a diagnostic cutoff of one tile block per SM
for later continuations that read a canonical E4 arena. First continuations keep
the current two-resident-wave cutoff. Both arms retain the same kernels, X0
selection and pacing rule. The coverage ledger records `canonical_input` and the
actual cutoff; `AB_CONT_POLICY_IDENTICAL=1` selects the current policy in both
arms. This flag is mutually exclusive with other whole-proof comparison flags.

To compare production wide fused folding against the preceding narrow-fold
implementation, set `AB_CONT_FOLD_WIDE_POLICY=fused_original` alongside
`AB_CONT_FUSION_POLICY=large`. Both arms use the original standalone publisher,
packed evaluators, the same fusion cutoff, and the same pacing and X0 selection.
The candidate changes fused fold arithmetic only, with the full production
wrapper checks. Per-pass coverage includes the actual `fold_arm`. Use
`AB_CONT_POLICY_IDENTICAL=1` for the corresponding narrow-fold control.

The retained `AB_CONT_FOLD_LANE8` and `AB_CONT_FOLD_WIDE` validation modes are
memory/arithmetic experiments; their standalone publication geometry is not the
production path. Likewise `AB_CONT_FOLD_LANE8_POLICY=1` and wide-policy modes
`fused`, `split`, and `both` retain those diagnostic comparisons. Do not interpret
them as the current-production comparison. Their frozen protocols and outcomes
are under `target/profiling/main-cont-fusion/fold-*` in the originating worktree.

`AB_CONT_CURRENT_SELECTOR=1` with `AB_CONT_FUSION_VALIDATE=1` forces both current
production X0 selector modes at the current production-selected geometry.
`AB_CONT_CURRENT_FUSION=1` instead compares current publication+split against
current fused execution, using the split selector predicate for both arms. These
resident timing modes reuse production symbols (arms19/20: fused dynamic/static;
21/22: publication+split dynamic/static). Split intervals include publication.
Both validation modes check all four arms at fold depth3 and both split arms at
depth0 against the full publication/tensor oracle. They are mutually exclusive
with other resident modes; neither changes the production dispatch policy.

For whole-proof cutoff diagnostics, `AB_CONT_EVALUATOR_POLICY=current` with
`AB_CONT_FUSION_POLICY=large` uses current production bodies in both arms.
`AB_CONT_CURRENT_WORDS` and `AB_CONT_CURRENT_WAVES` override only the candidate's
word cutoff and resident-wave count (one to three, scaled by b2 and SM count).
Omitted values retain production choices. Change one policy dimension at a time.
The ledger records forced arms19–22 and actual selector/geometry/pacing choices;
`AB_CONT_POLICY_IDENTICAL=1` runs the production policy in both arms.

`AB_CONT_CURRENT_FUSED_UPPER` restricts the current-policy candidate's static-X0
fused evaluators to programs below that exclusive word bound. Split selection
keeps the lower word cutoff. This changes selector dispatch only, using the same
production symbols; the independent ledger checks the fused/split distinction.

Current production selector policy uses static X0 at 1,024 or more words for
split evaluators, and from 1,024 through 5,499 words for fused evaluators. The
fixed-selector fusion diagnostic uses the split predicate for both forced arms;
it does not apply the fused upper bound to just one side of that comparison.

`AB_CONT_CURRENT_ARMS=a,b` overrides the two timed arms in current-selector or
current-fusion validation modes. Use two distinct arm numbers19–22; full
publication/tensor validation still checks all four current bodies. This allows
bounded pairwise comparisons of three existing implementations without new
kernels or production dispatch changes.

`AB_CONT_LARGE_CANONICAL_FUSION=1` with the current whole-proof policy mode
lowers the candidate fusion minimum to one row-tile block per SM for programs
at or above the fused selector upper bound that read canonical folded storage.
Other passes keep the two-wave threshold; selector choices are unchanged.
This explicit diagnostic comparison retains the previous two-wave baseline;
the candidate flag reproduces the production large-canonical admission rule.
