# Iteration-time measurements

Measured on 2026-08-06 in the `red` worktree.

Environment:

- GPU: NVIDIA RTX PRO 6000 Blackwell Server Edition (97,887 MiB)
- Driver: 610.57.04
- CUDA compiler: 13.3
- Rust: 1.99.0-nightly (2026-07-16)
- CMake: 4.2.3

## Build loop

| Scenario | Wall time | Scope observed |
| --- | ---: | --- |
| Clean release build in a separate target directory | 10.48 s | Standalone crate and its default dependencies |
| No-change release build | 0.05 s | Nothing rebuilt |
| Touch `native/windowed_vm.cu`, then release build | 7.06 s | This crate's CUDA object, device link, archive, and Rust link |
| Touch CUDA, build, then launch a `log_trace=8` smoke run | 6.41 s | 6.12 s reported by Cargo; launch included in wall time |

Commands were scoped to `-p gpu_gkr_windowed_bench`. The default dependency
tree contains neither `gpu_gkr_compiler` nor `gkr_eval_ir`; those are only
enabled by `artifact-gen`.

## Kernel timing

CUDA-event timings include the VM kernel plus the final 27-cell reduction.
Allocations and initialization are outside the timed region.

| Variant | `log_trace` | Logical 8-row blocks | Resident allocation | Requested source-load floor | Minimum | Median |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Initial | 20 | 4,096 | 530,263,686 B | 4,458,545,152 B | 2.690080 ms | 2.694976 ms |
| Initial | 24 | 65,536 | 8,484,040,806 B | 71,336,722,432 B | 36.057503 ms | 36.138657 ms |
| Inline descriptor + packed resolver | 24 | 65,536 | 8,484,038,832 B | 71,336,722,432 B | 30.681440 ms | 31.302864 ms |
| Per-term resolved source views | 24 | 65,536 | 8,484,038,832 B | 71,336,722,432 B | 30.917536 ms | 31.579632 ms |
| Round-0 typed groups, run 1 | 24 | 65,536 | 8,484,038,832 B | 71,336,722,432 B | 31.400415 ms | 32.076111 ms |
| Round-0 typed groups, run 2 | 24 | 65,536 | 8,484,038,832 B | 71,336,722,432 B | 33.562241 ms | 33.577679 ms |
| Typed complete atoms, run 1 | 24 | 65,536 | 8,484,038,832 B | 71,336,722,432 B | 25.360767 ms | 25.541311 ms |
| Typed complete atoms, run 2 | 24 | 65,536 | 8,484,038,832 B | 71,336,722,432 B | 25.113472 ms | 25.174576 ms |

The source-load value counts the loads requested by all 9 independently
executing warps before cache effects; it is not a DRAM-byte measurement. At
`log_trace=24`, dividing that floor by the median gives about 1.97 TB/s of
requested source traffic.

An Nsight Compute `basic` capture at `log_trace=20` reported:

- VM: 2.45 ms under profiler replay, 72 registers/thread, 0 B static/dynamic
  shared memory, 37.62% SM throughput, 32.32% memory throughput, and 9.44%
  DRAM throughput.
- Finalizer: 10.02 us, 20 registers/thread, and 128 B static shared memory.

The profiler duration should not be compared directly with the normal CUDA
event samples because Nsight Compute replays kernels to collect metrics.

## First repair profile

The full log-24 capture after moving all control tables into the by-value
`__grid_constant__` descriptor and factoring the corner resolver profiles only
`ab_gkr_windowed_vm_kernel`:

- report: `target/profiling/ncu/windowed_gkr_add_sub_l0_log24_repaired_vm_full.ncu-rep`;
- CSV: `target/profiling/ncu/windowed_gkr_add_sub_l0_log24_repaired_vm_full.csv`;
- NCU duration: 30.42 ms, down from 35.16 ms in the initial full capture;
- SASS instruction bundles: 8,432, down from 14,624;
- static `BRA` instructions: 776, down from 1,770;
- registers/thread: unchanged at 72, with zero stack, local, or shared memory;
- issue slots busy: 52.83%, up from 39.52%; and
- achieved occupancy: 43.47%, up from 37.59%.

PC-sampling proportions changed from 29.09% to 24.89% for long scoreboard,
22.10% to 22.73% for wait, and 19.58% to 17.77% for no instruction. The
control arrays now appear as `LDC`/`LDCU` parameter-space loads in SASS;
remaining `LDG` instructions service the actual backing, equality, and output
data.

## Resolved source-view pass

Resolving each source record, address slot, and typed column pointer once per
term operand produced the intended SASS shape, but did not improve runtime:

- SASS instructions: 8,008, down from 8,432;
- metadata `LDC`/`LDCU` instructions: 111, down from 243;
- backing `LDG` instructions: unchanged at 209;
- static `BRA` instructions: 784, up from 776; and
- registers/thread: 76, up from 72, with zero stack, local, or shared memory.

The first log-24 run measured 30.918 ms minimum and 31.580 ms median. A repeat
measured 30.988 ms minimum and 31.639 ms median. Both runs became bimodal late
in their 100 samples, but neither showed a throughput improvement over the
31.303 ms prior median. Compute-sanitizer at log trace 8 reported zero errors,
and the pinned log-8/log-24 checksums remained unchanged.

## Round-0 typed-group pass

The round-0 artifact now distinguishes BF groups from fixed two-member E4
add/sub groups and emits mixed products in BF-first order. The CUDA interpreter
uses one term switch for standalone and grouped records, accumulates BF groups
in BF, and folds every completed group through its E4 batching coefficient.
The normalized old/new semantic schedules both contain 150 terms, 175 records,
25 groups, and 72 atoms; their 176-line dumps have an empty diff.

The resulting VM SASS shape is:

- 4,984 instruction bundles, down from 8,008;
- 437 static `BRA` instructions, down from 784;
- 64 `LDC`/`LDCU` instructions, down from 111;
- 106 static `LDG` instructions, down from 209; and
- 80 registers/thread, up from 76, with zero calls, stack, local, or shared
  memory.

An independent post-implementation SASS review also found exactly one
class-extraction shift (`word0 >> 13`) in the kernel, confirming that ptxas did
not duplicate the term decoder. At this 288-thread block size, both 76 and 80
registers are in the same two-block/18-warp occupancy band; the next meaningful
target is at most 72 registers, while increases through 113 do not cross another
occupancy boundary.

The full log-24 capture contains only `ab_gkr_windowed_vm_kernel`:

- report: `target/profiling/ncu/windowed_gkr_add_sub_l0_log24_round0_wire_full.ncu-rep`;
- CSV: `target/profiling/ncu/windowed_gkr_add_sub_l0_log24_round0_wire_full.csv`;
- NCU duration: 33.57 ms;
- issue slots busy: 46.03%;
- achieved occupancy: 32.51%; and
- PC-sampling proportions: 23.22% long scoreboard, 28.86% wait, and 14.80%
  no instruction.

The two ordinary timing runs landed in different stable performance states,
so their delta versus the 31.640 ms previous repeat cannot be attributed to
the wire change alone. The finalizer is tiny and unchanged. Log-8 and log-24
checksums remain `0xbb2eb9da3c8c062b` and `0x8820ab14cacc9ff7` respectively;
compute-sanitizer reports zero errors.

## Typed complete-atom pass

The program is now 175 `align(8)` instruction records with separate `u16`
class, factor, source-A, and source-B fields. The outer loop loads one record,
tests the class field bit, and enters a BF or E4 path that consumes the complete
singleton/group. BF accumulation is local to the BF path, with a
`#pragma unroll 1` tail; the E4 pair is manually unrolled. Both paths initialize
their local triplet from the first contribution and fold once through the atom's
E4 coefficient. The descriptor remains 1,952 bytes and the inline program
remains 1,400 bytes.

The normalized schedule remains exactly equal to the original: both dumps have
150 terms, 175 records, 25 groups, 72 atoms, and 176 lines, with an empty diff.
The resulting VM SASS shape is:

- 7,112 instruction bundles, up from 4,984 for the loop-carried implementation;
- 760 static `BRA` instructions, up from 437;
- 103 `LDC`/`LDCU` sites, including 20 `LDC.64` sites and 13 `LDC.U16` sites;
- 233 static `LDG` sites, up from 106;
- 65 registers/thread, down from 80 and below the 72-register occupancy cliff;
- one BF-tail backward branch plus the outer-loop backedge; and
- zero calls, stack, local, or shared memory.

The full log-24 VM-only capture reports:

- report: `target/profiling/ncu/windowed_gkr_add_sub_l0_log24_typed_atom_full.ncu-rep`;
- CSV: `target/profiling/ncu/windowed_gkr_add_sub_l0_log24_typed_atom_full.csv`;
- NCU duration: 26.01 ms;
- issue slots busy: 59.84%;
- achieved occupancy: 47.17%; and
- PC-sampling proportions: 18.98% long scoreboard, 22.88% wait, and 20.94%
  no instruction.

The larger code footprint raises the no-instruction share, but the register
reduction crosses the occupancy threshold and dominates overall: the two
ordinary medians are 25.541 ms and 25.175 ms. That is roughly 20% faster than
the 31.580/31.639 ms resolved-source baseline and 21-25% faster than the
32.076/33.578 ms loop-carried typed-group pass. Compute-sanitizer reports zero
errors and the pinned log-8/log-24 checksums remain unchanged.

## Optimization ledger

- Done: replace the duplicated grouped/standalone term executors with one
  execution state machine, without outlining device calls.
- Done: canonicalize mixed BF/E4 products in the artifact and remove the
  runtime source-class load, swap, and selects.
- Done: replace loop-carried BF/E4 group state with aligned records and
  complete typed atom paths.

## 2026-08-07 optimization baseline refresh

Before the cache/occupancy experiments, the unchanged typed-complete-atom
kernel was rebuilt and timed again on the RTX PRO 6000 Blackwell Server
Edition. The incremental release build took 7.19 s. Resource usage remains 65
registers/thread with zero stack, local, or shared memory; ptxas also reports
zero spill loads and stores.

Two log-24 runs with 10 warmups and 100 measured iterations produced:

| Run | Minimum | Median | Checksum |
|---|---:|---:|---:|
| Baseline refresh 1 | 25.321793 ms | 25.360399 ms | `0x8820ab14cacc9ff7` |
| Baseline refresh 2 | 25.231808 ms | 25.271313 ms | `0x8820ab14cacc9ff7` |

The raw logs are under `target/profiling/windowed_experiments/`.

## Cache-all input pass

The BF input, E4 input, and 512-byte `eq_low` loads were changed from streaming
`.cs` to cache-all `.ca`. SASS replaced 52 scalar and 53 vector `.EF` load
sites with `.STRONG.SM` loads while leaving the remaining load sites unchanged.
The kernel remains at 65 registers/thread with zero stack, local, or shared
memory. The incremental release build took 8.75 s.

Two ordinary log-24 runs produced:

| Run | Minimum | Median | Checksum |
|---|---:|---:|---:|
| Cache-all inputs 1 | 22.466305 ms | 22.478960 ms | `0x8820ab14cacc9ff7` |
| Cache-all inputs 2 | 22.456673 ms | 22.460896 ms | `0x8820ab14cacc9ff7` |

This is an approximately 11% improvement over the refreshed baseline, so the
change is retained. The full VM-only profile is
`target/profiling/ncu/windowed_gkr_add_sub_l0_log24_ca_full.ncu-rep`:

- NCU duration: 22.93 ms;
- issue slots busy: 67.87%;
- achieved occupancy: 53.95%;
- L1/TEX hit rate: 90.23%, up from 61.93%;
- L2 hit rate: 18.09%, reflecting that far fewer repeated requests reach L2;
- PC-sampling proportions: 9.80% long scoreboard, 22.62% wait, 24.21% no
  instruction, 14.56% not selected, and 5.30% branch resolving.

### Streaming partial-output stores

The lane-zero partial writes previously used plain assignments, which compiled
to ordinary `STG.E.128`. They are now explicit `.cs` stores and compile to the
three expected `STG.E.EF.128` sites. Resource usage is unchanged. Two medians
were 22.454704 ms and 22.438671 ms with the pinned checksum. The movement is
near measurement noise, but the hint is retained because these sparse partials
are written once, consumed by the finalizer, and should not displace reusable
input data from L1.

### Four-block launch-bounds probe

Adding only `__launch_bounds__(288, 4)` forced ptxas from 65 to 56 registers,
but introduced a 24-byte stack frame and 32 static `LDL`/`STL` sites. The probe
failed the compile gate and was rejected without GPU timing.

## Shared accumulator occupancy pass

The three long-lived E4 accumulators were moved to thread-private, cell-major
shared storage at `shared[cell * 288 + thread]`, and the kernel was annotated
with `__launch_bounds__(288, 4)`. The resulting SASS uses 56 registers/thread,
zero stack/local memory, 10 static `LDS.128` sites, and 11 static `STS.128`
sites. Static shared storage is 13,824 bytes/block; resource tools report
14,848 bytes including the driver's 1,024-byte block reserve. The log-8
compute-sanitizer run reports zero errors and checksum
`0xbb2eb9da3c8c062b`.

With the runtime's default carveout, CUDA selected the full 102.4 kB/SM shared
partition. Two ordinary medians were 22.356768 ms and 22.342049 ms, only a
small improvement. The full report
`target/profiling/ncu/windowed_gkr_add_sub_l0_log24_shared_accumulators_full.ncu-rep`
shows why:

- NCU duration: 22.91 ms;
- theoretical/achieved occupancy: 75% / 58.62%;
- L1/TEX hit rate: 54.69%;
- L2 hit rate: 82.20%;
- issue slots busy: 66.34%; and
- long-scoreboard PC samples: 17.51%.

Setting the kernel's preferred shared-memory carveout to 60% selects the 64
KiB hardware partition (reported as 65.54 kB), the smallest supported partition
that admits four blocks on the RTX PRO 6000 Blackwell Server Edition. This is a
device-tuned hint rather than a portable partition guarantee. A production
transplant must also consider interactions with kernels that could otherwise
co-schedule under a different shared/L1 configuration. Two ordinary runs
improved to:

| Run | Minimum | Median | Checksum |
|---|---:|---:|---:|
| Shared accumulators, 60% carveout 1 | 20.655487 ms | 20.662849 ms | `0x8820ab14cacc9ff7` |
| Shared accumulators, 60% carveout 2 | 20.558624 ms | 20.562704 ms | `0x8820ab14cacc9ff7` |

The retained full report is
`target/profiling/ncu/windowed_gkr_add_sub_l0_log24_shared_accumulators_carveout60_full.ncu-rep`:

- NCU duration: 21.05 ms;
- theoretical/achieved occupancy: 75% / 67.79%;
- L1/TEX hit rate: 80.82%;
- L2 hit rate: 58.12%;
- issue slots busy: 72.01%; and
- PC-sampling proportions: 9.19% long scoreboard, 19.41% wait, 24.77% no
  instruction, 18.41% not selected, and 4.57% branch resolving.

### Hoisted corner-offset probe

Eight selector-dependent corner offsets were computed once and carried as
named fields. Ptxas kept the kernel at 56 ordinary registers with zero
stack/local memory, emitted uniform-path operations, and reduced whole-binary
`SHF.L.U32` sites from 164 to 43. Static SASS instructions fell from 7,440 to
7,168. Despite that shape, the two medians regressed to 21.353504 ms and
21.390961 ms. The variant was rejected and the direct single-shift corner
calculation restored.

The pre-triplet retained-source verification produced 20.542080 ms and
20.660976 ms medians with the log-24 checksum `0x8820ab14cacc9ff7`.

## Triplet apply pass

`window_triplet<T>` now owns the unrolled three-cell `apply` loop. BF and E4
group sums remain triplets through initialization, tail accumulation, and the
coefficient fold, so immediate/sign selection is expressed once outside the
cell loop. Ptxas reduced the VM from 56 to 55 registers/thread, static SASS
instructions from 7,440 to 7,408, and static branches from 768 to 760, with
zero stack/local memory.

Two ordinary log-24 runs produced:

| Run | Minimum | Median | Checksum |
|---|---:|---:|---:|
| Triplet apply 1 | 19.787296 ms | 19.793617 ms | `0x8820ab14cacc9ff7` |
| Triplet apply 2 | 19.781696 ms | 19.786768 ms | `0x8820ab14cacc9ff7` |

The refactor is retained. The full VM-only report is
`target/profiling/ncu/windowed_gkr_add_sub_l0_log24_triplet_apply_full.ncu-rep`:

- NCU duration: 20.26 ms;
- theoretical/achieved occupancy: 75% / 68.58%;
- L1/TEX hit rate: 81.41%;
- L2 hit rate: 56.73%;
- issue slots busy: 73.26%; and
- PC-sampling proportions: 9.16% long scoreboard, 17.80% wait, 23.05% no
  instruction, 20.68% not selected, and 4.53% branch resolving.

The final non-lineinfo build took 6.07 s. Two fresh verification medians were
19.764687 ms and 19.869104 ms with the log-24 checksum
`0x8820ab14cacc9ff7`. Resource usage remains 55 registers/thread, zero
stack/local memory, and 13,824 bytes static shared memory per block. A fresh
log-8 compute-sanitizer run reports zero errors and checksum
`0xbb2eb9da3c8c062b`.

## Warp-vote selector uniformity pass

The `x0`/`x1` infinity predicates are now computed once with full-warp
`__all_sync` votes and carried in a small by-value selector record through the
force-inlined VM evaluator. The nine selector warps remain in one block, run
the same program, and retain their existing row mapping and shared L1 working
set. There is no program filtering, VM duplication, launch split, or dummy
endpoint computation in this pass.

Ptxas did not add uniform branch sites, but propagating the voted predicates
removed substantial repeated selector control flow. A fresh VM-only
`cuobjdump` comparison reports:

- instruction lines: 7,008 to 6,936;
- `BSSY.RECONVERGENT` sites: 130 to 107;
- `BSYNC.RECONVERGENT` sites: 130 to 107;
- registers/thread: 55 to 56; and
- zero stack and local memory in both builds.

The incremental probe build took 8.94 s. Two ordinary log-24 runs produced:

| Run | Minimum | Median | Checksum |
|---|---:|---:|---:|
| Selector vote 1 | 18.061249 ms | 18.067200 ms | `0x8820ab14cacc9ff7` |
| Selector vote 2 | 18.046753 ms | 18.051504 ms | `0x8820ab14cacc9ff7` |

This is approximately 8.7% faster than the retained triplet-apply result. All
37 unit tests pass, and the log-8 compute-sanitizer run reports zero errors
with checksum `0xbb2eb9da3c8c062b`.

The new representative full VM-only report is
`target/profiling/ncu/windowed_gkr_add_sub_l0_log24_selector_vote_full.ncu-rep`:

- NCU duration: 18.39 ms, down from 20.26 ms;
- dynamic instructions: 22.18 billion, down from 26.37 billion;
- dynamic branches: 2.14 billion, down from 2.87 billion;
- theoretical/achieved occupancy: 75% / 65.53%;
- L1/TEX and L2 hit rates: 81.54% / 56.94%;
- issue slots busy: 67.68%;
- physical FMA-heavy and ALU-heavy pipe utilization: 66.78% / 47.73%; and
- PC-sampling proportions: 14.02% long scoreboard, 18.66% wait, 23.49% no
  instruction, 15.39% not selected, 8.55% math-pipe throttle, and 1.93%
  branch resolving.

The dominant physical FMA-heavy pipe remains roughly two-thirds utilized, so
future dummy-compute experiments have some but not unlimited headroom. The
final non-lineinfo build took 5.45 s and retains 56 registers/thread with zero
stack/local memory.

## Code-size experiment ledger

The selector-vote profile has moved the kernel into an instruction-delivery
regime: instruction-cache hit rate is 97.00%, and no-instruction is the largest
sampled stall reason at 23.49%. Source correlation identifies four inlined BF
endpoint-resolver copies arising from peeled first/tail evaluation and source
A/B evaluation.

Run the following independently, retaining only measured winners:

1. unify the BF first and tail member evaluation in one `#pragma unroll 1`
   loop while preserving first-member initialization;
2. A/B that against zero-initialized BF sums with every member using the normal
   immediate-apply path;
3. against the winning BF loop, make the eight non-double-infinity selector
   warps execute one common two-load/one-subtraction endpoint path, leaving the
   double-infinity warp on its four-corner path;
4. erase the BF singleton/group distinction entirely, accepting extra
   arithmetic for one group-shaped execution path;
5. replace the manually unrolled E4 singleton/two-member executor with a
   `#pragma unroll 1` loop; and
6. optionally measure fully unspecialized four-corner endpoint evaluation as a
   code-size/divergence ceiling experiment.

Do not combine unmeasured variants. The first three items are the immediate
implementation sequence; items four through six remain follow-up experiments.

### Unified-loop and 8+1 results

Fresh selector-vote baseline medians were 18.058928 ms and 18.125376 ms. The
VM used 56 registers/thread, zero stack/local memory, 6,936 static
instructions, and 107/107 `BSSY`/`BSYNC` sites.

| Variant | Registers | VM instructions | `BSSY` / `BSYNC` | Log-24 medians | Decision |
|---|---:|---:|---:|---:|---|
| Peeled BF baseline | 56 | 6,936 | 107 / 107 | 18.058928 / 18.125376 ms | Retained |
| Unified BF, first-aware | 56 | 5,536 | 71 / 71 | 18.787376 / 18.680225 ms | Rejected |
| Unified BF, apply-all | 56 | 5,488 | 71 / 71 | 18.409969 / 18.489552 ms | Rejected |
| 8+1 endpoint | 55 | 8,440 | 155 / 155 | Compile gate only | Rejected |

Both unified loops removed approximately one fifth of the static VM, proving
that the peeled first/tail structure generated the duplicated endpoint
resolvers. Their added loop/control and first-member arithmetic nevertheless
made ordinary execution slower. The apply-all form was the better unified
variant but still lost to the peeled baseline.

The 8+1 endpoint source did not lower to a common machine path. Explicit
double-infinity handling plus branchless result selection expanded the
force-inlined VM by 1,504 instructions and 48 reconvergence pairs, so it was
rejected before GPU timing. A later unspecialization probe should go directly
to fully unconditional four-corner evaluation if its purpose is to measure the
branchless ceiling.

The original selector-vote source was restored and rebuilt. Its generated VM
exactly recovered 56 registers/thread, zero stack/local memory, 6,936
instructions, and 107/107 reconvergence sites. All 37 release tests pass; the
log-8 compute-sanitizer run reports zero errors and checksum
`0xbb2eb9da3c8c062b`. Every timed log-24 variant produced checksum
`0x8820ab14cacc9ff7`. The representative full profile therefore remains
`target/profiling/ncu/windowed_gkr_add_sub_l0_log24_selector_vote_full.ncu-rep`.

## Schedule, outlining, and materialized-source experiments

The compiler artifact generator now supports deterministic `compiler`,
`control-atoms`, `control`, and `source` schedules and reports a locality/control
census. All schedules contain the same semantic multiset of 72 atoms and 150
terms. Changing only the embedded artifact leaves the VM SASS byte-for-byte
identical.

| Schedule | Field / shape / class transitions | Same source A / B | Log-24 medians |
|---|---:|---:|---:|
| Compiler | 3 / 18 / 51 | 41 / 28 | 18.092848 / 18.064976 ms |
| Control atoms | 1 / 2 / 26 | 39 / 27 | 18.168575 / 18.243361 ms |
| Control plus member reorder | 1 / 2 / 26 | 33 / 28 | 18.309200 / 18.277008 ms |
| Source | 1 / 25 / 52 | 54 / 26 | 18.163376 / 17.996143 ms; repeats 18.034864 / 18.033569 / 18.008656 ms |

The control-oriented orderings lost despite sharply reducing transition counts.
The small but repeatable source-locality lead is retained in the checked-in
artifact.

The spill/code-size matrix used that source schedule:

| Variant | Registers | Stack | VM instructions | Log-24 median(s) | Decision |
|---|---:|---:|---:|---:|---|
| BF-majority inverted dispatch | 54 | 0 B | 6,936 | 18.160608 / 18.171728 ms | Reject |
| `#pragma unroll 1` E4 loop | 56 | 0 B | 5,544 | 18.771616 / 18.836399 ms | Reject |
| Unconditional four-corner loads | 56 | 0 B | 7,632 | 19.303568 / 19.300049 ms | Reject |
| Outlined E4 executor, unbounded | 118 | 0 B | 4,240 inline | 51.463150 ms | Reject |
| Outlined E4 executor, 56-register cap | 56 | 128 B | 4,144 inline | 20.637054 ms | Reject |
| Outlined endpoint resolver | 56 | 72 B | 3,536 inline | 32.513901 / 32.581535 ms | Reject |
| Five-block launch bound | 40 | 64 B | 7,096 | 18.811888 / 18.829504 ms | Reject |
| Outlined procedural generator | 56 | 0 B | 4,944 inline | 21.376896 / 21.607073 ms | Reject |

The capped E4 callee reported 124 spill-store bytes and 136 spill-load bytes;
the five-block kernel emitted 34 static local stores and 39 local loads. Small
spill frames are operationally tolerable, but neither the extra occupancy nor
the instruction-cache relief recovered their traffic/call cost.

### Host-resolved and materialized source winner

Resolving each source's final column pointer on the host removes the inline
source-to-address-slot lookup. It retains 56 registers and zero stack/local
memory while reducing the VM from 6,936 to 6,768 instructions and constant-load
sites from 112 to 79. Its two medians were 17.168400 and 17.152496 ms.

The two procedural setup windows are now also backed by real, deterministically
initialized BF allocations. This is valid for this throughput-only benchmark:
it intentionally changes the checksum from `0x8820ab14cacc9ff7` to
`0x29757dbb496ca7dc`, but preserves real allocation and load traffic. Removing
the procedural source switch gives one uniform BF load path:

- VM instructions: 3,456;
- `BSSY` / `BSYNC`: 3 / 3;
- static `LDC` / `LDG` sites: 68 / 129;
- 56 registers/thread, zero stack/local memory; and
- log-24 medians: 15.343072 / 15.342336 ms.

Compacting the launch source table to exactly 59 resolved pointers reduces the
descriptor from 2,448 to 1,968 bytes and constant-parameter usage from 3,344 to
2,864 bytes without changing the instruction counts. The retained medians are
15.334929 and 15.334336 ms. Removing the warp votes increased reconvergence
sites from 3 to 40 and regressed to 15.685216 ms, so the votes remain.

The final log-8 compute-sanitizer run reports zero errors. The new full VM-only
report is
`target/profiling/ncu/windowed_gkr_add_sub_l0_log24_materialized_pointer_full.ncu-rep`:

- NCU duration: 15.74 ms;
- dynamic instructions and branches: 21.23 billion / 509.02 million;
- theoretical/achieved occupancy: 75% / 74.27%;
- issue slots busy: 76.40%;
- instruction-cache hit rate: 99.998%;
- L1/TEX and L2 hit rates: 85.80% / 42.43%;
- physical FMA-heavy and ALU-heavy utilization: 83.25% / 62.57%; and
- PC-sampling proportions: 33.26% not selected, 26.08% math-pipe throttle,
  11.11% wait, 7.65% dispatch stall, 6.64% long scoreboard, and 2.29% no
  instruction.

Relative to the retained selector-vote profile, no-instruction samples fell
from 23.49% to 2.29% and the ICC hit rate rose from 97.00% to 99.998%. The
kernel is now primarily limited by FMA-heavy math throughput rather than
instruction delivery. The ordinary 15.334 ms medians are about 15% faster than
the fresh 18.059 / 18.125 ms pre-experiment baseline.

### Compact source-reference result

The resolved-pointer source table is a useful throughput upper bound, but its
eight bytes per source do not scale well with larger programs. The retained
replacement stores a four-byte source record with a `u16` window and `u16`
relative column, plus one eight-byte host-resolved base pointer per window.
The record is physically packed into one `u32`; an initial two-field C++ form
made `ptxas` issue two `LDC.U16` operations per resolution.

The trace stride is not stored in either table. All inputs have the same
domain size, so the kernel computes `log_trace = desc.log_rows + 3` once and
resolves BF/E4 operands with typed `window_base + (column << log_trace)`
arithmetic. The descriptor falls from 1,968 to 1,792 bytes. For the current
artifact, source/window metadata is 236 + 48 bytes rather than 472 bytes of
resolved source pointers.

| Source encoding | VM instructions | `LDC` sites | Log-24 medians |
|---|---:|---:|---:|
| Resolved pointer upper bound | 3,456 | 68 | 15.334929 / 15.334336 ms |
| Separate `u16` fields | 3,568 | 88 | 15.886256 / 15.886224 ms |
| Packed `u32` | 3,576 | 72 | 15.838512 / 15.837168 ms |

The packed form is retained. It keeps 56 registers/thread, zero stack/local
memory, and 3/3 `BSSY`/`BSYNC` sites. Its approximately 3.28% cost quantifies
the dependent window-base lookup plus address arithmetic that the pointer
upper bound avoids. The release edit build took 7.16 seconds, preserving the
quick kernel-iteration goal. All 42 all-target tests pass; the log-8
compute-sanitizer run reports zero errors and checksum `0x6bd630443cf77a02`.
Artifact regeneration is byte-identical at
`3af2e3c55c556c8f8a4ed019cfca04dbd754aba92f093aa332329069c34ab5e3`.

Both compact-source timings remain VM-only. The two procedural setup windows
are still materialized as real BF allocations before timing, so their
materialization cost is not represented here and must be accounted for by any
end-to-end implementation.
