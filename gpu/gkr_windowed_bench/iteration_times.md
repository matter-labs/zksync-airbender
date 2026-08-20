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

## Direct-coordinate and addressless-procedural result

The source-table indirection is now eliminated entirely. Every ordinary
instruction operand carries a direct 13-bit coordinate: seven low bits select
the relative column and six bits select one of at most 64 windows. The kernel
decodes that coordinate and indexes only the six-entry inline window-base
table. This reduces the descriptor from 1,792 to 1,536 bytes.

With the procedural windows still materialized, the direct-coordinate stage
reported 3,560 static VM instructions, 55 `LDC` sites, 129 `LDG` sites, and
3/3 `BSSY`/`BSYNC` sites. It retained 56 registers/thread with zero stack or
local memory. Two log-24 medians were 15.937296 and 15.937280 ms, with the
materialized-input checksum `0x29757dbb496ca7dc`. Despite removing 17 `LDC`
sites and 16 instructions relative to the packed source table, it was about
0.10 ms slower; the removed dependent metadata load was not the limiting cost.
Its requested source-load floor was 71,336,722,432 bytes.

The final experimental encoding gives the four actual procedural terms their
own cold BF opcodes:

- class 4 is a linear procedural-A term and stores the procedural kind in
  `source_a`;
- class 8 is BF-by-procedural-B and stores a direct BF coordinate in
  `source_a` plus the procedural kind in `source_b`.

The checked-in add/sub layer-0 artifact contains exactly two terms of each
shape and no procedural group members. Ordinary term classes are rejected if
they reference a virtual window, keeping the common BF resolver free of a
procedural discriminator. The allocation plan now leaves virtual-window bases
null and allocates no storage for them. At log 24 this removes 128 MiB of BF
storage, reducing total resident storage from 8,618,256,560 to 8,484,038,832
bytes.

The honest procedural VM has 4,384 static instructions, 57 `LDC` sites, 133
`LDG` sites, 3/3 reconvergence sites, 56 registers/thread, and zero stack/local
memory. Explicitly constructing zero BF triplets in registers also removes all
three compiler-generated BF evaluator globals; only the pre-existing 96 bytes
of E4 zero objects remain. Two ordinary log-24 runs produced:

| Run | Minimum | Median | Checksum |
|---|---:|---:|---:|
| Direct procedural 1 | 15.861824 ms | 15.864608 ms | `0x8820ab14cacc9ff7` |
| Direct procedural 2 | 15.861312 ms | 15.864576 ms | `0x8820ab14cacc9ff7` |

The original procedural checksum is restored, and the honest path is slightly
faster than the materialized direct-coordinate checkpoint. A log-8
compute-sanitizer run reports zero errors and checksum
`0xbb2eb9da3c8c062b`. Non-lineinfo release rebuilds took 6.97 seconds for the
materialized stage and 7.02 seconds for the final procedural stage. The final
requested source-load floor is 70,665,633,792 bytes. The final source-scheduled
artifact hash is
`9519a96ed680a7505b029229cb396ccf48f65bd55e249cafc23545fd641b9f4b`.

The representative VM-only report is
`target/profiling/ncu/windowed_gkr_add_sub_l0_log24_direct_procedural_full.ncu-rep`:

- NCU duration: 16.20 ms;
- dynamic instructions and branches: 22.41 billion / 727.25 million;
- theoretical/achieved occupancy: 75% / 74.00%;
- L1/TEX, L2, and ICC hit rates: 86.02% / 41.57% / 99.90%;
- issue slots busy: 77.93%;
- physical shared-FMA-heavy-plus-ALU-lite and ALU-heavy utilization: 81.54% /
  66.05%; and
- PC-sampling proportions: 34.96% not selected, 20.25% math-pipe throttle,
  12.89% wait, 9.83% dispatch stall, 6.78% long scoreboard, and 2.93% no
  instruction.

## Five-block occupancy probe

A five-block probe kept all three E4 accumulator planes in shared memory and
changed the launch bound from four to five blocks. Five blocks require 74,240
bytes of shared memory including the measured driver reserve. A 73% preferred
carveout request—the rounded-up fraction actually required—selects the next
supported hardware partition, 102.4 KiB; there is no intermediate partition on
this device.

Register allocation is quantized in eight-register-per-thread tiers. A nominal
44-register allocation would round to 48 and require 69,120 registers for five
288-thread blocks, exceeding the 65,536-register SM file. Ptxas therefore
compiled the probe at 40 registers/thread. Relative to the 56-register
baseline, it introduced a 72-byte stack frame, 59 static `LDL` sites, 53 static
`STL` sites, and grew the VM from 4,384 to 4,616 static instructions. Static
shared memory remained 13,824 bytes, reported as 14,848 bytes including the
driver reserve.

NCU confirmed five-block residency: register and warp limits were both five
blocks, shared memory admitted six, theoretical occupancy was 93.75%, and
achieved occupancy was 90.99%. Two ordinary log-24 runs nevertheless
regressed:

| Run | Minimum | Median | Checksum |
|---|---:|---:|---:|
| Five blocks 1 | 16.457184 ms | 16.472641 ms | `0x8820ab14cacc9ff7` |
| Five blocks 2 | 16.449152 ms | 16.463440 ms | `0x8820ab14cacc9ff7` |

The full rejected-variant report is
`target/profiling/windowed_five_block/five_block_full.ncu-rep`. Compared with
the representative four-block profile:

| Metric | Four blocks | Five blocks |
|---|---:|---:|
| NCU duration | 16.20 ms | 16.87 ms |
| Dynamic instructions | 22.41 billion | 23.81 billion |
| Achieved occupancy | 74.00% | 90.99% |
| Issue slots busy | 77.93% | 79.84% |
| Shared FMA-heavy + ALU-lite | 81.54% | 75.71% |
| ALU-heavy | 66.05% | 59.45% |
| L1/TEX hit rate | 86.02% | 51.36% |
| L2 hit rate | 41.57% | 84.04% |
| Local spill requests | 0 | 62,521,344 |
| Not-selected samples | 34.96% | 40.17% |
| Math-pipe throttle samples | 20.25% | 22.66% |
| Wait samples | 12.89% | 9.50% |
| Dispatch-stall samples | 9.83% | 8.77% |
| Long-scoreboard samples | 6.78% | 7.30% |
| No-instruction samples | 2.93% | 2.26% |

The extra warps reduce wait, dispatch, and instruction-starvation stalls, but
those were not the dominant limit. They increase contention on already-busy
math pipelines, while forced spills add 6.26% more dynamic instructions and
the larger shared partition substantially reduces L1 capacity. The five-block
variant is rejected; the 56-register, four-block launch bound and 60% carveout
are restored.

## Lazy BF-group Montgomery reduction

The round-zero BF artifact now opts ten groups into a product-prefix encoding.
The BF group header's formerly-zero `source_b` stores the lazy product count;
factor bit 15 marks a reduction boundary and the low 15 bits retain the
immediate ID. The generator orders direct BF products before linear members,
marks every fourth product and the final product, and leaves groups with zero
or one product on the eager path. The retained artifact census is ten lazy
groups, 72 lazy products, and 21 boundaries. Its SHA-256 is
`c264c0969e8df75e3b05dde5492f57dd0519834c2ebcb41dace2d5474e30091f`.

Each lazy contribution is accumulated as a nonnegative raw `u64` Montgomery
product. Negative terms negate one operand as `p - a`; banked terms first scale
one operand with the existing reduced BF multiply. At most four raw products
are accumulated before `bf::red_wide`. Intermediate boundaries rebase the
reduced limb with a raw multiply by `MONT_R`, while the final product boundary
returns to the ordinary BF group sum for the linear tail. The validator checks
the product prefix, masked immediate IDs, final boundary, and four-product
bound; old artifacts select the eager path because their header payload is
zero.

The candidate keeps 56 registers/thread, zero stack/local memory, 13,824 bytes
of static shared memory (14,848 bytes including the driver reserve), and the
four-block launch bound. An exact VM-section opcode census, stopping at the
next function and excluding `NOP`, counts 5,731 static instructions versus
4,384 before the change; the new binary has 86 `LDC`,
207 `LDG`, 1,007 `IMAD`, and 3/3 `BSSY`/`BSYNC` sites. A log-8
compute-sanitizer run reports zero errors and checksum
`0xbb2eb9da3c8c062b`.

Two contemporaneous log-24 baseline and candidate runs produced:

| Run | Minimum | Median | Checksum |
|---|---:|---:|---:|
| Eager baseline 1 | 15.862464 ms | 15.864592 ms | `0x8820ab14cacc9ff7` |
| Eager baseline 2 | 15.862720 ms | 15.865120 ms | `0x8820ab14cacc9ff7` |
| Lazy candidate 1 | 15.809312 ms | 15.812272 ms | `0x8820ab14cacc9ff7` |
| Lazy candidate 2 | 15.810080 ms | 15.813264 ms | `0x8820ab14cacc9ff7` |

The approximately 0.33% improvement is repeatable. The full VM-only report is
`target/profiling/lazy_bf_reduction/lazy_bf_reduction_full.ncu-rep`:

- NCU duration is 16.18 ms, with 21.79 billion dynamic instructions and 613.42
  million branches;
- dynamic `IMAD` falls from 4,149,870,592 to 4,027,187,200, a 2.96% reduction;
- theoretical/achieved occupancy remains 75% / 73.96%;
- shared-FMA-heavy-plus-ALU-lite utilization falls from 81.54% to 79.25%, while
  ALU-heavy moves from 66.05% to 66.44%;
- issue slots busy fall from 77.93% to 76.02%;
- L1/TEX, L2, and ICC hit rates are 84.57% / 46.94% / 98.16%, versus the
  eager profile's 86.02% / 41.57% / 99.90%; and
- PC-sampling proportions are 33.25% not selected, 26.10% math-pipe throttle,
  10.97% wait, 8.65% dispatch stall, 5.54% long scoreboard, and 3.44% no
  instruction.

The larger static body measurably hurts ICC locality and does not translate the
full IMAD reduction into elapsed time, but the ordinary timing win is stable
without an occupancy or spill regression. The lazy artifact and executor are
retained as the next experimental baseline.

## Lazy BF product-loop deduplication

The first lazy executor force-inlined the complete BF product source resolver,
two endpoint interpolators, and immediate dispatch at three source callsites:
the peeled first product, loop body, and peeled final product. Its linear tail
also called the general BF evaluator, so ptxas emitted product arms that the
generated schedule never executes. This explains why removing reductions
lowered dynamic instructions while the static VM grew sharply.

The artifact validator now makes the generator's schedule invariant explicit:
after a nonzero lazy product prefix, every remaining BF group member must be
linear. A product in that tail is rejected as `LazyProductTailClass`. This
permits the CUDA lazy tail to use a one-case linear evaluator without embedding
unreachable product or procedural-linear machinery.

Two loop shapes were measured independently. Variant A starts three `u64`
sums at zero and runs the entire product prefix through one `#pragma unroll 1`
loop and one evaluator callsite. Intermediate encoded boundaries reduce and
rebase; the final member is recognized from the loop counter and receives only
the post-loop final reduction. Variant B peels the first product and unifies
the remainder. It checks a boundary on the peeled first member because that is
legal in the artifact even though the current generator does not emit it.

The table uses a consistent `cuobjdump` census over only the VM function,
excluding `NOP` instructions:

| Variant | Registers | Stack / local | VM instructions | `LDG` | `LDC` | `IMAD` | `IADD` | `BRA` | `BSSY` / `BSYNC` | Log-24 medians |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Three-site baseline | 56 | 0 / 0 B | 5,731 | 207 | 86 | 1,007 | 1,463 | 374 | 3 / 3 | 15.814000 / 15.813504 ms |
| Unified zero-init (A) | 56 | 0 / 0 B | 4,715 | 151 | 67 | 853 | 1,278 | 277 | 3 / 3 | 15.447056 / 15.446784 ms |
| Peeled first (B) | 56 | 0 / 0 B | 4,952 | 167 | 75 | 898 | 1,332 | 282 | 3 / 3 | 15.680112 / 15.678928 ms |

All three candidate binaries used 13,824 bytes of static shared memory (14,848
bytes including the driver reserve). Both new variants passed all 60 library
tests, reproduced log-8 checksum `0xbb2eb9da3c8c062b` and log-24 checksum
`0x8820ab14cacc9ff7`, and reported zero compute-sanitizer errors. Variant A is
retained: its two medians are about 2.32% faster than the contemporaneous
three-site baseline, while Variant B gives back most of that improvement.

The representative full VM-only report is
`target/profiling/lazy_bf_loop_dedup/retained_full.ncu-rep`. Relative to the
previous lazy-reduction report, using the same raw metrics and normalization:

- NCU duration falls from 16.181856 to 15.836992 ms;
- dynamic instructions fall from 21,790,523,392 to 21,601,648,640, while
  dynamic `IMAD` is nearly unchanged at 4,027,187,200 versus 4,025,810,944;
- dynamic `BRA` rises from 609,878,016 to 625,541,120 because the unified loop
  executes more control, but duplicated evaluator control and selector work
  disappear elsewhere;
- theoretical/achieved occupancy remains 75% / 74.01%, and issue slots busy
  rise from 76.02% to 77.18%;
- shared-FMA-heavy-plus-ALU-lite and ALU-heavy utilization rise from 79.25% /
  66.44% to 80.22% / 67.16%;
- L1/TEX, L2, and ICC hit rates move from 84.57% / 46.94% / 98.16% to
  85.66% / 42.64% / 98.25%; and
- all-sample PC proportions move from 32.40% to 34.70% not selected, 25.27%
  to 22.00% math-pipe throttle, 11.29% to 11.13% wait, 8.51% to 9.46%
  dispatch stall, 6.45% to 6.16% long scoreboard, and 3.47% to 3.72% no
  instruction.

The gain therefore does not come from eliminating another material number of
Montgomery multiplications. It comes from removing force-inlined interpreter
machinery and about 189 million executed instructions while preserving the
lazy-reduction arithmetic. The kernel remains primarily limited by the shared
FMA-heavy/ALU-lite pipe, but its instruction/control overhead is lower.

## Warp-local three-lane partial-store probe

The retained epilogue performs three sequential warp reductions and lets lane
zero issue one streaming E4 store after each reduction. The probe instead let
lane `cell` retain the completed result for cell `cell`; after all reductions,
lanes zero through two issued one indexed store instruction to their three
contiguous partial-output locations. It did not stage data across warps, add a
barrier, or change the requested output bytes.

Ptxas emitted one VM `STG.E.EF.128` site instead of three while preserving 56
registers/thread, zero stack/local memory, and 14,848 reported shared bytes.
All 60 library tests passed, and the log-8 Compute Sanitizer run reproduced
checksum `0xbb2eb9da3c8c062b` with zero errors.

Two candidate and contemporaneous baseline log-24 trials produced:

| Variant | Median 1 | Median 2 |
|---|---:|---:|
| Three-lane store | 15.470287 ms | 15.469280 ms |
| Retained lane-zero stores | 15.446192 ms | 15.445808 ms |

The candidate is consistently about 0.15% slower. Reducing the number of warp
store instructions does not compensate for selecting and carrying the
lane-owned E4 result through the remaining reductions. The original three
lane-zero stores are restored.

## Swizzled three-output reduction probes

Two follow-up probes attempted to reduce all three output cells concurrently.
The first multiplied every shared accumulator by `eq`, then assigned eight
lanes to each cell. Those lanes directly summed four strided shared values,
wrote 24 partials back in a modulo-four swizzle, and finished the three
independent eight-way reductions with shuffle masks 16, 8, and 4. The second
probe replaced the direct shared 1:4 sums with two shuffle stages per cell;
only the resulting 24 four-row partials passed through shared memory before
the same concurrent final reduction.

Both probes retained 56 registers/thread, zero stack/local memory, and 14,848
reported shared bytes. Both emitted one streaming E4 output-store site. The
direct-shared version reduced the VM from 60 to 12 scalar shuffle instructions;
the shuffle-first version emitted 36. Their exact VM-only SASS census and
log-24 timings were:

| Variant | VM instructions | `SHFL.BFLY` | `LDS.128` | `STS.128` | `STG.E.EF.128` | Median 1 | Median 2 |
|---|---:|---:|---:|---:|---:|---:|---:|
| Retained independent reductions | 4,715 | 60 | 9 | 10 | 3 | 15.445792 ms | 15.446688 ms |
| Direct-shared 1:4 + shuffles | 4,576 | 12 | 14 | 15 | 1 | 15.515040 ms | 15.515232 ms |
| Shuffle 1:4 + shared transpose | 4,624 | 36 | 10 | 13 | 1 | 15.519567 ms | 15.519360 ms |

The direct-shared and shuffle-first candidates are about 0.45% and 0.47%
slower than the contemporaneous control. The reduction instruction savings do
not repay the shared-memory transpose and its dependency/reconvergence cost;
moving more of the first stage back to shuffles is slightly worse still. Both
candidates reproduced the log-8 checksum `0xbb2eb9da3c8c062b`; the direct-shared
candidate also passed Compute Sanitizer with zero errors, and the shuffle-first
candidate passed the same check independently. The original three sequential
warp reductions and stores are restored.

## Round-zero linear BF/E4 specialization

The retained round-zero encoding uses the high bit of a BF or E4 group
header's `source_b` as validated product-presence metadata. BF headers use the
low 15 bits as a product-prefix count: zero is generic eager encoding, one is
a validated one-product eager prefix, and two or more select the existing lazy
wide-product prefix. E4 headers keep their implicit arity of two and require
all low payload bits to be zero. The decoder rejects either direction of a
flag/member mismatch, and the generator derives the bit from member classes.

Product-free BF atoms now have a distinct pair-shaped executor. The five
infinity-selector warps advance over a group without loading its members,
loading its batching coefficient, or touching shared accumulators. The four
Boolean-selector warps load only the two selected `bit2` endpoints, apply BF
immediates to a two-cell sum, and fold accumulator cells zero and one. For a
product group with an encoded prefix, infinity warps skip its known-linear
tail and Boolean warps apply that tail to the first two product sums only. The
three product cells and the wide lazy-product reduction are unchanged.

The same second-stage specialization applies to product-free E4 atoms. The
source-scheduled add/sub artifact has one pure-linear E4 pair group; its other
E4 atoms are product-bearing and stay on the general triplet executor. This is
a round-zero wire invariant, not an add/sub-layer-zero CUDA special case.

All timed variants retained 56 registers/thread, zero stack/local memory, and
13,824 bytes of static shared memory (14,848 bytes including the driver
reserve). The static census excludes `NOP` instructions:

| Variant | VM instructions | `LDG` | `LDC` | `IMAD` | `IADD` | `BRA` | `BSSY` / `BSYNC` | Median 1 | Median 2 | Decision |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| Contemporaneous control | 4,715 | 151 | 67 | 853 | 1,278 | 277 | 3 / 3 | 15.447472 ms | 15.445888 ms | Superseded |
| BF pair/product-tail specialization | 5,765 | 185 | 93 | 1,010 | 1,448 | 418 | 3 / 3 | 14.455248 ms | 14.454880 ms | Retain |
| Merged product-prefix tails | 5,009 | 157 | 78 | 912 | 1,336 | 310 | 3 / 3 | 14.539552 ms | 14.541248 ms | Reject |
| BF plus E4 pair specialization | 6,028 | 189 | 101 | 1,068 | 1,543 | 425 | 3 / 3 | 13.998848 ms | 13.998960 ms | Retain |
| Split BF/E4 top-level loops | 6,080 | 189 | 103 | 1,071 | 1,548 | 431 | 3 / 3 | 14.007088 ms | 14.010144 ms | Reject |

The product-prefix merge proved that a smaller static body is not sufficient:
although it removed 756 instructions from the BF candidate, its less
specialized control layout was about 0.59% slower. Likewise, replacing the
per-atom field dispatch with separate BF and E4 loops added loop overhead and
lost about 0.07%. The retained BF+E4 candidate is about 9.37% faster than the
contemporaneous control and 3.16% faster than the BF-only candidate.

The retained full VM-only report is
`target/profiling/linear_bf_specialization/retained_full.ncu-rep`. Relative to
`target/profiling/lazy_bf_loop_dedup/retained_full.ncu-rep`:

- NCU duration falls from 15.836992 to 14.304096 ms;
- dynamic instructions fall from 21,601,648,640 to 19,695,730,688;
- dynamic `IMAD`, `IADD`, and `BRA` fall from 4,025,810,944 / 5,695,537,152 /
  625,541,120 to 3,596,746,752 / 5,114,429,440 / 588,578,816;
- achieved occupancy moves from 74.01% to 70.96%, while issue slots busy rise
  from 77.27% to 77.81%;
- FMA-heavy, its ALU-lite subpipe, and ALU-heavy utilization move from 80.22%
  / 37.31% / 67.16% to 80.99% / 36.12% / 67.99%;
- L1/TEX, L2, and ICC hit rates move from 85.66% / 42.64% / 98.25% to 83.96%
  / 48.64% / 97.91%; and
- all-sample PC proportions are 33.63% not selected, 23.51% math-pipe
  throttle, 12.70% wait, 9.59% selected, 8.37% dispatch stall, 4.67% no
  instruction, 4.39% long scoreboard, and 3.05% short scoreboard.

The final candidate passes all 65 artifact/library tests, reproduces log-8
checksum `0xbb2eb9da3c8c062b` and log-24 checksum
`0x8820ab14cacc9ff7`, and reports zero Compute Sanitizer errors. The regenerated
artifact SHA-256 is
`0360242bf31d20f837bb9618c3b64c5f8b9f288e540f9e6266c6c72c509ae50d`.
The log-24 requested source-load floor remains 70,665,633,792 bytes; the
specialization removes arithmetic and accumulator traffic, not the benchmark's
allocation footprint or declared input-load floor.

## Fast-affine BF-group encoding probe

A follow-up encoding reserved bit 15 of a BF group header's `source_a` field
as a validated fast-affine promise and used the low 15 bits for arity. The
source-scheduled round-zero artifact had 14 matching groups: three pure
two-linear-member `+1/+1` groups and eleven product-prefix groups with exactly
one `-1` linear tail. E4 headers rejected the bit. The CUDA candidate used
direct, manually unrolled addition for the pure groups and direct subtraction
for the one-tail product groups, bypassing generic BF immediate dispatch.

The candidate kept 56 registers/thread, zero stack/local memory, and 13,824
bytes of static shared memory (14,848 bytes including the driver reserve). It
passed all 69 artifact-generator/library tests, reproduced log-8 checksum
`0xbb2eb9da3c8c062b` under Compute Sanitizer with zero errors, and reproduced
log-24 checksum `0x8820ab14cacc9ff7`. Its candidate artifact SHA-256 was
`3fee3d861dbbe585c2e9c64a28af5f57d2dc1e65736a407d4a5e122b7d52fc84`.

The static VM census and locked 10-warmup/100-iteration timings were:

| Variant | VM instructions | `LDG` | `LDC` | `IMAD` | `IADD` | `BRA` | `BSSY` / `BSYNC` | Median 1 | Median 2 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Retained control | 6,028 | 189 | 101 | 1,068 | 1,543 | 425 | 3 / 3 | 14.000880 ms | 13.999952 ms |
| Fast-affine candidate | 6,132 | 197 | 109 | 1,083 | 1,559 | 431 | 3 / 3 | 14.207392 ms | 14.207504 ms |

An interleaved rerun of the preserved control measured 13.999744 ms, ruling
out a clock or thermal shift. The candidate is therefore about 1.48% slower:
the extra arity mask, flag branches, and 104-instruction static expansion cost
more than eliminating immediate dispatch in 14 groups. A full NCU capture was
not taken because the ordinary timing regression was large, repeatable, and
already accompanied by the unfavorable static-code delta.

The experiment is rejected. The wire encoding, decoder/generator changes,
CUDA paths, and candidate artifact were removed. The restored artifact SHA-256
is `0360242bf31d20f837bb9618c3b64c5f8b9f288e540f9e6266c6c72c509ae50d`,
and the log-24 requested source-load floor remains 70,665,633,792 bytes.

## Autonomous accumulator-arithmetic probes

### Explicit BF multiply plus add

The BF-valued accumulator fold previously used the generic scalar
`e4::fma(core, sum, accumulator)`. Its four underlying `bf::fma` operations
use `red_wide` because the accumulator is injected into the high word before
Montgomery reduction. The candidate instead performs `e4::mul(core, sum)`
followed by `e4::add`, allowing the products to use the narrower `bf::red`
path before ordinary modular addition.

Ptxas kept 56 registers/thread, zero stack/local memory, and 13,824 bytes of
static shared memory (14,848 bytes including the driver reserve). The VM-only
static body fell from 6,028 to 6,004 non-NOP instructions, with `IADD` sites
falling from 1,543 to 1,523; `LDG`, `LDC`, `IMAD`, `BRA`, `BSSY`, and `BSYNC`
counts were unchanged.

Locked 10-warmup/100-iteration log-24 timings were:

| Variant | Median 1 | Median 2 | Interleaved median | Checksum |
|---|---:|---:|---:|---:|
| Retained fused control | 14.000384 ms | 13.998624 ms | 13.998528 ms | `0x8820ab14cacc9ff7` |
| Explicit multiply plus add | 13.861649 ms | 13.861456 ms | — | `0x8820ab14cacc9ff7` |

The approximately 0.98% improvement is repeatable and is retained as the new
working baseline. On this Blackwell target, avoiding the general wide fused
reduction is cheaper than the nominal source-level fusion.

### Hoisted E4 batching-core non-residue products

The E4-valued fold was rewritten locally to compute the batching core's three
`mul_by_non_residue` limbs once per atom and reuse them across its two or three
output cells. A benchmark-local flat quartic multiply duplicated the exact
four lazy accumulators used by `e4::mul` and then added the existing
accumulator.

Nvcc already performs this common-subexpression elimination across the
unrolled cell loop: the candidate and retained BF multiply-plus-add kernel had
byte-identical VM SASS. Both contained 6,004 non-NOP instructions with
identical opcode counts and retained 56 registers/thread, zero stack/local
memory, and 14,848 reported shared bytes. Compute Sanitizer reported zero
errors and reproduced log-8 checksum `0xbb2eb9da3c8c062b`.

The source-expanded candidate measured 13.859552 and 13.861344 ms versus the
retained kernel's 13.861649 and 13.861456 ms. With identical generated code,
the sub-0.01% difference is measurement noise. The local helper is rejected
and the clearer shared `e4::fma` call is restored.

### Factored-equality high-product warp broadcast

The next isolated probe targets an epilogue redundancy visible from the
factor geometry. At log 24, the low equality factor owns five bits, so every
lane in a warp has the same two high-factor indices. The retained kernel
nevertheless performs the full high-high E4 multiplication independently in
all 32 lanes before multiplying by each lane's low factor.

The candidate elects one leader per subgroup of lanes sharing the high
indices, computes the high product only in those leaders, and broadcasts its
four limbs with four indexed warp shuffles. The subgroup is derived from
`min(eq_sizes.low, 5)`, so the scheme remains correct for every supported
factor geometry: log-24 and log-8 use one leader per warp, smaller low factors
use multiple leaders, and a zero-bit low factor degenerates to one leader per
lane. This should exchange up to 31 of 32 redundant full E4 multiplications
for four shuffle instructions per thread without changing tables or
allocations.

The initial generic-mask form retained 56 registers/thread, zero stack/local
memory, and 14,848 reported shared bytes. It emitted 6,020 non-NOP VM
instructions and measured 13.850161, 13.850272, and 13.847296 ms against
interleaved multiply-plus-add controls of 13.860368 and 13.859552 ms. A simpler
but equivalent identity, `leader_lane = lane & ~low`, removed the min/shift/mask
bookkeeping. It emitted 6,017 instructions, versus 6,004 for the control, with
four additional `SHFL` sites and one additional `BRA`; the other principal
opcode counts matched the multiply-plus-add kernel. Its medians were
13.848352 and 13.849136 ms against an interleaved 13.859600 ms control, a
repeatable approximately 0.08% improvement. Compute Sanitizer reported zero
errors and reproduced both pinned checksums.

The original arithmetic-saving rationale needs an important qualification:
SIMT issues the high multiplication once per warp even when all lanes are
active, so predicating it to leaders does not remove 31 warp instructions.
Only the small measured code-shape/active-mask effect is real; the result is
not a 32-fold arithmetic saving. Five alternating timing comparisons favored
the simplified candidate, and the operand-order isolation below independently
confirmed its approximately 0.11% incremental gain. It is retained on that
empirical basis, not on the rejected per-lane arithmetic argument.

### Duplicate-product reuse census

An independent decoded-artifact census found 109 product members and 109
distinct `(source_a, source_b, class)` triples. There are zero duplicate
products to cache or reference across atoms, so no product-reuse encoding or
register cache was implemented.

### Equality multiply operand-order probe

The final epilogue micro-probe swaps `e4::mul(accumulator, eq)` to the
commutative `e4::mul(eq, accumulator)`. This places the cell-invariant equality
value in the flat multiplier's first operand, allowing nvcc to reuse its three
non-residue products across the unrolled three-cell loop if they were not
already eliminated. The candidate is bit-exact because each quartic output
accumulates the same four non-overflowing `u64` products.

The operand swap alone emitted 5,970 non-NOP VM instructions, including 1,056
`IMAD`, 1,517 `IADD`, 425 `BRA`, and 60 `SHFL` sites. It measured 13.844849
and 13.846208 ms. Combined with the equality-high broadcast it emitted 5,982
instructions, including the same `IMAD` and `IADD` counts, 426 `BRA`, and 64
`SHFL` sites. Three locked combined medians were 13.830336, 13.829360, and
13.829888 ms. Both variants retained 56 registers/thread, zero stack/local
memory, and 14,848 reported shared bytes; Compute Sanitizer found zero errors
and both pinned checksums matched.

Putting equality first is retained: compared with the broadcast-only form it
removes 35 static instructions, including 12 `IMAD`, six `IADD`, six
`VIMNMX`, and six `LOP3` sites. This confirms that nvcc reuses equality's
three non-residue products across the unrolled output cells. The broadcast is
also retained because its isolated incremental improvement remained stable
when layered on the operand swap, despite its less direct SIMT mechanism. The
combined kernel is approximately 1.21% faster than the original fused control.

### Partial-warp active-guard probe

For the measured log-8 and log-24 configurations, `logical_rows` is divisible
by 32 and the VM grid contains exactly `logical_rows / 32` blocks. Therefore
every launched lane is active, while the generic kernel still clamps the row
and selects zero instead of the equality-weighted accumulator in every output
cell. The next isolated candidate removes only that row guard and output
select. The candidate is valid for log trace at least 8, including both pinned
benchmark sizes, but not for the crate's currently accepted log-3 through
log-7 geometries. It will be retained only if the measured gain justifies
either an explicit minimum-size contract or a separate small-geometry path;
otherwise the generic guard remains.

Ptxas moved in the wrong direction after the apparent source simplification:
the candidate emitted 5,986 non-NOP VM instructions versus 5,982 for the
control, adding two `IMAD`, one `IADD`, two `LOP3`, and one `SEL` site while
removing two `ISETP` and three `BRA` sites. Resources remained 56
registers/thread, zero stack/local memory, and 14,848 reported shared bytes.
Two locked candidate medians were 14.018720 and 14.016928 ms, while the
interleaved preserved control measured 13.829184 ms. The checksum remained
`0x8820ab14cacc9ff7`, but the candidate was approximately 1.36% slower. It is
rejected and the generic active guard is restored; no supported-size contract
is narrowed.

### Fused wide-product accumulation probe

The final profile identifies raw lazy BF products as the largest
math-pipe-throttle source location. The retained loop computes each raw `u64`
product with `mul_wide`, returns a three-cell temporary, and then adds it to
the running wide sums. The next candidate instead passes the sums into that
resolver and uses `mad_wide(operand_a, operand_b, sum)` directly. This preserves
the same nonnegative terms, encoded four-product overflow boundaries, and
final Montgomery reductions. It may remove the separate 64-bit additions and
shorten live ranges, but it may also move work from the less-loaded ALU-heavy
pipe onto the already limiting FMA-heavy pipe; SASS and paired timing decide.

The candidate retained 56 registers/thread, zero stack/local memory, and
14,848 reported shared bytes. Its VM body fell only from 5,982 to 5,980
non-NOP instructions: three `IADD` sites disappeared, one `BRA` appeared, and
the 1,056 `IMAD` sites were unchanged. The dynamic loop effect was much larger
than that static delta suggests. Two locked candidate medians were 13.684336
and 13.684384 ms versus a 13.830976 ms interleaved control, a repeatable 1.06%
improvement. Both pinned checksums match, and log-8 Compute Sanitizer reports
zero errors.

A focused VM-only report at
`target/profiling/autonomous_math_pass/mad_wide_profile.ncu-rep` confirms the
mechanism. Relative to the pre-candidate full report, dynamic instructions
fall from 19,271,647,232 to 19,111,804,928 and NCU duration falls from
14.153248 to 13.992160 ms. Shared FMA-heavy utilization moves from 80.97% to
80.66%, ALU-heavy from 66.86% to 66.51%, math-pipe-throttle cycles per issued
instruction from 2.591 to 2.510, and issue activity from 76.98% to 77.16%.
The fused accumulator is retained.

### Shift/subtract Montgomery rebase probe

Every intermediate lazy-product boundary reduces its wide sum and then
rebases the reduced limb with `mul_wide(limb, MONT_R)` so more raw products can
be accumulated. For Baby Bear, `MONT_R = 2^28 - 2` exactly. Replacing that
constant multiply with `(u64(limb) << 28) - (u64(limb) << 1)` produces the
identical nonnegative integer, so it preserves both the overflow proof and all
later reductions. The current SASS has three static `IMAD.WIDE` sites for this
operation inside the dynamically frequent boundary path. The candidate tests
whether explicit shift/subtract moves enough work from the limiting shared
FMA-heavy pipe to the less-loaded ALU-heavy pipe; ptxas may also canonicalize
the expression back to the multiply, in which case it is a no-op.

Ptxas did exactly that: the candidate and retained fused-wide kernel have
byte-identical VM SASS, including 5,980 non-NOP instructions, 1,056 `IMAD`,
1,514 `IADD`, and 377 `SHF` sites, with identical resource usage. The three
rebases remain `IMAD.WIDE.U32` by constant `0x0ffffffe`. No timing run is
meaningful for identical generated code; the explicit shift/subtract source is
rejected and the clearer `mul_wide` form is restored.

### In-place E4 term accumulation probe

The product-bearing E4 executor currently receives each evaluated term as a
three-cell E4 triplet and then copies or add/subtracts that 12-limb temporary
into the group sums. The candidate keeps the same term switch, interpolation,
field multiplications, signs, and reductions, but lets each switch arm consume
its three result cells directly into the destination sum. Separate compile-time
initialize and accumulate forms avoid a dynamic first-member branch. No field
operation is fused into `red_wide`: E4-by-E4 coefficients are already at the
four-product bound, and adding another high-word term would exceed its valid
domain. This probe targets only temporary live ranges and ptxas scheduling.

The callback form retained 56 registers/thread and zero stack/local memory,
but expanded the VM from 5,980 to 6,295 non-NOP instructions. It removed 12
static `LDG` sites while adding five `IMAD`, 123 `IADD`, 88 `VIMNMX`, 29
`BRA`, five `LOP3`, and 49 `MOV` sites. Two locked medians were 14.191136 and
14.193056 ms versus a 13.683152 ms interleaved fused-wide control, a roughly
3.71% regression with the correct checksum. The candidate is rejected and
the compiler-friendly return-by-value triplet is restored.

### Lazy-boundary predicate-order probe

The unified wide-product loop currently tests `member + 1 <
product_prefix_count` before the instruction's encoded `REDUCE_AFTER` bit.
Only 21 of the artifact's 72 lazy products carry that bit, including ten final
products that must not rebase. Reversing the short-circuit operands preserves
the exact boundary semantics and wire encoding but gives ptxas the opportunity
to skip the loop-end comparison for the 51 unmarked products. The boundary
line is also a top wait/math PC-sampling location in the retained profile.

Ptxas canonicalized both predicate orders to byte-identical VM SASS: 5,980
non-NOP instructions with identical `IMAD`, `IADD`, `ISETP`, `BRA`, and `LOP3`
counts and unchanged resources. No timing distinction exists; the original
loop-end-first source order is restored.

### Intermediate-only lazy-boundary encoding probe

Source operand order cannot change the flattened SASS: every lazy product
still executes an `IADD`, `LOP3`, `ISETP`, and branch to combine the loop-end
test with `REDUCE_AFTER`. The stronger candidate changes the experimental wire
invariant so only intermediate reduce-and-rebase boundaries carry the bit; the
last product is always handled by the existing unconditional post-loop final
reduction. The generator marks each fourth non-final product, and the validator
rejects a rebase bit on the final product while retaining the maximum-four-raw-
products check. The VM can then branch on the bit alone. This does not change
term order, immediate IDs, raw-product windows, or arithmetic results, but it
requires a regenerated artifact and updated validator fixtures.

The regenerated source-scheduled artifact contains the same 10 lazy groups
and 72 lazy products, with 11 intermediate boundary bits instead of 21 bits
including final products. Regeneration took 21.23 seconds. All 65
artifact-generator/library tests pass. The artifact SHA-256 is now
`10b5559c9d51cddf36e3208e41f446466ed3b72ae94bc5fcf93853f80cb9ec7e`.

Ptxas retained 56 registers/thread, zero stack/local memory, and 14,848
reported shared bytes. The VM falls from 5,980 to 5,978 non-NOP instructions;
the only static opcode change is two fewer `LOP3` sites. Two locked medians
were 13.639392 and 13.637248 ms versus a 13.683168 ms interleaved control, a
repeatable approximately 0.33% improvement. Both pinned checksums match, and
log-8 Compute Sanitizer reports zero errors.

The focused report at
`target/profiling/autonomous_math_pass/intermediate_only_profile.ncu-rep`
shows dynamic instructions falling from 19,111,804,928 to 19,026,870,272 and
NCU duration from 13.992160 to 13.934592 ms. ALU-heavy utilization falls from
66.51% to 66.13%, math-pipe-throttle cycles per issued instruction from 2.510
to 2.498, and the remaining resource envelope is unchanged. The
intermediate-only boundary encoding is retained.

### Final autonomous-pass verification and profile

The final non-lineinfo edit build took 5.75 seconds. Its VM is byte-identical
to the timed candidate and contains 5,978 non-NOP instructions: 101 `LDC`, 189
`LDG`, 1,056 `IMAD`, 1,514 `IADD`, 316 `ISETP`, 427 `BRA`, 64 `SHFL`, 726
`VIMNMX`, and 411 `LOP3` sites. Ptxas reports 56 registers/thread, zero
stack/local memory, and 13,824 bytes static shared memory (14,848 bytes with
the driver reserve).

A fresh deterministic regeneration produced byte-identical artifact SHA-256
`10b5559c9d51cddf36e3208e41f446466ed3b72ae94bc5fcf93853f80cb9ec7e`.
All 65 artifact-generator/library tests pass. Final Compute Sanitizer reports
zero errors and log-8 checksum `0xbb2eb9da3c8c062b`. Two final locked log-24
medians were 13.639424 and 13.636433 ms around an interleaved original control
of 13.996912 ms, a 2.56% autonomous-pass improvement. The log-24 checksum is
`0x8820ab14cacc9ff7`, and the requested source-load floor remains
70,665,633,792 bytes.

The representative final VM-only report is
`target/profiling/autonomous_math_pass/final_retained_full.ncu-rep`. Relative
to the pre-autonomous full report:

- NCU duration falls from 14.153248 to 13.890464 ms;
- dynamic instructions fall from 19,271,647,232 to 19,026,870,272;
- shared FMA-heavy and ALU-heavy utilization move from 80.97% / 66.86% to
  80.78% / 66.11%, while issue activity moves from 76.98% to 77.04%;
- math-pipe-throttle cycles per issued instruction fall from 2.591 to 2.497;
- memory throughput is still only 41.30%, with 83.69% L1/TEX and 49.16% L2 hit
  rates; and
- instruction-cache hit rate remains 97.89%, while no-instruction stall is
  only 0.540 cycles per issued instruction.

The limiting resource is therefore still the shared FMA-heavy/ALU-lite math
pipe, not memory bandwidth, occupancy, or instruction delivery. The remaining
obvious field fusions are either outside `red_wide`'s overflow domain or were
measured as regressions in this ledger.

## LSB-contiguous window layout switch

On 2026-08-12, branch `rr/gpu_windowed_gkr` permanently replaced the MSB
split-half mapping `row | (corner << log_rows)` with the LSB-contiguous mapping
`(row << 3) | corner`. Warp geometry, equality factoring, the artifact and
descriptor ABI, and the final 27-cell order are unchanged.

Two locked log-8 runs reproduced checksum `0xcfeca7094d6c4b25` exactly. Two
locked log-24 runs reproduced checksum `0xae1bdb657d25b249` exactly, with
median timings of 14.581088 ms and 14.554560 ms. The pre-switch checksums
(`0xbb2eb9da3c8c062b` at log-8 and `0x8820ab14cacc9ff7` at log-24) and these
post-switch checksums are intentionally not value-comparable because the
deterministic direct and procedural inputs are functions of physical index.

A contemporaneous locked comparison used separate clean MSB and LSB binaries
with the same ignored lockfile, `CUDAARCHS=native`, toolchain, artifact,
allocation report, and resource envelope. Three interleaved log-24 pairs
measured MSB medians of 13.644608, 13.656879, and 13.657904 ms versus LSB
medians of 14.564049, 14.553392, and 14.650880 ms. The paired regressions were
6.7385%, 6.5646%, and 7.2703%; first-to-last drift was only 0.0974% for MSB and
0.5962% for LSB. Paired log-8 and log-20 medians regressed by 2.8915% and
6.6242%, respectively. Per-layout log-8 and log-24 checksums reproduced; the
log-20 checksums are single-run observations. LSB log-8 Compute Sanitizer
reported zero errors.

Matched log-24 NCU reports identify warp request splitting as the cause.
Global-load sectors per request rise from 4.678556616 to 31.980091248 and L1
LSU wavefront utilization from 32.008274% to 91.088309%. L2 read sectors rise
50.340489%, LG-throttle stalls per issue rise from 0.001706 to 0.574214, and
long-scoreboard stalls rise 64.622583%. DRAM read bytes are flat within
0.003288% because L1/L2 hit rates improve, so this is request splitting plus
L1-to-L2 traffic amplification, not DRAM overfetch. The 6.44% profiled net
slowdown occurs despite 2.092124% fewer dynamic instructions; the
memory-system cost is therefore at least as large as the net wall-time
regression, and plausibly larger given the removed ALU work.

### LSB packed-load register-envelope A/B

The follow-up compared two candidates derived from the same frozen scalar-LSB
source. Arm A packs BF and E4 direct-source pairs/cubes and changes only the VM
launch bound to three blocks; ptxas reports 71 registers, zero stack/local
memory, and 14,848 reported shared bytes. Its VM contains 47 64-bit, 26
128-bit, and 71 modifier-bearing 256-bit global-load sites. Arm B keeps E4
scalar at the original four-block/56-register envelope, but ptxas still emits
an 8-byte stack frame with one `STL.64` and one `LDL.LU.64`; it therefore failed
the static gate and was never executed.

The scalar control and Arm A passed literal same-layout checksums at all three
sizes: `0xcfeca7094d6c4b25` at log-8, `0x57f0a731d658ac7c` at log-20, and
`0xae1bdb657d25b249` at log-24. Arm A's log-8 Compute Sanitizer run reported
zero errors. The size-control medians were 0.073152 versus 0.072288 ms at
log-8 and 0.954112 versus 0.755584 ms at log-20 for scalar versus Arm A.

The locked log-24 session alternated scalar/Arm A over four rounds. Scalar
medians were 14.676080, 14.760368, 14.784800, and 14.807505 ms; Arm A medians
were 11.446096, 11.453552, 11.588720, and 11.541744 ms. The corresponding
paired deltas were -22.008493%, -22.403344%, -21.617337%, and -22.054769%.
Median-of-medians was 14.772584 versus 11.497648 ms (-22.169013%), with
0.895505% scalar and 0.835639% Arm A first-to-last drift. Relative to the
inferred MSB-equivalent denominator, Arm A recovers 23.662871 percentage points
(351.159330% of the original 6.7385-point regression) and clears the 13.93 ms
target.

Matched 17-section NCU profiles measured 15.060832 versus 11.898560 ms
(-20.996662%). Global-load requests fell from 474,021,888 to 170,459,136
(-64.039818%), sectors/request stayed essentially flat at 31.980091248 versus
31.944636678, L1 LSU wavefront utilization fell from 91.058949% to 51.133728%,
and LG-throttle stalls/issue fell from 0.577271 to 0.000006. L2 read sectors
fell 24.673706% while DRAM read bytes remained within +0.048067%. Dynamic
instructions fell 29.720003%. Theoretical/achieved occupancy fell from
75%/70.584599% to 56.25%/52.781090%; issue activity fell from 70.883795% to
63.255375%, FMA-heavy utilization from 76.994461% to 69.129629%, and
FMA-heavy active time from 11.596006 to 8.225430 ms. Long-scoreboard and wait
stalls rose, but math-pipe throttle and not-selected stalls fell enough that
the lower-occupancy arm remained decisively faster. Arm A is retained as a
target-success repair.

## LSB accumulator and geometry campaign

The 2026-08-12 follow-up kept the LSB-contiguous artifact/layout fixed and
measured only phase splitting, selector partitioning, accumulator placement,
and exact wide-arithmetic representations. Every functional-valid arm below
passed log-8 Compute Sanitizer with `ERROR SUMMARY: 0 errors` and reproduced
all three literal checksums: `0xcfeca7094d6c4b25` (log 8),
`0x57f0a731d658ac7c` (log 20), and `0xae1bdb657d25b249`
(log 24).

| Executed arm | VM resources (`REG/STACK/SHARED/LOCAL`) | Result |
| --- | --- | --- |
| `control` | `71/0/14848/0` | functional-valid |
| `relaxed-288x2` | `96/0/14848/0` | functional-valid |
| `phase-split-shared-288x3` | `72/0/14848/0` | functional-valid |
| `phase-split-shared-288x2` | `85/0/14848/0` | functional-valid |
| `phase-split-shared-96x9` | `71/0/5632/0` | functional-valid |
| `canonical-reg-288x2` | `91/0/0/0` | functional-valid |
| `canonical-reg-96x9` | `72/0/0/0` | functional-valid |
| `canonical-reg-96x8` | `80/0/0/0` | functional-valid |
| `bf-u96-reg-96x8` | `79/0/0/0` | functional-valid; selected |
| `bf-u96-reg-288x2` | `94/0/0/0` | functional-valid |
| `bf-u64-reg-288x2` | `96/0/0/0` | functional-valid |
| `bf-u64-reg-96x9` | `72/0/0/0` | functional-valid |
| `bf-u96-reg-96x6` | `93/0/0/0` | functional-valid |
| `full-u96-reg-96x6` | `96/0/0/0` | functional-valid |
| `prefix-u96-bf-u96-reg-96x8` | `78/0/0/0` | functional-valid; rejected by timing |

Static-only/rejected arms were never executed. `bf-u96-reg-96x9` spilled 24
stack bytes; full-u96 x8/x7 spilled 40 bytes; and the dual-u64 prefix rider
spilled 48 bytes. The static-valid provenance-only canonical x7/x6 and BF-u96
x7 arms were not run.

Balanced locked sessions used separate processes, immutable binary bindings,
10 warmups, 100 samples per log-24 position, and log-8/log-20 size controls.
Positive deltas mean the candidate is faster.

| Session comparison | Reference / candidate median (ms) | Paired delta | Classification |
| --- | ---: | ---: | --- |
| control → relaxed x2 | 11.503712 / 13.832080 | -20.438812% | material regression |
| control → phase-split shared x3 | 11.666776 / 11.040199 | +5.365195% | material win |
| control → partitioned shared x9 | 11.711728 / 14.086872 | -20.326719% | material regression |
| shared x2 → canonical-register x2 | 13.551344 / 12.967984 | +4.303640% | material win |
| control → canonical-register x2 | 11.483120 / 12.967984 | -12.932226% | material regression |
| shared x9 → canonical-register x9 | 13.968128 / 11.263216 | +19.290829% | material win |
| control → canonical-register x9 | 11.628464 / 11.263216 | +2.829636% | material win |
| canonical x2 → BF-u96 x2 | 12.940416 / 11.778112 | +9.028657% | material win |
| control → BF-u96 x2 | 11.605951 / 11.778112 | -1.390192% | material regression |
| canonical x2 → BF-u64 x2 | 12.977232 / 12.363696 | +4.835916% | material win |
| control → BF-u64 x2 | 11.669985 / 12.363696 | -5.987134% | material regression |
| canonical x8 → BF-u96 x8 | 11.286079 / 10.454048 | +7.394038% | material win |
| control → BF-u96 x8 | 11.635808 / 10.454048 | +9.863896% | material win |
| canonical x9 → BF-u64 x9 | 11.382896 / 10.881984 | +4.400567% | material win |
| control → BF-u64 x9 | 11.717520 / 10.881984 | +7.130656% | material win |
| BF-u96 x6 → full-u96 x6 (repeat) | 11.465088 / 11.542560 | -0.649903% | material regression |
| control → full-u96 x6 (repeat) | 11.631920 / 11.542560 | +0.793678% | unstable (`-,+,+`) |
| BF-u96 x8 → straight-u96 prefix | 10.384231 / 10.661345 | -2.596362% | material regression |

The original full-u96 session was kept separate: its exact-parent delta was
-0.581290% with unanimous negative signs, while the control-relative row was
classified `repeat`. The prescribed repeat above confirmed the parent-relative
regression; samples from the processes were not pooled.

Eleven mandatory full NCU profiles used each arm's immutable lineinfo binary,
log 24, one warmup, one profiled iteration, and base-unit CSV export. All
requested metrics except shared load/store request counts were supported. This
NCU/GPU exposes shared load/store instruction counts, wavefronts, and bank
conflicts but no shared-request counter; both request metrics are explicitly
reported as unsupported. Raw reports, imports, bindings, commands, and hashes are under
`target/profiling/ncu/20260812_windowed_lsb_accumulator_campaign/`.

| Matched NCU boundary | Duration delta | Dynamic instructions | Active blocks/SM | Issue activity | Shared load wavefronts | Duration × FMA-heavy |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| control → relaxed x2 | +19.475359% | -6.787203% | 3 → 2 | -22.405324% | -0.013886% | -4.960027% |
| shared x2 → canonical x2 | -4.549244% | -1.614205% | 2 → 2 | +2.727462% | 387,222,356 → 0 | +0.898579% |
| shared x9 → canonical x9 | -19.642922% | +2.031234% | 9 → 9 | +25.764015% | 387,325,982 → 0 | -2.246314% |
| canonical x8 → BF-u96 x8 | -7.334484% | -10.231989% | 8 → 8 | -2.947617% | 0 → 0 | -16.136486% |
| BF-u96 x6 → full-u96 x6 | +0.686191% | +4.267986% | 6 → 6 | +2.850507% | 0 → 0 | +1.539957% |
| BF-u96 x8 → straight-u96 prefix | +1.132550% | +1.284207% | 8 → 8 | -0.347102% | 0 → 0 | -1.930584% |

The mechanism evidence agrees with the balanced timing. Registerization removes
the private shared accumulator traffic without sacrificing matched residency;
the 96-thread form gains strongly from issue activity. BF-only u96 then removes
10.23% of dynamic instructions and 16.14% of duration-weighted FMA-heavy work
relative to its exact canonical x8 parent. Extending u96 through E4 adds 4.27%
dynamic instructions and 1.54% duration-weighted FMA-heavy work, consistent
with its repeatable regression. The within-2% prefix rider also adds 1.28%
instructions and 4.10% duration-weighted ALU-heavy work; its NCU duration rises
1.13% even though duration-weighted FMA-heavy work falls 1.93%. All eleven
reports show zero local and shared spill requests.

The selected arm is `bf-u96-reg-96x8`: 96 threads, three CTAs per row tile,
launch bound eight, 79 registers, and zero stack/local/shared memory. It is the
fastest repeatable complete arm and materially beats both its contemporaneous
retained control and its exact canonical parent. The E4 suffix stays canonical;
the optional inner-prefix riders were not retained.

## Compact-program decode campaign

The 2026-08-13 follow-up kept `bf-u96-reg-96x8` as the universal parent and
asked whether a denser, cheaper-to-decode instruction stream could remove a
meaningful part of the VM's control work. A reconciled per-address profile
assigned all `10,716,774,400` dynamic warp instructions exactly once. Program
fetch/decode/control owns 31.20%, source resolution/load owns 26.58%, arithmetic
owns 40.12%, and the explicit setup/equality/output residual is 2.11%. These
are ownership shares, not independently removable time estimates.

The permanent CPU-only census covers every layer of all 12 primary circuits:
57 discovered layers and 114 continuation/extension coordinates. It records
semantic structure, the compiler's actual greedy binding, and the benchmark's
six-slot/350-word encoding separately. Workload weights are preserved as four
profiles: raw corpus, current-branch base layer, development-branch recursion
proxy, and an explicitly unavailable current-branch recursion profile.

### Calibration and selector sharing

The instruction-inflation campaign preserved 102 attempts. The first 32 seed
points and two replacement-sink points optimized away; 32 shared-sink points
changed residency; two scratch-ABI attempts did not compile; and 32 final
zero-spill/eight-block points were fit-eligible. Eight fits split by atom/member,
serial/ILP, and requested instruction family yield an all-pair interval of
`0.494936` to `0.795720` ms per billion added warp instructions. The raw points,
exclusions, actual generated instruction currency, and fits remain in
`target/windowed-gkr-decode-compact-program/calibration-{attempts,fits}.tsv`.

Two selector-replay probes showed why straightforward fusion is unattractive.
Canonical-E4 replay used 163 registers and 12 active warps/SM, regressing
79.99%; full-u96 replay used 171 registers and eight active warps/SM,
regressing 115.05%. Full-u96 did execute 10.15% fewer instructions, but issue
activity collapsed. These probes replayed per-selector decode and therefore
do not reject a genuinely shared decoder; they quantify the compiler/state
cost of the obvious fully inlined implementations.

### Compact and scheduling arms

All executable arms passed zero-error log-8 memcheck, literal log-8/20/24
checksums, canonical-map checks, and zero-spill static gates.

| Exact-parent comparison | Program words | REG | Dynamic instruction delta | Paired timing | Result |
| --- | ---: | ---: | ---: | ---: | --- |
| parent → structural segmentation | 350 | 78 | +1.069 B | -7.868817% | regression |
| parent → direct specialized compact | 326 | 79 | +1.027 B | -6.290436% | regression |
| direct compact → same-window compact | 312 | 79 | +1.252 B | -8.170728% | regression |
| direct compact → direct permutation | 326 | 79 | 0 | -0.200880% repeat | unstable |
| same-window → same-window permutation | 311 | 79 | -0.001 B | -0.016772% repeat | unstable |

The direct format saves about 183.50 million uniform program-load instructions
versus structural segmentation, but its shifts, masks, and Boolean unpacking
still leave it 1.027 billion instructions above the retained parent. The
same-window decoder saves only 28.90 million plain `LDC` executions while
adding 1.252 billion instructions, led by `LOP3`, moves, shifts, integer MADs,
branches, and predicates. Occupancy stays at eight blocks/SM; the loss is
decode arithmetic and control, with additional L2 traffic, not a new register
or source-load bottleneck.

The permutation policy could legally reorder 71 product records inside lazy
segments, but the retained schedule was already nearly in that order. Only
eight records moved, as four adjacent swaps. Its neutral timing is therefore
evidence about this small realized perturbation only.

Null-versus-source-identical-control observations in the five compact sessions
ranged from -0.356938% to +0.220842% and had mixed signs. The much larger
structural/direct/same-window regressions are outside that band; the
permutation effects are not.

### Projection and interpretation

Projection joins use canonical record IDs and apply nine selectors to product
prefixes and four selectors to tails. Under raw, current-base, and development
proxy weights, the three fully projectable arms all add instructions and have
positive calibrated time intervals. For example, direct specialized compact
projects +3.424 B instructions / 2.017–2.725 ms for the raw profile,
+25.955 B / 15.289–20.653 ms for current base, and +31.305 B /
18.441–24.910 ms for the development proxy. These totals are comparative
weighted work units, not an end-to-end prover forecast. Permutation projections
remain partial because the corpus census knows where movement is legal but not
what movement a future scheduler would actually realize. Current-branch full
recursion remains unavailable.

The historical direct-coordinate experiment is an important counterexample:
removing 17 `LDC` sites and 16 static instructions made the materialized path
about 0.10 ms slower. Likewise, the earlier canonical-to-BF-u96 boundary shows
that a large coherent arithmetic change can win: -10.23% dynamic instructions,
-16.14% duration-weighted FMA work, and +7.394% timing versus the exact parent
at unchanged eight-block residency. Instruction count is useful currency only
within a matched mechanism and resource envelope.

No permanent compact GPU decoder is selected. The retained live kernel remains
`bf-u96-reg-96x8`; only the deterministic census, compact-codec, and host-oracle
tooling is kept. Plausible next experiments are a broader BF/E4-specialized
codec, direct source/address work, a truly shared non-replayed selector decoder,
combined mechanisms, or a separately controlled program-storage change.
Program storage is still inline uniform kernel-parameter data, large circuits
still need typed escape/capacity handling, and static-size/instruction-cache
results are pessimistic while 42 singleton BF atoms, untargeted tails, and all
seven E4 atoms remain on escape paths.

## R0 prototype-bank broad screen

The 2026-08-15 prototype bank moved from one-at-a-time experiments to a single
fat executable containing the complete legal R0 cross-product: eight by-value
program encodings, six legal inner/outer accumulator pairs, five selector
geometries, and ordinary or capacity-8/16/32 materialized-source policies where
defined. This is broad-search evidence, not a production selection or a
launch-bound/max-register tuning campaign.

All 245 symbols and 425 runtime configurations linked into one immutable
Blackwell executable. Correctness covered all 57 R0 coordinates at log 3 and
log 12. The production screen then exercised 13 typed real-domain coordinates,
giving 5,525 dispositions: 4,895 launchable exact-cell/checksum passes and 630
pre-launch shared-capacity facts. It retained 26,448 measured CUDA-event samples
(5–21 per launchable configuration after a two-warmup/three-measured-event pilot)
plus 9,790 retained-session warmups. Schema v1 reduced each pilot to its median;
its raw five events were not preserved. Post-review schema v2 fixes that evidence
gap and uses distinct pilot/retained candidate-pass rotations, but no v2 GPU run
exists; every timing number below remains exploratory v1 evidence from runner
SHA `9c8f615c...6472`.
The pairwise sanitizer cover exercised all 23 primitive factors with zero-error
memcheck, and every cooperative materialized cover row also passed racecheck.

Percentages below use `(candidate / controlled baseline - 1) × 100`; negative
is faster and positive is slower. Each paired row changes only the named factor.

| Controlled factor | Pairs | Median | p10 to p90 | Faster / slower |
| --- | ---: | ---: | ---: | ---: |
| compact R0 port vs current fixed slot, canonical ordinary | 65 | -1.732% | -17.143% to +3.012% | 41 / 24 |
| split-fixed slot vs current fixed slot, canonical ordinary | 65 | -10.645% | -20.190% to -0.143% | 59 / 6 |
| split-fixed direct vs current fixed slot, canonical ordinary | 65 | -6.316% | -28.536% to +2.998% | 46 / 19 |
| homogeneous direct vs current fixed slot, canonical ordinary | 65 | +5.101% | -10.619% to +16.527% | 19 / 46 |
| grouped direct vs current fixed slot, canonical ordinary | 65 | -3.352% | -20.486% to +4.202% | 46 / 19 |
| whole-BF u64 vs canonical outer accumulation | 1,276 | +23.679% | +11.494% to +79.865% | 16 / 1,260 |
| whole-BF u96 vs canonical outer accumulation | 1,276 | +30.108% | +4.803% to +87.645% | 15 / 1,261 |
| inner-u64 vs canonical inner, canonical outer | 334 | -0.987% | -6.076% to +10.424% | 202 / 132 |
| partitioned 96-thread vs wide 288-thread, ordinary sources | 390 | -32.417% | -42.608% to -1.713% | 357 / 33 |
| capacity-8 materialization vs ordinary, wide 288-thread | 390 | -33.467% | -57.2% to -1.3% | 354 / 36 |
| capacity-8 materialization vs ordinary, partitioned 96-thread | 390 | +105.773% | +56.1% to +153.7% | 0 / 390 |
| capacity-8 materialization vs ordinary, x2-major 96-thread | 390 | +0.732% | -28.3% to +30.8% | 190 / 200 |

The representation result is especially useful. Across these 13 coordinates,
compact R0 uses a median 0.886× the current logical program-plus-slot bytes and
requires no escape word anywhere in the full 57-coordinate R0 corpus, but its
controlled timing improvement is only 1.7%. Homogeneous direct is denser still
(median 0.767×) yet slower and statically spills in the five canonical ordinary
geometry symbols. Split-fixed slot uses the same median bytes as current fixed
slot but improves timing by 10.6%, showing that BF/E4 phase separation and
cheaper class dispatch matter more here than density alone. Direct source fields
are nearly neutral against their slot equivalents at the corpus aggregate, so
the extra slot lookup is not the dominant cost.

The accumulator and source-policy interactions are equally strong. Current
whole-BF u64/u96 prototypes raise the ordinary-symbol median register count from
100 to about 166/239 and lose accordingly; this diagnoses these implementations,
not the arithmetic idea in isolation. Inner-u64 is much cheaper and mildly
helpful overall, but the E4-heavy `unsigned_mul_div:2` coordinate reverses the
sign. For ordinary sources, partitioned 96-thread CTAs usually exploit their
greater block granularity. Once source values are cooperatively materialized,
the wide block instead amortizes one tile across all nine warps; partitioning
repeats the staging and is uniformly slower. Capacity 16/32 commonly restrict
residency to one block/SM and are correspondingly expensive.

The full normalized rows, static/program/tile joins, controlled global and
per-coordinate factor tables, and Pareto inputs are under
`target/windowed-gkr-r0-prototype-bank/report/`. They intentionally contain no
winner, score, threshold, rejection, or selected-implementation field. The next
search stage should retain multiple mechanisms—especially split-fixed slot,
ordinary partitioned geometry, and wide capacity-8 materialization—and explore
implementation variants before any launch-bound or max-register fine tuning.

## Sectioned three-warp launch-bound sweep

The 2026-08-17 sweep compiled all 225 sectioned schema-v2 candidates into one
executable and did not rebuild between candidates. For each of 15 corpus shape
masks it retained fixed wide-9 at three blocks and natural plus
7/8/9/10/12/16-block split-3 and low-register serial-3 variants. The heavy
three-warp variant was retained only in the compile canary. Static inspection
covered 226 symbols including the unchanged generic reference; correctness was
1,740/1,740 rows across the exact all-57 log-3/log-12 matrix and a 30-row
universal compatibility check.

The table below keeps geometry choice and launch-bound effect separate. “Best
bound” is descriptive within that geometry and coordinate, and its final
percentage is relative to the same geometry's natural sectioned arm. Generic
is the same-session generic interpreter, not the historical prototype.

| Coordinate | Generic ms | Wide-9 b3 ms | Split-3 natural ms | Split-3 best bound / ms / vs natural | Low-3 natural ms | Low-3 best bound / ms / vs natural |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| add_sub_lui_auipc_mop:0 | 17.095920 | 9.435376 | 10.019712 | b12 / 9.641776 / -3.772% | 13.723904 | b7 / 13.705472 / -0.134% |
| bigint_with_extended_control:0 | 57.066463 | 28.573153 | 34.679680 | b12 / 30.307728 / -12.607% | 41.975519 | b7 / 41.861025 / -0.273% |
| blake2_with_extended_control:0 | 17.343392 | 13.080432 | 15.275504 | natural / 15.275504 / 0.000% | 25.276257 | b7 / 25.247056 / -0.116% |
| inits_and_teardowns:3 | 1.234048 | 1.235424 | 1.341888 | b8 / 1.328576 / -0.992% | 1.282848 | b7 / 1.273152 / -0.756% |
| shift_binop:0 | 13.355488 | 12.230112 | 14.121392 | b12 / 10.066304 / -28.716% | 18.681776 | b7 / 18.681264 / -0.003% |

Aggregate launch-bound effects across those five coordinates are:

| Geometry / bound | Median vs same-geometry natural | Range | Actual register range | Shapes with stack bytes |
| --- | ---: | ---: | ---: | ---: |
| serial3_low natural | 0.000% | 0.000% to 0.000% | 61–80 | 0/5 |
| serial3_low b7 | -0.134% | -0.756% to -0.003% | 70–80 | 0/5 |
| serial3_low b8 | +0.006% | -0.755% to +0.090% | 70–80 | 0/5 |
| serial3_low b9 | +2.992% | +0.612% to +10.026% | 62–72 | 2/5 |
| serial3_low b10 | +3.728% | +0.076% to +21.128% | 61–64 | 2/5 |
| serial3_low b12 | +15.603% | +2.461% to +38.240% | 56 | 4/5 |
| serial3_low b16 | +91.209% | +42.317% to +259.233% | 40 | 5/5 |
| split3 natural | 0.000% | 0.000% to 0.000% | 61–84 | 0/5 |
| split3 b7 | -0.983% | -11.061% to +0.418% | 64–80 | 2/5 |
| split3 b8 | -0.992% | -11.081% to +1.349% | 64–80 | 2/5 |
| split3 b9 | -3.674% | -15.170% to +1.866% | 66–72 | 2/5 |
| split3 b10 | -0.005% | -5.612% to +3.278% | 61–64 | 2/5 |
| split3 b12 | -3.772% | -28.716% to +9.364% | 56 | 4/5 |
| split3 b16 | +79.074% | +30.906% to +213.744% | 40 | 5/5 |
| wide9 b3 | 0.000% | 0.000% to 0.000% | 64–72 | 2/5 |

Percentages use `(candidate / baseline - 1) × 100`, so negative means faster.
The complete 80-row table includes registers, theoretical register bucket,
stack/local/shared bytes, instruction count, SASS hash, exact natural identity,
and both primary and secondary denominators at
`target/windowed-gkr-r0-sectioned-launch-bounds/report/sectioned-screen-normalized.{jsonl,tsv}`.
The 15-row aggregate is
`target/windowed-gkr-r0-sectioned-launch-bounds/report/sectioned-bound-summary.{json,tsv}`.
These are coarse search data, not a production selection or a claim that one
geometry/bound should serve every circuit.
