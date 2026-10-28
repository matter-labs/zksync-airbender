# Verification checkpoints

These are historical results for the stated source snapshots and scopes.
[Verification status](VERIFICATION_STATUS.md) owns the current evidence inventory.

## Current focused validation

The supported-use public theorem, public library root and twelve new regression
theorems compile. The original bigint/control, ROM-shadow and special5
counterexample modules also compile unchanged. The final selected frontend
passes over 3403 modules, 14 concrete Tests modules and five retained Sail modules,
using one worker, with normal Lake no-build source freshness and recomputed
compiled-artifact hashes. No repair builds were needed. This is selected-scope
evidence, not a whole-project assurance snapshot. A prerequisite dependency
rebuild reached the 900-second cap; the later incremental scoped builds passed.
Cold-run feasibility remains unestablished.

Direct independent kernel replay also passes for all six new modules: 192 safe
declarations at a 32 MiB Lean thread stack. Imported modules were not transitively
replayed in that focused check. All 12399 established audit roots are retained,
with ten additional explicit roots. Complete environment auditing and transitive
replay remain separate pending gates.
Focused axiom smoke reports for the contract, bridge and regression roots contain
only propext, Classical.choice and Quot.sound; they do not replace that complete
environment audit.

The helper/trace layer check now passes. HashABI imports circuit-level protocol
modules directly. The round `Airbender.Blake2Round.controlAt` and special5 `Airbender.Keccak.scheduleControl`
definitions moved verbatim into definition-only protocol modules; their public
names and bodies and the remaining caller definitions are preserved. A guarded
normal build of both protocols, HashABI and both caller modules passes (1833
Lake jobs, 11.39 seconds, 521.11 MiB footprint and 2896.70 MiB resident), with no
surviving owned workers. Direct kernel replay also passes for all five changed
modules, covering 60 safe declarations at a 32 MiB Lean thread stack, with
compiled parts unchanged across replay. Imports were not replayed transitively
in this focused check. No production circuit, generator or layout changed.

Linux resource/process controls also pass in a disposable aarch64 container
(Linux 6.10.14-linuxkit, Python 3.12.11): 29 guard tests and 23 compilation-pool
policy/process tests. They exercise anonymous-memory limits, finite process
stack, pidfd/subreaper supervision, detached-descendant cleanup and aggregate
worker limits. These controls do not establish a Linux Lean build, full replay
or cold-cache reproduction.

The full frontend rebuilt the project and concrete Tests sources, then found
late imports in the [direct audit entrypoint](Airbender/Checks/Axioms.lean). All 908
imports now precede commands, preserving their order and every one of the 12409
explicit roots in its original order. The repaired entrypoint compiles (6844
Lake jobs, 19.78 seconds, 960.70 MiB footprint and 4416.84 MiB resident), with no
surviving owned workers. An earlier attempt also stopped at a competing-worker
lock check. Interrupted attempts are not successful assurance snapshots.

The later run completed source freshness for all 4862 modules (219 concrete Tests),
native dependency freshness, library/executable builds, direct axiom comparison,
importer runtime and source/evidence identity checks. Final review exposed two
stale mutation fixtures and a reserved local name in the generated Lean inventory.
The fixtures now forge consistent hash manifests to reach their intended absence
and path checks; production validation is unchanged. All nine snapshot mutation
controls pass. The repaired inventory passes 200 contextual guide references,
190 explicit public Review theorem roots, 1305 links and the layer check (61.25
seconds, 768.65 MiB footprint, 4238.23 MiB resident, no surviving owned workers).
Fifteen assurance policy tests pass.

The final complete source/runtime/review frontend passes at f0b059fe6412:
4862 modules, 219 concrete Tests, five retained Sail modules and native freshness
for 3509 runtime modules, both executables and the library. Normal Lake no-build
freshness, compiled-artifact hashes, direct axiom comparison, importer runtime
and all review checks pass. Its 23 guarded jobs total 260.14 seconds from the
normally built cache, with peak footprint 855.31 MiB, resident 4279.14 MiB and no
surviving owned workers. This is a complete frontend snapshot, not a completed
environment audit or independent transitive replay.

The subsequent Mac environment audit stopped at the unchanged resident cap:
5125.94 MiB against 5120 MiB, footprint 1193.53 MiB, after 125.97 seconds, with no
surviving owned workers. It issued no successful audit result. Remaining assurance
is being attempted in native aarch64 Linux using its documented charged-memory
accounting and the same limits. Cold cache bootstrap exposed a metadata query
counted as a second compiler: Mathlib's initializer invokes `lean --print-prefix`.
Linux now recognizes only that exact query; its memory and time remain charged,
and unknown invocations and two actual compilers still trigger the worker limit.
Linux native freshness now passes at ac90532c92b1: twelve executed generators,
thirteen complete exports, all receipts and 546 native dep-info inputs. The 25
guarded jobs total 242.97 seconds, with peak charged memory 1629.62 MiB and no
surviving owned workers. Both retained/fresh compiler validators and provenance
controls pass; all 67 native compiler export files reproduce byte for byte.
The CI comparison now checks the exact root-file inventory and every byte,
leaving the separate interpretation/lookup directories to their own validators.
Its actual-data check passes and missing, extra and changed export controls reject.
Environment auditing, transitive replay, negative controls and the complete cold
Linux frontend remain pending.

### Prior compiler-composition checkpoint

Native Rust compiler capture regeneration and both retained/fresh production
checks pass: all 67 files reproduce byte for byte. The measured guarded run took
27.06 seconds, with peak footprint 1341.22 MiB and resident memory 1353.02 MiB,
and left no surviving owned workers. This validates the native capture/provenance
step only. Separately, all 14 actual native logical-row compositions compile,
including payload/mask/helper transport, operand coverage and setup bindings.
Program execution, logical execution and the final public compiler theorem module
compile and pass direct selected-module kernel replay at a 32 MiB Lean thread
stack. The final public-wrapper build took 37.49 seconds, with peak footprint
586.75 MiB and resident memory 3093.56 MiB, and left no surviving owned workers.

An isolated fixture using the actual Lake target metadata passes all eight dirty
cases: two setup inputs across four setup-reading test modules. This checks Lake
dependency wiring using a lightweight fixture; it does not execute the actual
setup-test bodies. Separately, the three previously omitted GKR tests, four actual
setup tests, two new regressions and upstream platform compatibility compile and
belong to the completed selected frontend scope.

The final selected frontend passes over a 3279-module import closure containing
10 concrete Tests and five retained Sail modules, using one worker. Project-import
inventory, normal Lake no-build source-freshness queries and recomputed compiled
artifact hashes all pass without repair builds. The run took 96.51 seconds,
with peak footprint 538.71 MiB and resident memory 1585.52 MiB, and left no
surviving owned workers. Source and compiled manifests bind this selected scope;
no full assurance build snapshot was issued. The final upstream-compatibility
build also passes: 670.85 seconds, peak footprint 1589.04 MiB, raw resident memory
4110.22 MiB and no surviving owned workers.

The full environment audit, complete independent dependency replay, transitive
negative controls and cold-run feasibility remain pending. The completed Linux
25-job native setup generator/export freshness gate and the 67-file compiler
capture reproduction check are separate from those proof assurance gates.

The current targeted environment walk of
[the Keccak Iota mapping](Airbender/Review/Circuits/Keccak/Iota.lean)
confirmed constructor/type dependencies on Quot.sound and propext that the direct
report omitted. The [reviewed disposition](scripts/axiom_dispositions.json)
records that standard-axiom baseline correction. This targeted result does not
regenerate the full baseline or establish a complete current-head audit.

## Historical validation evidence

- Full ordinary suite at `5b17af422`: 1,842 modules and 176 concrete Tests passed.
- Before the hash circuit rollback, f099bb549 passed 34 compiler targets and a
  direct 7,766-root axiom report. Direct reports are smoke tests; they do not replace
  the compiled-environment dependency audit or independent replay.
- After rollback, focused native-path/tests and 293 regenerated compiler modules,
  provenance checks and focused direct axiom reports were recorded. These do not
  establish a full current-head suite, native hash enforcement or full replay.

[Detailed evidence history](VERIFICATION_HISTORY.md) ·
[Compiler scope and historical evidence](GKR_COMPILER_VERIFICATION.md) ·
[Reproduce checks](README.md#reproduce)
