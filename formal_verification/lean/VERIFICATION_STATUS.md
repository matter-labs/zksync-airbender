# Verification status

<!-- source-names: keccak_special5 -->

The retained circuit models and conditional execution composition have proof
coverage described below. The compiler scope is **22 captured production
compilations**: eleven families, with and without caches. This is a coverage
inventory, not a claim that all assurance gates passed at the current head.

## Proof coverage

| Area | Result |
| --- | --- |
| [Ordinary circuits](Airbender/Review/Circuits/README.md) | Arithmetic, branches/jumps, comparisons, shifts/bitwise and word/subword memory have reference soundness proofs. |
| [Whole execution](Airbender/Review/Trace/README.md) | Program-parametric pooled and unified source/trace execution reach terminal PC/cells; actual paths include jumps and repeated-PC loops. This generality is distinct from the compiler bridge below. |
| [Delegated workers](Airbender/Review/Trace/Workers/README.md) | Bigint, BLAKE2 and `keccak_special5` calls compose with the CPU under explicit contracts. Complete algorithms additionally require protocol coverage and valid memory gaps. |
| [Supported delegation use](Airbender/Review/Trace/UnifiedReduced/SupportedUseExecution.lean) | The new public path theorem derives bigint/hash worker contracts from public wrapper shapes and reference-prefix validity by induction over exact native prefixes. It covers bigint, G and extended round, with G separation retained. Public initialization, physical tracked-RAM/configuration/setup inputs and exact matching remain explicit. |
| [Provided Keccak wrapper](FINDINGS.md#f12--blessed-keccak-path-is-outside-current-proof-coverage) | Uncovered. The wrapper uses 361 calls to three split circuits; Lean covers the distinct 649-call special5 protocol. The inspected unified setup also omits the split CSRs. Split modeling and setup integration are deferred. |
| [Initialization and public inputs](Airbender/Review/Circuits/Initialization/README.md) | Native boundary products, public ROM/decoder bindings and both initialization profiles connect to execution. Exact logical matching remains explicit. |
| [GKR compiler preservation](Airbender/Review/Compiler/README.md) | All 22 captures have base-field arithmetic preservation. New logical execution APIs take physical arithmetic/active rows and exact matching of actual native encoding/leaf tuples. Field/mask/helper transport, operand coverage and setup-column bindings connect those tuples to source constraints, deriving helper bounds, authored membership and Clean/decoder validity without canonical framing. Supplied-program wrappers require decoder-table equality with the retained capture; explicit Airbender-platform wrappers are available. Older framed/fixed-program wrappers remain compatible. All 14 native row compositions and public wrappers compile; execution/public modules pass selected-module replay at a 32 MiB Lean thread stack. The selected 3279-module/10-test frontend passes freshness and artifact-hash checking without repairs. Full project/runtime, audit, replay and Linux assurance remain pending; sampled lookup/product enforcement remains outside the model. |

These are conditional soundness claims. Accepted cryptographic proof data implying
native gate validity and exact logical matching is outside the model. Captured
instances do not establish universal correctness of the Rust compiler. See the
[compiler premise table](Airbender/Review/Compiler/README.md#execution-premises),
[Review guide](Airbender/Review/README.md) and [trust boundaries](TRUST_AND_REVIEW.md).

The [ValidDelegationUse](Airbender/Review/Trace/UnifiedReduced/DelegationUse.lean)
contract excludes special5 calls and requires supported wrapper shapes, safe
entry and valid reference-prefix arguments. Its current covered registry contains
bigint, G and extended round; blessed split Keccak is outside that scope.
Existing special5 results remain conditional circuit/protocol
coverage; they do not prove execution of blessed Keccak programs. See
[F12](FINDINGS.md#f12--blessed-keccak-path-is-outside-current-proof-coverage).

## Remaining work

1. Preserve the public supported-use boundary for
   [F02 bigint commands](FINDINGS.md#f02--valid-bigint-operation-observations-do-not-establish-valid-calls),
   [F04 worker RAM ports](FINDINGS.md#f04--a-valid-copy-mode-does-not-bind-native-worker-rom-to-public-bytes)
   and [F11 hash witness contracts](FINDINGS.md#f11--hash-witness-contracts-remain-unenforced).
   These invalid invocations are excluded by the developers' supported-use
   contract. General native acceptance is not asserted to validate them. Keep
   G pointer separation and the blessed round masks' zero low limb explicit;
   the circuits are unchanged.
2. Complete whole-project validation of the physical-row logical lookup/helper
   connections and supplied-program wrappers after their focused build/replay and
   selected-frontend passes. Exact tuple matching retains natural multiplicities
   independent of physical counters; supplied programs must match the retained
   decoder tables. New setups and sampled-argument enforcement remain outside scope.
3. Complete a current-head full suite, environment dependency audit, independent
   kernel replay and negative controls. No complete current-head pass is recorded.
4. Validate advisory CI, Linux resource/process controls, replay stack and empty-cache
   reproduction on suitable hosts. Selectively required CI follows a complete Linux
   pass. CUDA/AVX-512 execution and a regenerated proof remain external checks.

Other implementation cases: [findings register](FINDINGS.md#linear-and-open-pr-review--15-october-2026).
Separately scoped work: [deferred milestones](FORMAL_VERIFICATION_PLAN.md#deferred-milestones).

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
modules directly. The round `controlAt` and special5 `scheduleControl`
definitions moved verbatim into definition-only protocol modules; their public
names and bodies and the remaining caller definitions are preserved. A guarded
normal build of both protocols, HashABI and both caller modules passes (1833
Lake jobs, 11.39 seconds, 521.11 MiB footprint and 2896.70 MiB resident), with no
surviving owned workers. Direct kernel replay also passes for all five changed
modules, covering 60 safe declarations at a 32 MiB Lean thread stack, with
compiled parts unchanged across replay. Imports were not replayed transitively
in this focused check. No production circuit, generator or layout changed.

Linux resource/process controls also pass in a disposable aarch64 container
(Linux 6.10.14-linuxkit, Python 3.12.11): 27 guard tests and 22 compilation-pool
policy/process tests. They exercise anonymous-memory limits, finite process
stack, pidfd/subreaper supervision, detached-descendant cleanup and aggregate
worker limits. These controls do not establish a Linux Lean build, full replay
or cold-cache reproduction. The full project frontend is being rerun after
its first attempt stopped at a competing-worker lock check; that interrupted
attempt is not recorded as a pass.

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

The full project frontend, executable/runtime checks, full environment audit,
complete independent dependency replay, transitive negative controls, Linux
controls and cold-run feasibility remain pending. The 25 native setup generator/
export freshness jobs and receipts remain a separate gate from the 67-file native
compiler capture check above.

The current targeted environment walk of
[the Keccak Iota mapping](Airbender/Review/Circuits/Keccak/Iota.lean)
confirmed constructor/type dependencies on Quot.sound and propext that the direct
report omitted. The [reviewed disposition](scripts/axiom_dispositions.json)
records that standard-axiom baseline correction. This targeted result does not
regenerate the full baseline or establish a complete current-head audit.

## Historical validation evidence

- Full ordinary suite at `5b17af422`: 1,842 modules and 176 concrete Tests passed.
- Before the hash circuit rollback, `f099bb549` passed 34 compiler targets and a
  direct 7,766-root axiom report. Direct reports are smoke tests; they do not replace
  the compiled-environment dependency audit or independent replay.
- After rollback, focused native-path/tests and 293 regenerated compiler modules,
  provenance checks and focused direct axiom reports were recorded. These do not
  establish a full current-head suite, native hash enforcement or full replay.

[Detailed evidence history](VERIFICATION_HISTORY.md) ·
[Compiler scope and historical evidence](GKR_COMPILER_VERIFICATION.md) ·
[Reproduce checks](README.md#reproduce)
