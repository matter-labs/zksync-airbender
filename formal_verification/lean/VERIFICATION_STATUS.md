# Verification status

The retained circuit models and conditional execution composition have proof
coverage described below. The compiler scope is **22 captured production
compilations**: eleven families, with and without caches. This is a coverage
inventory, not a claim that all assurance gates passed at the current head.

## Proof coverage

| Area | Result |
| --- | --- |
| [Ordinary circuits](Airbender/Review/Circuits/README.md) | Arithmetic, branches/jumps, comparisons, shifts/bitwise and word/subword memory have reference soundness proofs. |
| [Whole execution](Airbender/Review/Trace/README.md) | Program-parametric pooled and unified source/trace execution reach terminal PC/cells; actual paths include jumps and repeated-PC loops. This generality is distinct from the compiler bridge below. |
| [Delegated workers](Airbender/Review/Trace/Workers/README.md) | Bigint and BLAKE2/Keccak calls compose with the CPU under explicit contracts. Complete algorithms additionally require protocol coverage and valid memory gaps. |
| [Initialization and public inputs](Airbender/Review/Circuits/Initialization/README.md) | Native boundary products, public ROM/decoder bindings and both initialization profiles connect to execution. Exact logical matching remains explicit. |
| [GKR compiler preservation](Airbender/Review/Compiler/README.md) | All 22 captures have base-field arithmetic preservation. New logical execution APIs take physical arithmetic/active rows and exact matching of actual native encoding/leaf tuples. Field/mask/helper transport, operand coverage and setup-column bindings connect those tuples to source constraints, deriving helper bounds, authored membership and Clean/decoder validity without canonical framing. Supplied-program wrappers require decoder-table equality with the retained capture; explicit Airbender-platform wrappers are available. Older framed/fixed-program wrappers remain compatible. All 14 native row compositions and public wrappers compile; execution/public modules pass selected-module replay at a 32 MiB Lean thread stack. The selected 3279-module/10-test frontend passes freshness and artifact-hash checking without repairs. Full project/runtime, audit, replay and Linux assurance remain pending; sampled lookup/product enforcement remains outside the model. |

These are conditional soundness claims. Accepted cryptographic proof data implying
native gate validity and exact logical matching is outside the model. Captured
instances do not establish universal correctness of the Rust compiler. See the
[compiler premise table](Airbender/Review/Compiler/README.md#execution-premises),
[Review guide](Airbender/Review/README.md) and [trust boundaries](TRUST_AND_REVIEW.md).

## Remaining work

1. Implementation enforcement remains open for
   [F02 bigint commands](FINDINGS.md#f02--valid-bigint-operation-observations-do-not-establish-valid-calls),
   [F04 worker RAM ports](FINDINGS.md#f04--a-valid-copy-mode-does-not-bind-native-worker-rom-to-public-bytes)
   and [F11 hash witness contracts](FINDINGS.md#f11--hash-witness-contracts-remain-unenforced).
   Conditional assumptions document the missing enforcement; the circuits are
   unchanged. F11 also records VM bundle-entry differences and the stricter round
   low-limb model profile.
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
