# Verification status

Native upstream baseline: `av_gkr_compiler` at `451884662`. The ordinary
source/runtime suite at proof-refactor commit `5b17af422` passes all 1,842 modules
and 176 concrete Tests (24 October 2026). Direct reports cover 4,425 audit roots
(158 axiom-free), preserving all 4,379 earlier reports. The separate compiled
declaration-origin audit also passes. Full independent kernel replay and the final
negative-control sweep remain incomplete; ordinary compilation and axiom reports
do not certify those gates.

**Checked** means kernel-checked soundness of the imported richer no-cache
constraints under the published Review contracts. See [trust boundaries](TRUST_AND_REVIEW.md)
and the [fixed scope](FORMAL_VERIFICATION_PLAN.md).

The [GKR compiler preservation effort](GKR_COMPILER_VERIFICATION.md) is active.
All 22 production source/compiler arithmetic, graph-wiring and lookup-field
instances (eleven families, both cache modes) pass kernel checking, with
corruption controls. All 22 consumer field-role and helper-address uniqueness
instances pass as well. Arithmetic witness extension covers the selected source
arithmetic slice. All 60 actual native lookup output pairs have checked
formula/port reduction proofs, with metadata count and one-setup-term checks.
All 4,436 consumed authored lookup fields also pass the source bridge; the 38
generic/range-16 groups reduce to the exact original query multiset plus their
actual native setup contribution. Source table interpretation, timestamp helpers,
RAM products and complete witness extension remain open. The native
input mutation control exposed ineffective deprecated Lake dependency keys;
these have been replaced by `needs`, and affected compiler targets passed ordinary
dependency-aware replay. All 140 roots in the arithmetic/wiring/lookup-field
checkpoint passed a direct axiom audit using only standard Lean axioms. The
expanded compiler inventory contains 658 audited roots, including the consumed
source-query reductions and their rejection controls.

Source table geometry and all 60 consumed setup operands are also checked. The
38 source-query reductions compose with an explicit source table-row and
multiplicity interpretation. Distinct multiplicity columns avoid every original
source variable. Binding this interpretation to materialized tables/witness
generation, and the timestamp/RAM/full-extension work, remain required. The
expanded compiler audit contains 1,010 roots using only standard Lean axioms.

## Checked coverage

| Circuit | Coverage |
| --- | --- |
| [ADD/SUB](Airbender/Review/Circuits/AddSub/Theorems.lean) | ADD/ADDI/SUB/LUI/AUIPC; [ADDMOD/SUBMOD/MULMOD/FMAMOD with pooled execution and external reads/hints](Airbender/Review/Trace/Modular/ExternalTheorems.lean). |
| [Jump/branch/SLT](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean) | JAL/JALR, all six branches and four comparisons. |
| [Unsigned mul/div](Airbender/Review/Circuits/MulDiv/Theorems.lean) | MUL/MULHU/DIVU/REMU, including zero divisors. |
| [Shift/binop](Airbender/Review/Circuits/ShiftBinop/Theorems.lean) | Standard register/immediate bitwise and shift operations; REV8. |
| [Word memory](Airbender/Review/Circuits/WordMemory/Theorems.lean) | RAM/ROM LW and RAM SW. |
| [Subword memory](Airbender/Review/Circuits/SubwordMemory/Theorems.lean) | RAM/ROM LB/LBU/LH/LHU and RAM SB/SH. |
| [Unified reduced machine](Airbender/Review/Trace/UnifiedReduced/Theorems.lean) | Standard instructions, TRIADD, all XORROT modes and [all four modular operations](Airbender/Review/Trace/UnifiedReduced/ModularExecution.lean); retirement and terminal PC/cells. |
| [Bigint](Airbender/Review/Trace/Workers/Bigint/Theorems.lean) | All seven selected operations, carry/overflow and actual native port observations. |
| [BLAKE2 G](Airbender/Review/Trace/Workers/Blake2G/Theorems.lean) | [Full-state reference micro-call sequences](Airbender/Review/Trace/Workers/Blake2G/ReferenceCalls.lean) and complete 56/80-call work-vector folds. |
| [BLAKE2 extended control](Airbender/Review/Trace/Workers/Blake2Round/Theorems.lean) | [Full-state reference micro-call sequences](Airbender/Review/Trace/Workers/Blake2Round/ReferenceCalls.lean) and complete seven-/ten-round compression in actual RAM. |
| [Keccak special5](Airbender/Review/Trace/Workers/Keccak/Theorems.lean) | [Full-state reference micro-call sequences](Airbender/Review/Trace/Workers/Keccak/ReferenceCalls.lean), all seven modes and the complete 649-call reference permutation in actual RAM. |

| Integration | Coverage |
| --- | --- |
| [Pooled execution](Airbender/Review/Trace/Soundness.lean) | Initialized history derives reads, bounds and decoding; six-family Sail execution realizes terminal PC/cells. |
| [Mixed cycles](Airbender/Review/Trace/UnifiedReduced/MixedCycles.lean) | Ordinary/custom retirement, [complete bigint calls under F02](Airbender/Review/Trace/UnifiedReduced/BigintCalls.lean), caller observations and every worker share one initialized history and raw PC/clock path. |
| [Full mixed execution](Airbender/Review/Trace/UnifiedReduced/FullExecution.lean) | Ordinary/TRIADD/XORROT and complete bigint/G/extended-round/Keccak CSR calls reach native terminal PC/cells with the supported straight-line ordinary registry and F02 command contract; tracked data RAM is at or above the ROM limit; native constraints derive worker participation. |
| [Native actual-path full execution](Airbender/Review/Trace/UnifiedReduced/NativePathExecution.lean) | Branches, JAL/JALR and repeated-PC loops compose with complete bigint, BLAKE2 G, extended-round and Keccak calls, realizing native terminal PC/cells. Native constraints derive supported hash controllers, round masks and G base separation without an occurrence plan. Initialization/matching, memory/configuration, retirement profile and F02 remain explicit. |
| [Complete actual-path spans](Airbender/Review/Trace/UnifiedReduced/PathSpanExecution.lean) | Under a per-trace occurrence plan and complete protocol coverage, full native worker partition/count and complete algorithms share one derived history; each span uses readonly gaps or computed disjoint stores. Other ordinary writes retain whole-execution semantics. |
| [Hash spans](Airbender/Review/Trace/UnifiedReduced/Segmentation.lean) | Existing preparation and selected references compose; issued hash workers partition into complete spans under the public protocol profile. |
| [Canonical terminal PC](Airbender/Review/Helpers/Context/VerifierBoundary/README.md) | Checked under the external canonical verifier boundary. |
| [Inactive padding](Airbender/Review/Helpers/Context/PaddingBoundary/README.md) | Architectural erasure and existing execution derived under the external contribution-mask boundary. |
| [Initialization/teardown](Airbender/Review/Circuits/Initialization/README.md) | Actual standalone/inline GKR products, computed RAM boundary tokens and pooled/unified execution adapters; native zero seed and domain properties derived. |
| [Native mixed ROM](Airbender/Review/Trace/UnifiedReduced/NativeMixedROM.lean) | Public boot bytes and the explicit worker RAM contract compose into one ordinary/caller/worker memory history and terminal cells. F04 enforcement remains open. |

### Checked composition regressions

General branch/jump/loop composition and complete span algorithms pass the ordinary
suite, together with the Airbender device configuration, memory bridges and both
actual initialization profiles, including the disputed RAM regions. The accepted
native [COPY regression](Tests/DynamicCopyLoop.lean) contains branches, JAL/JALR,
a repeated-PC loop and two complete calls in one derived history, realizing the
terminal PC/cells. Standalone and inline physical/native platform applications
and the old-claim/profile compatibility regressions also pass.
The four BabyBear entrypoint types match their original exported types exactly.
The accepted native [G-loop regression](Tests/PathGLoop.lean),
`Tests.PathGLoop.complete_regression`, also passes the ordinary suite. All
three variants retain their actual full executions and terminal PC 160/cells;
55 calls revisit the loop PCs and the last call uses index 55/controller 183.
The baseline and scratch SW7 variants group the complete 56-call G protocol.
The protected-message SW7 variant instead refutes its actual endpoint
[`WordMapping`](Airbender/Review/Trace/Workers/Blake2G/WorkVector.lean) and [`PathSpanAlgorithmAt`](Airbender/Review/Trace/UnifiedReduced/Paths/SpanProjection.lean), while retaining its full execution.
The stronger protected-store regression now excludes every admissible event order,
`PathSpansResult`, and `PathSpanGapCertificate` (focused kernel build).
The [consumed-message variant](Tests/PathGConsumedMessage.lean) moves the store
to message word 8, which the last G call reads. Its 228 CPU rows and 56 G rows
have native acceptance and an initialized execution history. Every admissible
history ends with state lane 3 equal to 119, while the independent 56-call
computation on the initial zero state/message yields zero. This refutes the
hash relation itself without using `messageUnchanged`.
Whole execution preserves ordinary writes even when they modify a protected block;
the grouped algorithm claims additionally require readonly gaps or computed stores
disjoint from that block. Standard boot-ROM-data copying is outside the checked scope.

The native actual-path entrypoint derives local successful-call validity for
arbitrary accepted traces, including controllers loaded from memory or computed
without a literal/AUIPC/ADDI preparation chain. The refreshed G, extended-round
and Keccak circuits enforce their supported local controls; G also enforces
separate state/message bases. [`Tests.NativeProtocolGap`](Tests/NativeProtocolGap.lean)
checks rejection of G control80 and equal G bases. The older
[`PathExecution`](Airbender/Review/Trace/UnifiedReduced/PathExecution.lean)
interface retains its per-trace occurrence plan for compatibility. Complete
algorithm grouping still needs protocol coverage and valid gaps; those properties
do not follow from arbitrary local successful calls.

## Remaining work

1. Complete independent kernel replay over the full dependency inventory. The
   latest extra sweep was stopped at the user's direction after the ordinary
   suite and declaration-origin audit passed; it is not a replay pass.
2. Complete the final negative-control sweep at the proof-refactor commit. Earlier
   direct and full transitive controls passed on the review candidate, but the
   latest sweep was not completed.
3. Validate remote CI, Linux process controls and empty-cache reproduction on
   suitable hosts. AIH-336 additionally retains CUDA/AVX-512 execution and a complete
   regenerated proof as external validation tasks.
4. Resolve implementation enforcement for [F02 bigint command validity](FINDINGS.md#f02--valid-bigint-operation-observations-do-not-establish-valid-calls)
   and [F04 worker RAM ports](FINDINGS.md#f04--a-valid-copy-mode-does-not-bind-native-worker-rom-to-public-bytes).
   Their conditional composition proofs are checked; general native acceptance
   has not been shown to enforce these contracts. Other implementation cases and
   target-specific validation remain in the
   [case register](FINDINGS.md#linear-and-open-pr-review--15-october-2026).

Temporary assumptions do not close implementation bugs. Separately scoped work:
[deferred milestones](FORMAL_VERIFICATION_PLAN.md#deferred-milestones).

## Validation

The ordinary-suite gate validates source and artifact freshness through normal
Lake dependency tracking, including all concrete Tests and both executables. The
full-suite, registration and declaration-origin counts below describe
`5b17af422` and predate the native successful-call refresh. That refresh has
its own focused validation record.
[Native provenance](artifacts/setup/README.md) was verified and committed as
e11139827: all twelve production generators ran with CI absent, all thirteen
fresh exports match complete retained JSON, and execution receipts plus 546 actual
dependency inputs pass. The [eight evidence files](artifacts/setup/native-evidence.json)
are separately pinned. Remote CI, Linux process controls and an empty-cache cold
bootstrap require their own execution on a suitable host.

- All 1,842 source modules, the library, both executables and all 176 concrete Tests pass at `5b17af422`.
- Native successful-call refresh: focused builds pass for the three family `NativeValidity` modules, `native_path_execution_soundness`, and eight affected concrete Tests: G-loop, consumed-message, native-control/base rejection, G memory, G, extended-round, round calls and Keccak. Direct reports for 16 selected roots use only `propext`, `Classical.choice` and `Quot.sound`. Review import layers and the new public theorem's audit registration also pass.
- Fresh no-cache G/round/Keccak exports and provenance checks pass (13 retained artifacts, 713 native source hashes).
- Importer layout and setup dispatch pass for twelve layouts and thirteen setups.
- Direct axiom reports: 4,425 roots, 158 axiom-free; only `propext`, `Classical.choice` and `Quot.sound`.
- All 178 public Review theorem registrations and contextual reference checks pass, including nine build-snapshot tampering controls.
- Compiled declaration-origin audit: 8,560 roots and 170,355 declarations pass, with no forbidden axioms, unsafe proof dependencies, missing baseline roots or undispositioned changes. The documented pre-existing constructor/type closure of `Airbender.Keccak.IotaMapping` reaches standard `Quot.sound`/`propext`; its direct report remains unchanged.
- Earlier direct/full-transitive assurance controls passed on the review candidate. Full independent kernel replay and the final negative-control sweep at `5b17af422` remain incomplete.
- The proof-only modularity refactor is committed and integrated. Scoped cached recomputation and edit-invalidation experiments passed; no whole-project cold-build or replay speedup is claimed.
- No handwritten project diagnostics, `sorry` or project axioms.

[Reproduce the checks](README.md#reproduce).
