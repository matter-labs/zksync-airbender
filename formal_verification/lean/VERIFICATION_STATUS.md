# Verification status

Native upstream baseline: `av_gkr_compiler` at `451884662`. The ordinary
source/runtime suite passes all 1,742 modules and 176 concrete Tests. Fresh direct
reports cover 4,425 audit roots (158 axiom-free), preserving all 4,379 earlier
reports. Declaration-origin auditing, transitive assurance controls and independent
kernel replay are separate required gates; direct reports alone do not certify them.

**Checked** means kernel-checked soundness of the imported richer no-cache
constraints under the published Review contracts. See [trust boundaries](TRUST_AND_REVIEW.md)
and the [fixed scope](FORMAL_VERIFICATION_PLAN.md).

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
| [Actual-path full execution](Airbender/Review/Trace/UnifiedReduced/PathExecution.lean) | Branches, JAL/JALR and repeated-PC loops compose with complete calls from all four worker families; native terminal PC/cells, public occurrence preparation, retirement profile and F02 remain explicit. |
| [Complete actual-path spans](Airbender/Review/Trace/UnifiedReduced/PathSpanExecution.lean) | Full native worker partition/count and complete algorithms share one derived history; each span uses readonly gaps or computed disjoint stores. Other ordinary writes retain whole-execution semantics. |
| [Hash spans](Airbender/Review/Trace/UnifiedReduced/Segmentation.lean) | Existing preparation and selected references compose; issued hash workers partition into complete spans under the public protocol profile. |
| [Canonical terminal PC](Airbender/Review/Helpers/Context/VerifierBoundary/README.md) | Checked under the external canonical verifier boundary. |
| [Inactive padding](Airbender/Review/Helpers/Context/PaddingBoundary/README.md) | Architectural erasure and existing execution derived under the external contribution-mask boundary. |
| [Initialization/teardown](Airbender/Review/Circuits/Initialization/README.md) | Actual standalone/inline GKR products, computed RAM boundary tokens and pooled/unified execution adapters; native zero seed and domain properties derived. |
| [Native mixed ROM](Airbender/Review/Trace/UnifiedReduced/NativeMixedROM.lean) | Public boot bytes and the explicit worker RAM contract compose into one ordinary/caller/worker memory history and terminal cells. F04 enforcement remains open. |

## Remaining work

Implementation findings and external validation are tracked in the
[case register](FINDINGS.md#linear-and-open-pr-review--15-october-2026).
General branch/jump/loop composition and complete span algorithms now pass focused
kernel checks in the current working tree. The Airbender device configuration,
memory bridges and both actual initialization profiles also pass, including the
disputed RAM regions. The accepted native COPY regression also passes: branches,
JAL/JALR and a repeated-PC loop contain two complete calls in one derived history
and realize the terminal PC/cells. Both standalone and inline physical/native
platform applications pass, as do the old-claim/profile compatibility regressions.
The four BabyBear entrypoint types match their original exported types exactly.
The accepted native [G-loop regression](Tests/PathGLoop.lean),
`Tests.PathGLoop.complete_regression`, also passes focused kernel checks. All
three variants retain their actual full executions and terminal PC 160/cells;
55 calls revisit the loop PCs and the last call uses index 55/controller 183.
The baseline and scratch SW7 variants group the complete 56-call G protocol.
The protected-message SW7 variant instead refutes its actual endpoint
[`WordMapping`](Airbender/Review/Trace/Workers/Blake2G/WorkVector.lean) and [`PathSpanAlgorithmAt`](Airbender/Review/Trace/UnifiedReduced/Paths/SpanProjection.lean), while retaining its full execution.
These applications must also pass the separate declaration-origin audit,
transitive controls and full independent kernel replay over the complete inventory.
Standard boot-ROM-data copying is outside the checked scope.

Temporary assumptions do not close implementation bugs. Separately scoped work:
[deferred milestones](FORMAL_VERIFICATION_PLAN.md#deferred-milestones).

## Validation

The ordinary suite validates current source and artifact freshness through normal
Lake dependency tracking, including all concrete Tests and both executables.
[Native provenance](artifacts/setup/README.md) was verified and committed as
e11139827: all twelve production generators ran with CI absent, all thirteen
fresh exports match complete retained JSON, and execution receipts plus 546 actual
dependency inputs pass. The [eight evidence files](artifacts/setup/native-evidence.json)
are separately pinned. Remote CI, Linux process controls and an empty-cache cold
bootstrap require their own execution on a suitable host.

- All 1,742 source modules, the library, both executables and all 176 concrete Tests pass.
- Importer layout and setup dispatch pass for twelve layouts and thirteen setups.
- Direct axiom reports: 4,425 roots, 158 axiom-free; only `propext`, `Classical.choice` and `Quot.sound`.
- All 178 public Review theorem registrations and contextual reference checks pass, including nine build-snapshot tampering controls.
- Complete assurance additionally requires the compiled declaration-origin audit and separate full-dependency kernel replay with direct/transitive negative controls.
- No handwritten project diagnostics, `sorry` or project axioms.

[Reproduce the checks](README.md#reproduce).
