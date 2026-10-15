# Verification status

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
| [Full mixed execution](Airbender/Review/Trace/UnifiedReduced/FullExecution.lean) | Ordinary/TRIADD/XORROT and complete bigint/G/extended-round/Keccak CSR calls reach native terminal PC/cells under the existing public protocol profile and explicit F02/F03 contracts. |
| [Hash spans](Airbender/Review/Trace/UnifiedReduced/Segmentation.lean) | Existing preparation and selected references compose; issued hash workers partition into complete spans under the public protocol profile. |
| [Canonical terminal PC](Airbender/Review/Helpers/Context/VerifierBoundary/README.md) | Checked under the external canonical verifier boundary. |
| [Inactive padding](Airbender/Review/Helpers/Context/PaddingBoundary/README.md) | Architectural erasure and existing execution derived under the external contribution-mask boundary. |
| [Native mixed ROM](Airbender/Review/Trace/UnifiedReduced/NativeMixedROM.lean) | Public boot bytes and the explicit worker RAM contract compose into one ordinary/caller/worker memory history and terminal cells. F04 enforcement remains open. |

## Remaining work

Temporary assumptions narrow proofs; implementation findings remain open until
fixed or independently shown to be enforced. See the [case register](FINDINGS.md#linear-and-open-pr-review--15-october-2026).

| Claim | Blocker |
| --- | --- |
| Initialization/teardown local soundness | Retained artifacts have no equations/range queries; needs richer proof input. |
| Native setup table import | Shared ranges, bigint and G/round XOR tables, and G/Keccak controllers are imported and checked; other table definitions and program-dependent consumers are being migrated. |

AIH-334's EVM check is fixed and tested. AIH-336's tail/cache correction passes CPU
regressions; accelerated runtime/proof replay and other findings remain in the case register.

Evidence and detailed boundaries: [findings](FINDINGS.md).
Separately scoped work: [deferred milestones](FORMAL_VERIFICATION_PLAN.md#deferred-milestones).

## Validation

- Library, both executables and all 121 concrete test modules pass.
- Importer regressions pass.
- Axiom audit: 2,949 roots, 92 axiom-free; only `propext`, `Classical.choice` and `Quot.sound`.
- All 158 public Review theorem roots are audited; review/reference checks pass.
- No handwritten project diagnostics, `sorry` or project axioms.

[Reproduce the checks](README.md#reproduce).
