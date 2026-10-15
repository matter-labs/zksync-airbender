# Verification status

**Checked** means kernel-checked soundness of the imported richer no-cache
constraints under the published Review contracts. See [trust boundaries](TRUST_AND_REVIEW.md)
and the [fixed scope](FORMAL_VERIFICATION_PLAN.md).

## Checked coverage

| Circuit | Coverage |
| --- | --- |
| [ADD/SUB](Airbender/Review/Circuits/AddSub/Theorems.lean) | ADD/ADDI/SUB/LUI/AUIPC; local ADDMOD/SUBMOD/MULMOD/FMAMOD. |
| [Jump/branch/SLT](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean) | JAL/JALR, all six branches and four comparisons. |
| [Unsigned mul/div](Airbender/Review/Circuits/MulDiv/Theorems.lean) | MUL/MULHU/DIVU/REMU, including zero divisors. |
| [Shift/binop](Airbender/Review/Circuits/ShiftBinop/Theorems.lean) | Standard register/immediate bitwise and shift operations; REV8. |
| [Word memory](Airbender/Review/Circuits/WordMemory/Theorems.lean) | RAM/ROM LW and RAM SW. |
| [Subword memory](Airbender/Review/Circuits/SubwordMemory/Theorems.lean) | RAM/ROM LB/LBU/LH/LHU and RAM SB/SH. |
| [Unified reduced machine](Airbender/Review/Trace/UnifiedReduced/Theorems.lean) | Standard instructions, TRIADD and all XORROT modes; original Sail retirement and terminal PC/cells. |
| [Bigint](Airbender/Review/Trace/Workers/Bigint/Theorems.lean) | All seven selected operations, carry/overflow and actual native port observations. |
| [BLAKE2 G](Airbender/Review/Trace/Workers/Blake2G/Theorems.lean) | Full G update and complete 56/80-call work-vector folds. |
| [BLAKE2 extended control](Airbender/Review/Trace/Workers/Blake2Round/Theorems.lean) | Complete seven-/ten-round reference compression in actual RAM. |
| [Keccak special5](Airbender/Review/Trace/Workers/Keccak/Theorems.lean) | All seven modes and the complete 649-call reference permutation in actual RAM. |

| Integration | Coverage |
| --- | --- |
| [Pooled execution](Airbender/Review/Trace/Soundness.lean) | Initialized history derives reads, bounds and decoding; six-family Sail execution realizes terminal PC/cells. |
| [Mixed cycles](Airbender/Review/Trace/UnifiedReduced/MixedCycles.lean) | Ordinary/custom retirement, caller observations and every worker share one initialized history and raw PC/clock path. |
| [Hash spans](Airbender/Review/Trace/UnifiedReduced/Segmentation.lean) | Existing preparation and selected references compose; issued hash workers partition into complete spans under the public protocol profile. |
| [Canonical terminal PC](Airbender/Review/Helpers/Context/VerifierBoundary/README.md) | Checked under the external canonical verifier boundary. |
| [Inactive padding](Airbender/Review/Helpers/Context/PaddingBoundary/README.md) | Architectural erasure and existing execution derived under the external contribution-mask boundary. |

## Open claims

These require external inputs or a scope decision.

| Claim | Blocker |
| --- | --- |
| Full custom-CSR execution of mixed callers | Accepted bigint controls 0/65537 violate the pinned ABI; active zero-clock workers can have effects without callers. Needs justified call-validity/participation binding. |
| Native worker ROM composition | Native zero ROM shadows lack a binding to public bytes or the RAM-only custom ABI. |
| Initialization/teardown local soundness | Retained artifacts have no equations/range queries; needs richer proof input. |

Evidence and detailed boundaries: [findings](FINDINGS.md).
Separately scoped work: [deferred milestones](FORMAL_VERIFICATION_PLAN.md#deferred-milestones).

## Validation

- Library, both executables and all 117 concrete test modules pass.
- 143 importer guards pass.
- Axiom audit: 2,548 roots, 73 axiom-free; only `propext`, `Classical.choice` and `Quot.sound`.
- All 136 public Review theorem roots are audited; review/reference checks pass.
- No handwritten project diagnostics, `sorry` or project axioms.

[Reproduce the checks](README.md#reproduce).
