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
All 22 production configurations (eleven families, both cache modes) have checked
source-arithmetic preservation, graph wiring, consumer field roles, cache
semantics and source lookup-field identities. Both directions of the complete
base-field arithmetic relation are checked, covering every native arithmetic
gate, scalar cache and scalar materializer. Forward extension currently requires
the independently source-derived clock/borrow assertions. An additional checked
stage derives these assertions from the original bounded integer clock contract
and canonical fresh borrows, then constructs the entire extension-field graph.
It preserves original inputs and all other coordinates outside the borrow set.

All 4,436 consumed authored lookup fields agree with 836 original requests.
Another 474 timestamp/alignment query occurrences agree with independently
source-derived helpers. All 60 native lookup output pairs reduce to source query
lists plus their actual setup contributions. Table geometry and all 60 consumed
setup operands are checked; the 38 authored generic/range-16 query reductions
also compose with an explicit source table-row/multiplicity interpretation.
All literal setup columns are now imported and bound to both cache modes.
Actual finite multiplicity coordinates and external setup addresses are checked,
and canonical witness construction preserves every authored query field/mask.

All 48 RAM/initialization product output scalars reduce to the independent source
executor/delegation/initialization tuples, preserving exactly 476 occurrences,
initialization direction and the source execution mask. Source variables,
history/setup inputs and borrow witnesses have separate domains with checked
native projections. Borrows are distinct and avoid original/history cells.

Generic helper proofs derive strict integer clock order and alignment, construct
valid subtraction borrows and range bounds, and derive added executor assertions
from integer clock advance by four. These facts now compose with every native
arithmetic assertion and complete graph construction in all 22 configurations.
An additional checked stage constructs inactive histories and proves membership
of all 474 actual helper query occurrences from explicit source primitive/history
contracts in every configuration. Active histories and original coordinates are
preserved; inactive history cells may be reset to zero, preserving original
arithmetic and masked effects. Padding clocks must be positive, as in the native
executor convention starting at 4. The same graph witnesses now carry the actual
materialized lookup setup and chosen counters. Current
production source inputs have no relative timestamp groups; unsupported grouped
profiles are rejected.

The complete native base-field relation now also implies all 2,070 arithmetic
assertions in the retained post-compiler Clean models, in both cache modes.
Their exact logical placements and arithmetic inventories are checked, including
the models' full clock constraints. The resulting constraint theorems retain
explicit primitive lookup-membership premises; deriving those premises and the
final execution composition remains open.

All 22 configurations now construct one lookup multiplicity vector before any
extension ring/challenges are chosen. Original arithmetic/Booleans, source clock
and ordering/alignment contracts, and enabled authored table membership produce
complete native graph witnesses for every row. All actual native lookup output
groups have zero aggregate rational-pair numerators, including at zero
denominators. Helper memberships are derived from source primitive conditions.
All source RAM/initialization fields are now framed through the canonical
history/borrow/counter choices in all 22 configurations. The same complete
native witnesses preserve all 48 actual memory product ports and their full
trace products against the raw source memory view, including external cells.
Pooled logical-token/execution composition remains open.

The combined compiler audit covers 4,887 roots using only standard Lean axioms.
The normal root build, ten materialized-counter controls and five memory-frame
controls pass.
Isolated source-preserving native lookup, memory-cache, timestamp-helper and
native arithmetic-borrow
mutations trigger normal Lake rebuilding and kernel rejection; restoration
passes. A prior mutation exposed ineffective deprecated dependency keys, now
replaced by `needs`. Actual artifact provenance, input freshness, direct axiom
reports and full independent kernel replay remain distinct checks.

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
