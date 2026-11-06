# Findings and unresolved bindings

This register concerns native v2 dev revision
67ee094449abaebc77e58435f130ce6ea27721e5, pinned in
[provenance](artifacts/provenance.json). It uses the finding-status standard from
FINDINGS.md in the pinned v3 source revision
805909325323812df4b7479288b9058d1d2671f5, reviewed against the current PR #585
reference b29277dd895499574e317a994fd89243a72f06cb on 6 November. Native fixes
in its newer v3 base are not inherited by this unchanged v2 target. The reduced
importer limitation and its removal are coverage work, not a native defect.
Proof progress belongs in
[verification status](VERIFICATION_STATUS.md), not in the finding count.

## Assessment standard

- **Accepted-relation discrepancy:** a checked bad witness satisfies the exact
  stated native acceptance relation but violates the specified reference or
  binding. Identify that relation and every missing or excluded enforcement step.
- **Concrete source defect:** a specific incorrect implementation or missing
  validation check, with pinned source evidence and a reproducible case or a direct
  argument demonstrating the incorrect behavior. A full forged proof is not required to retain such a defect.
- **Unresolved binding:** a material enforcement or implementation correspondence
  needed by a broader claim remains unproved. Track it as open; neither a theorem
  premise nor calling it an intended interface establishes enforcement.
- **Profile difference:** an explicit, supported semantic/configuration choice.
  It is not automatically a defect. A missing validation check must not be
  reclassified as a profile merely because a conditional theorem assumes it away.
- **Derived or excluded case:** the relevant stronger accepted relation actually
  derives the property or rejects the proposed witness. Record exactly where;
  exclusion by a temporary assumption alone is not a fix.

A finding must record its pinned revision/path, expected property, evidence,
exact tested scope, broader-path disposition and remaining enforcement/fix work.
A fix is closed only after the affected source/path is changed and validated, or
existing enforcement is demonstrated. Proof completion and open PRs are not fixes.

## Backport issue-handling policy

The user explicitly requires unchanged production circuits. Do not fix circuit
or machine Rust code in this backport. For any newly confirmed v2 issue, record
its exact native evidence and broader-path disposition here, and expose any
necessary restriction as a narrow Review interface assumption. The assumption
must remain visible in the conditional theorem contract; it is not a fix, an
enforcement proof or a project axiom. The assessment standard above continues
to apply. No new assumption is needed merely because a connection is unfinished.

## Confirmed native-v2 defects

**None established by this backport so far.** This is an evidence status, not a
claim that v2 is defect-free or that unassessed verifier/protocol paths are safe.
The old register contained 71 coverage, boundary and regression notes; those are
preserved in the [historical coverage log](VERIFICATION_STATUS.md#historical-coverage-and-boundary-notes).
Their number is not a vulnerability or defect count.

## Checked scope boundaries

These assessed cases explain why the existing notes do not establish v2 defects.
The rejection scope is logical/native as stated; cryptographic enforcement is
still a separate open binding below.

| Case | Classification and checked evidence | Limit |
| --- | --- | --- |
| V3 F01 terminal-PC witness shape | **Excluded by native v2 constraints.** The negative-high variant passes the native polynomials but fails the actual outgoing-high scalar query; [regressions](Tests/JumpPC.lean) and [native bounds](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean) retain canonical negative-offset targets. | This retests that witness shape and the supported ordinary masks. It does not establish whole-machine terminal/contribution closure. |
| Stale readonly aliases | **Rejected by full logical memory matching.** Bad timestamps satisfy local equations but fail accepted matching: [arithmetic](Tests/InitializedHistory.lean), [control](Tests/ControlHistory.lean) and all six [immediate/x0 shift aliases](Tests/ShiftHistoryFixture.lean). | Local equations alone are a weaker relation. These are enforcement regressions, not accepted-trace counterexamples or a cryptographic enforcement proof. |
| Decoder-owned x0 flags and filler | **Excluded in the checked native profiles.** [Bad flags](Tests/InitializedHistory.lean), [word-memory flags](Tests/WordMemory.lean) and [actual decoder/sentinel checks](Tests/NativeDecoderRows.lean) are rejected by the corresponding decoder membership or native constraints. | Do not generalize this to arbitrary decoder-only commitments, setup consumers or unassessed filler domains. |
| Discarded v2 operations versus v3 F06 | **Different native behavior, with original Sail effects retained.** V2 keeps the original opcode/operands and masks the actual write; [SUB x0](Tests/X0History.lean) and [ordinary/x0 ROM loads](Tests/WordMemoryROMTransport.lean) preserve the original source/reference effects. | The v3 discarded-LW discrepancy is not inherited as a v2 finding. This does not waive actual reads or shadow participation. |
| PC rollover, sparse holes and loader padding | **Supported behavior or explicit construction scope.** [RV32 rollover](Tests/PC.lean), [sparse execution](Tests/SparseExecution.lean), and [loader padding](Airbender/Review/Helpers/Tables/WordROMPadding.lean) retain their actual v2 behavior. | Missing public Sail bytes remain read failures until explicit padding is constructed. This is not a demonstrated native loader defect. |
| Shift/binop compilation CSR table | **Configuration profile plus unresolved runtime binding.** [The imported artifact](Airbender/Review/Circuits/ShiftBinop/Artifact.lean) retains the compilation-test CSR profile and all actual selector fields. | Empty delegation allow-list/nondeterminism fixture data does not establish production CSR setup or custom-call semantics; see B03. |

All remaining numerical table certificates, routing/results, initialized histories
and fetched-execution milestones are coverage evidence in the status document.
They are not independent findings merely because malformed test inputs reject.

## Checked reduced source/artifact divergence

Independent compilation of unchanged native v2 Rust produces 112 quadratic
rows, 142 variables and fourteen fixed regions, while the historical shipped
reduced JSON contains 114 quadratic rows, 141 variables and thirteen regions.
The source registry additionally materializes truncation ID 47. The
[regenerated artifact](Airbender/Review/Circuits/ReducedMachine/NativeArtifact.lean),
[public fixed fixture](Airbender/Review/Circuits/ReducedMachine/Tables/Native.lean)
and [reproduction controls](scripts/check_native_setup.py) retain exact evidence.
The tested configuration uses ROM second-word bits 6, decoder capacity 1048576
and trace log 23. The [native proving test](../../prover/src/tests/unrolled/reduced_machine.rs)
freshly compiles its configured circuit; this comparison does not exhibit an
accepted bad witness or establish that a verifier consumes the historical JSON.

This is a checked provenance divergence and a restriction on coverage transfer,
not a confirmed circuit defect. The historical artifact is preserved; current
machine work targets the separately regenerated constraints and complete pool.
No circuit fix or equivalence assumption is introduced. General compiler and
runtime configuration correspondence remain B01/B03 boundaries below.

The [native shift routing/filler/port and numerical contribution claims](Airbender/Review/Circuits/ReducedMachine/Theorems.lean)
add coverage under an explicit decoded packed mask. Both actual output columns
and all 4,194,304 numerical rows are checked; full native pool membership now
derives exact bounded outputs, and native equations connect them to the actual
selected contribution fields. Separate generic projections close the former
numerical proof allocation gap without raising limits. Resource failures and
proof completion are neither circuit defects nor fixes. Public decoding/mask,
canonical architectural source-key binding, initialized reads, complete word,
rd/x0, numerical PC and execution remain unfinished connections. No new
restriction or issue-handling assumption is introduced.
The [regenerated native initialized history](Airbender/Review/Trace/Families/ReducedMachine/History.lean)
now supplies logical memory consistency, newest reads and native clock/row
accounting from public initialization and accepted matching. Missing local source
ranges are an explicit native history design; establishing write preservation
and initialized range induction is still proof work. No accepted bad history or
source defect is exhibited by that unfinished connection. Word/execution and
physical/protocol boundaries remain separate.
The [selected public shift decoder connection](Airbender/Review/Trace/Families/ReducedMachine/Decoder.lean)
now derives actual native masks and rd/x0 fields, and native equations reject
sparse holes/padding. Native Rust decoder-export/fixed-ROM fidelity is still an
open correspondence boundary, not a confirmed defect. Other combined profiles,
write preservation and initialized execution remain unfinished proof work.
[Initialized selected-shift ranges and native source keys](Airbender/Review/Trace/Families/ReducedMachine/Sources.lean)
now close the missing low-read binding in that profile: proved masked-write
preservation feeds shared public-seed history induction. No source bound, write
rule or expected key is supplied publicly. Earlier large-coefficient arithmetic
attempts hit the allocation cap; symbolic proofs replace them at unchanged limits.
These resource failures and proof completion are neither native defects nor fixes.
Other combined profiles, original Sail execution and physical/protocol boundaries
remain open.
[Complete initialized native RV32 shift words](Airbender/Review/Trace/Families/ReducedMachine/Results.lean)
now close the selected profile's numerical candidate and actual masked-write
connection. This is proof progress, not a native defect or fix. Selected-profile
original Sail cell/GPR transport is now checked from actual mixed-port constraints and initialized
history. Original selected shift operands and Sail clauses are now checked at
the actual GPR after-states. [Actual native numerical PC+4/wrap](Airbender/Review/Trace/Families/ReducedMachine/PC.lean)
now follows from original public decoding and native carry equations. [Initialized
original normal/fetched selected-shift execution](Airbender/Review/Trace/Families/ReducedMachine/FetchedExecution.lean)
now composes to actual native terminal PC/cell reads under explicit public
interfaces. Other combined profiles, physical setup and full protocol behavior
remain open. No issue-handling assumption is introduced.
Confirmed native-v2 defects remain zero.

## Open bindings

These are unresolved proof/implementation bindings, explicitly separated
from confirmed implementation defects. Evidence of
a missing native check or an accepted discrepancy would promote a separate finding.
An additional Lean assumption would not close one.

| ID | Unresolved binding and evidence | What would close it |
| --- | --- | --- |
| B01 | **General Rust/JSON/compiler/setup correspondence.** [Provenance](artifacts/provenance.json), [strict parsing](Airbender/Import/Parse.lean), actual exported-row certificates and reproducible native fixtures provide specific checks. They do not prove arbitrary Rust preprocessing, JSON emission/parsing, query placement, reserved normalization rows or LDE correspondence. | Establish the relevant end-to-end implementation connection for the actual target/path, with complete supported and rejected-domain coverage; retain the existing specific certificates. |
| B02 | **Logical acceptance to physical verifier enforcement.** [Native row/state/memory matching](Airbender/Review/Helpers/Context/Model.lean) and Clean lookup membership are explicit theorem premises. Cryptographic permutation/lookup/statement enforcement and their physical argument correspondence are separately scoped. | Validate the actual verifier/statement/argument checks and connect them to these exact logical relations. A logical permutation premise is not that validation. |
| B03 | **Runtime CSR table configuration.** The [shift/binop fixture](Airbender/Review/Circuits/ShiftBinop/Artifact.lean) has nondeterminism enabled and an empty delegation CSR allow-list. Its exact compilation-test table is checked; correspondence to the separately configured production/runtime table is not established. | Inspect the actual runtime generator/allow-list and public setup binding before extending the ordinary claims to custom CSR semantics. Worker/caller proof milestones are tracked in the plan and the unassessed candidate list, not counted as new defects. |

## V3 findings awaiting v2 assessment

These are candidates, not confirmed v2 findings. Source proofs, fixes and temporary
contracts are not evidence that the same condition exists or is enforced on v2.

| Candidate | Native-v2 assessment still required |
| --- | --- |
| V3 F02 invalid bigint controls | Retest controls 0 and 65537 against the actual v2 worker/caller constraints and original ABI, including initialized matching and the relevant public instruction path. |
| V3 F03 unissued/zero-clock workers | Check actual v2 caller-to-worker and worker-to-caller accounting, zero-clock cancellation and possible state changes. Unique issued clocks alone do not establish the converse. |
| V3 F04 worker ROM pointers | Check actual v2 worker ROM/shadow reads, public bytes, allowed pointers and reference behavior. No RAM-only premise is adopted as a fix. |
| V3 F01/F05 beyond checked ordinary paths | Inspect actual v2 total-statement terminal encoding, contribution masking, inactive rows and initialization/teardown. The ordinary F01 retest above does not settle these other paths. |
| V3 reviewed source/protocol reports | Independently assess affected v2 paths for initialization-window validation, reachable decoder filler outside checked profiles, transcript freshness and recursive output binding before claiming a defect or a repair. |
