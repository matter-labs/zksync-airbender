# Findings and unresolved bindings

This register concerns native v2 dev revision
67ee094449abaebc77e58435f130ce6ea27721e5, pinned in
[provenance](artifacts/provenance.json). It uses the finding-status standard from
FINDINGS.md in the pinned v3 source revision
805909325323812df4b7479288b9058d1d2671f5. Proof progress belongs in
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
