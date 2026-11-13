# Review guide

This directory states the verification claims and their meaning: circuit
relations, the shared context needed to interpret their witnesses, and complete
execution contracts. It exposes the selected references, observable mappings and
assumptions for human review; supporting proof calculations live in Proofs.

## Main checked results

| Result | Where to review it |
| --- | --- |
| Matching plus timestamp/initialization conditions forces complete memory histories and latest-write reads. | [Logical memory result](Helpers/Memory/README.md#logical-memory-result) |
| Public ROM bytes and `RV.decode` bind the instruction and metadata used by retirement. | [Decoder connections](Helpers/Decoder/README.md#checked-connections) |
| Accepted selected circuit rows have the stated reference effects under their visible interfaces. | [Circuit results](Circuits/README.md#checked-results) |
| Admitted ordinary instruction traces are a run of `RV.run` reaching the native terminal PC and tracked values; external-read extensions also prove consumption. | [Trace results](Trace/README.md#checked-results) |
| Native worker operations and complete selected hash spans reach their references on actual history values. | [Worker results](Trace/Workers/README.md#checked-results) |
| Joint native cuts, caller placement and prepared references use derived states/schedules. | [Unified results](Trace/UnifiedReduced/README.md#checked-results) |

Each link states the remaining premises and scope. A memory-consistency result,
an operation effect and a whole-instruction retirement result are distinct claims.

Every claim is stated against our RV32 spec, [ISA/RV32.lean](ISA/RV32.lean) (`RV.step`, `RV.run`; state in
[State.lean](ISA/State.lean), custom operations and delegation calls in [Delegations.lean](ISA/Delegations.lean)).
Read it first: it is short and marks each difference from standard RV32IM with `-- Airbender:`. Its tie to the
official Sail model is the leaf [ISA/Sail](ISA/Sail/Theorems.lean), the only claims that mention Sail.

Choose one of the two routes below. Start with [Properties](Helpers/Properties.lean)
for the meaning of soundness, completeness and the observable circuit relation.
That module imports only [CleanCore](../CleanCore.lean), our transcription of the Clean definitions we use.

Soundness says every input/output transition admitted by the circuit relation,
for any witness, is allowed by the selected reference. Completeness asks for a
witness for every allowed transition; the current project does not prove completeness.

## Review one circuit

Start in [Circuits](Circuits/README.md) and select a family. Its guide identifies
the claim, reference, artifact, named mappings and required helpers.

Read the model's satisfaction predicate and observable mapping separately from
its interface assumptions. Check what is public, what is logically matched, and
what is derived. Follow the bounds, actual reads and decoder selectors derived
from accepted constraints and initialized history; keep any local calculation
interface conditions visible.

Use the [helper guide](Helpers/README.md) to follow only the relevant topics.
A per-circuit claim can require shared history without requiring a whole-run
execution contract. Worker-local effects and complete worker protocols have
different scopes; the family guide points to the appropriate claim.

## Review whole-trace execution

Start in [Trace](Trace/README.md). Select the composed claim, then follow its
execution relation, public boundary and composition-specific contracts.
Check that the conclusion reaches the native terminal PC and tracked cells from
one public initial `RV.State`. Keep caller limitations explicit.

## Scope and evidence

Claims concern the imported richer no-cache constraints, using Clean's semantics
(through CleanCore) and our RV32 spec. Field, public state/program/domain, modeled
tables and logical matching are genuine conditions. Their applicability needs human review.

Trust base of the spec: this directory (`Human.*`) and CleanCore, our transcription of Clean, import Lean and
Mathlib (including Batteries) only, apart from the Sail leaf below. The one file that imports Clean is the leaf
[CleanCore/Equivalence.lean](../CleanCore/Equivalence.lean), which proves each CleanCore definition equal to Clean's;
nothing here imports it. Clean, and with it its native_decide prime instances in Clean's Utils/Primes.lean, is therefore
not in the spec's import closure (nor in that of the proofs in `proven/`; only the audit file `test/Checks/Axioms.lean` imports it).
The Sail model (generated SailRV32 and lean-sail) is imported only by `ISA/Sail/*` and
[Helpers/Core/Configuration.lean](Helpers/Core/Configuration.lean).

[Verification status](../../../docs/VERIFICATION_STATUS.md) records checked coverage and
counterexamples. [Trust boundaries](../../../docs/TRUST_AND_REVIEW.md) records import,
generation, table and cryptographic correspondence that is not proved.
[Reproduction](../../../README.md#reproduce) gives the build, regression and audit gates.
Supporting calculations remain in Proofs; importer fidelity is a separate review.
