# Review guide

This directory states the verification claims and their meaning: circuit
relations, the shared context needed to interpret their witnesses, and complete
execution contracts. It exposes the selected references, observable mappings and
assumptions for human review; supporting proof calculations live in Proofs.

## Main checked results

| Result | Where to review it |
| --- | --- |
| Captured GKR arithmetic preserves source obligations; new physical-row logical APIs compose to Sail execution under exact lookup matching, alongside framed compatibility wrappers. | [Compiler claims and boundaries](Compiler/README.md) |
| Matching plus timestamp/initialization conditions forces complete memory histories and latest-write reads. | [Logical memory result](Helpers/Memory/README.md#logical-memory-result) |
| Public bytes and original Sail decoding bind the instruction and metadata used by retirement. | [Decoder connections](Helpers/Decoder/README.md#checked-connections) |
| Accepted selected circuit rows have the stated reference effects under their visible interfaces. | [Circuit results](Circuits/README.md#checked-results) |
| Admitted ordinary instruction traces reach the native terminal PC and tracked values; external-read extensions also prove consumption. | [Trace results](Trace/README.md#checked-results) |
| Native worker operations and complete selected hash spans reach their references on actual history values. | [Worker results](Trace/Workers/README.md#checked-results) |
| Joint native cuts, caller placement and prepared references use derived states/schedules. | [Unified results](Trace/UnifiedReduced/README.md#checked-results) |

Each link states the remaining premises and scope. A memory-consistency result,
an operation effect and a whole-instruction retirement result are distinct claims.

Choose one of the two routes below. Start with [Properties](Helpers/Properties.lean)
for the meaning of soundness, completeness and the observable circuit relation.
That module imports only Clean.

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
one public initial state. Keep profile deviations and caller limitations explicit.

## Scope and evidence

Circuit/trace claims concern the imported richer no-cache constraints, using
Clean and pinned original Sail standard semantics or project custom references.
Compiler claims additionally cover base-field arithmetic preservation for 22
captured cached/uncached compilations and conditional executor composition. New
physical-row APIs derive membership/helper validity from exact tuple matching;
supplied-program wrappers require retained decoder-table compatibility. The
[compiler guide](Compiler/README.md#execution-premises) states those logical
boundaries. All 14 actual native row compositions and public wrappers compile;
execution/public modules pass selected-module replay at a 32 MiB Lean thread
stack. The selected 3279-module/10-test frontend passes freshness and compiled
artifact-hash checks without repairs. This supplies selected source/compiled
manifests, not a full assurance snapshot; full project/runtime, environment,
independent replay, transitive negative-control and Linux/cold-run checks remain
pending. See [current validation scope](../../VERIFICATION_STATUS.md#current-focused-validation).
Field/configuration, public state/program/domain, modeled tables and logical
matching are genuine conditions. Their applicability needs human review.

[Verification status](../../VERIFICATION_STATUS.md) records checked coverage and
counterexamples. [Trust boundaries](../../TRUST_AND_REVIEW.md) records import,
generation, table and cryptographic correspondence that is not proved.
[Reproduction](../../README.md#reproduce) gives the build, regression and audit gates.
Supporting calculations remain in Proofs; importer fidelity is a separate review.
