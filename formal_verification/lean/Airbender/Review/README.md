# Review guide

This directory states the verification claims and their meaning: circuit
relations, the shared context needed to interpret their witnesses, and complete
execution contracts. It exposes the selected references, observable mappings and
assumptions for human review; supporting proof calculations live in Proofs.

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

Claims concern the imported richer no-cache constraints, using Clean and pinned
original Sail standard semantics or the pinned project custom references.
Field/configuration, public state/program/domain, modeled tables and logical
matching are genuine conditions. Their applicability needs human review.

[Verification status](../../VERIFICATION_STATUS.md) records checked coverage and
counterexamples. [Trust boundaries](../../TRUST_AND_REVIEW.md) records import,
generation, table and cryptographic correspondence that is not proved.
[Reproduction](../../README.md#reproduce) gives the build, regression and audit gates.
Supporting calculations remain in Proofs; importer fidelity is a separate review.
