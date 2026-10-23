---
name: zk-verifier-soundness-review
description: Recompute the concrete computational soundness budget of one named zero-knowledge verifier configuration, proof-system instance, or bounded protocol composition. Use for deep reviews of field and extension-field size, algebraic error, Sumcheck/GKR or AIR/DEEP errors, WHIR/FRI proximity and query security, batching, memory/lookup arguments, challenge bias, Fiat-Shamir retries, PoW grinding, hash security, and union bounds; do not use without exact parameters and a bounded configuration.
---

# Focused Verifier Soundness-Budget Review

Audit one concrete parameterized security claim. Do not infer “100-bit security”
from a feature name, table label, query count, or PoW exponent.

## Defensive correctness scope

This is an authorized, benign, read-only review of verifier correctness. Its
purpose is to identify implementation flaws so maintainers can patch them.
Limit deliverables to root cause, the precise verifier acceptance or rejection
consequence, remediation, and defensive regression tests. Use only minimal
symbolic counterexamples needed to prove a mismatch. Do not produce executable
demonstrations, operational reproduction procedures, deployment payloads,
network probes, credential/access steps, or live-system instructions.

## Require one parameterized target

Resolve:

- one verifier configuration and accepted statement;
- one proof-system instance and exact field/extension/hash/transcript;
- exact degrees, domain/rate/blowup, folds, queries, batches, layers, chunks,
  element bounds, security mode, PoW schedule, and deployed/generated artifact;
- the claimed security notion and adversary/work model.

If the target lacks concrete parameters, ask for the configuration or limit the
result to a symbolic budget with explicit variables. Do not combine every
supported security level or both GKR/WHIR and historical STARK/FRI in one run
unless the user explicitly requests that comparison.

Use verifier-enforced parameters and bounds. Consult prover configuration only
to locate intended schedules or provenance after extracting the verifier's
actual instance, never as evidence that the verifier enforces them. Without a
concrete verifier configuration and acceptance path, this skill does not produce
a soundness budget.

Treat every value admitted by a verifier-facing API, validation predicate,
generated constant domain, or supported build/generator/test path as reachable
for review even when no checked-in preset currently selects it. “Unused by the
current configuration” is not “unreachable.” Evaluate the full admitted domain,
especially endpoints and nearby security-level increases. Record current
deployment selection separately; a precise dormant activation condition makes
the defect latent rather than nonexistent.

### Verifier-first search discipline

Extract every credited parameter, bound, retry limit, challenge distribution,
and PoW check from the concrete verifier or authenticated deployment policy.
Do not begin with prover configuration tables and then assume parity. Open
producer configuration only to explain a verifier-selected value whose
provenance remains unclear. A field helper, prover schedule, or performance
model without a verifier-facing call path is implementation history, not a
verifier soundness finding.

## Soundness is compositional, not a checklist total

Consume local error terms from transcript, GKR/WHIR, STARK/FRI, and composition
reviews when available, but independently verify their hypotheses and units.
Separate:

- algebraic bad-challenge probability;
- proximity-gap establishment and low-degree-test error;
- query sampling and Merkle/hash binding;
- Fiat-Shamir/random-oracle transformation loss;
- prover retry/grinding work;
- multi-proof, multi-chunk, and multi-statement union bounds.

Do not simply add advertised “bits.” Convert terms to probabilities under one
defined experiment, compose conservatively, and only then convert back with
`-log2`.

Once a configuration and claimed security level are selected, no protocol term
that contributes to that claim may be declared outside scope. Bounded review may
delegate a protocol-specific derivation, but the final budget must incorporate
its result or remain explicitly incomplete. A serious neighboring finding does
not permit stopping before the selected error ledger is closed.

## Read the references

Always read:

- [security theory and accounting](references/security-theory.md)
- [grinding and current budget checklist](../zk-verifier-review/references/grinding-and-soundness-budget-expanded.md)

Read only the selected protocol reference:

- [Sumcheck/GKR](../zk-verifier-review/references/sumcheck-and-gkr-expanded.md)
- [WHIR PCS](../zk-verifier-review/references/pcs-whir-expanded.md)
- [AIR/DEEP-ALI/FRI](../zk-verifier-review/references/stark-deep-fri.md)
- [composition/global arguments](../zk-verifier-review/references/cross-circuit-and-aggregation-expanded.md)
- [normative paper map](../zk-verifier-review/references/normative-sources-expanded.md)

Fetch and cite the exact version of each primary paper whose theorem supplies a
term. Parameter folklore or a neighboring protocol is not a theorem citation.

## Workflow

1. Define the security experiment: false statement or false opening, adaptive
   or fixed statement, number of proofs/attempts, classical or quantum random
   oracle if claimed, and adversarial work budget.
2. Build the enforced-parameter table from verifier code, generated artifacts,
   setup/key, and deployment. Trace every constant to provenance and every
   runtime size to a verifier-side bound.
3. Write one row per failure event and cite the exact theorem/lemma and its
   hypotheses. Distinguish proven, conjectural, heuristic, and implementation-
   specific terms.
4. For every challenge, determine its actual support and distribution after
   hash-to-field mapping, truncation, reduction, skipped words, and forbidden
   values. Use the smallest field/support actually sampled.
5. Account for Sumcheck/zerocheck, gate/claim batching, permutation/memory,
   LogUp, quotient/OOD/DEEP, and terminal checks using actual degrees, numbers
   of variables/items, and dependencies.
   Derive circuit-dependent degrees and counts from the compiled artifact,
   layout, verifier-enforced trace/domain sizes, and active table/oracle
   inventories. Count exact per-row relations, table entries, tuple widths,
   batched columns, and ceiling-log effects when the repository exposes them;
   do not stop at a coarse field-size estimate or call the term a specification
   question merely because the count spans several circuit structures.
6. Reconstruct the proximity pipeline: how far an invalid witness/claim is from
   the code after algebraic reduction, which list-decoding/proximity-gap theorem
   applies, and how the exact WHIR/FRI schedule converts that gap into rejection.
7. Model queries exactly: with/without replacement, duplicates, correlations,
   reused indices across batches/rounds, cap/path authentication, and terminal
   polynomial degree. Never substitute an informal `(1-δ)^q` term when the
   protocol theorem has additional round/list/compiler errors.
8. Model PoW as a cost on transcript retries. Verify nonce domain, threshold,
   seed prefix, state update, low-entropy consumed words, and the maximum number
   of affordable attempts. For every random challenge, identify its bad event,
   single-shot bound, exact protected transcript prefix, circuit-derived loss,
   required grinding, enforced grinding, and every intervening prover message.
   A later PoW cannot protect an earlier draw. Do not automatically “add PoW
   bits.”
9. Add hash collision/preimage and transcript-transformation assumptions at the
   configured digest/round count. Keep them separate from information-theoretic
   IOP errors.
10. Compose probabilities with justified conditional/union arguments. Account
    for layers, batches, chunks, proof classes, recursion levels, accepted proofs
    over the deployment lifetime, and retry attempts.
11. Recompute every supported parameter table entry in scope and compare it to
    code. State conservative rounding direction and numerical precision.

## Required artifacts

### Enforced-parameter table

| Parameter | Claimed value | Verifier-enforced source | Runtime bound/provenance | Configuration reachability |
|---|---|---|---|---|

### Error ledger

| Event | Conditional error formula | Concrete value | Theorem/version | Hypotheses checked | Dependence/composition |
|---|---|---|---|---|---|

### Retry/grinding model

| Grinding step | Bound transcript prefix | Per-attempt work | Attempt budget | Per-attempt success | Total success bound |
|---|---|---|---|---|---|

### Challenge-to-grinding coverage

| Challenge or challenge family | Bad event and exact degree/count | Single-shot bound | Required grinding under the work model | Enforced nonce/check placement | Closed or unresolved |
|---|---|---|---|---|---|

### Final budget

Report information-theoretic error, computational hash assumptions, retry model,
total probability, conservative bits, claimed bits, and margin separately.

## Evidence gate

Confirm a security overstatement only when the claimed notion/level is real,
the deployed/reachable configuration is exact, the corrected theorem hypotheses
and arithmetic are shown, and the resulting conservative bound materially fails
the claim. Missing documentation or a theorem mismatch without a completed bound
is a specification question. Do not turn asymptotic concerns into concrete bits.

A security-level feature name alone is not a claim or a reachable instance.
For a non-deployed historical example, require an end-to-end build/test or
generation path that selects the level, constructs the proof, emits the matching
verifier/artifact, and consumes the defective parameter. Record build
reachability and deployment reachability separately. A later fix or PR statement
is evidence of intent, not proof that the old configuration was usable.

For grinding findings, identify the exact bad-challenge event and its single-shot
probability before discussing PoW. Then state the adversarial work/attempt model
under which the missing work is material. Never claim that `b` PoW bits
information-theoretically add `b` soundness bits, add PoW counts from distinct
phases, or infer a whole-system security level from a local retry-cost gap. If
all reachable configurations derive zero bits, adding the mechanism is hardening
or future support rather than a historical security failure.

If an exact parameter defect exists only in an unselected or unbuilt
configuration, preserve it as a separate **latent finding** with the precise
feature/artifact activation condition and a symbolic or concrete budget for
that configuration. Do not assign deployed severity or treat an advertised but
unenforced future target as a current security claim. Reachable parameter
failures and honest-proof failures are not latent.

Classify an exact arithmetic or mechanism defect as **implementation-only** when
no consuming acceptance path, honest-proof rejection, or concrete supported
security claim is established. Preserve it as latent only when the violated
invariant and a precise feature/artifact/caller activation condition are known;
a TODO or hypothetical future parameter without that evidence remains a lead.

## Deliverable

Return the exact configuration, theorem/version citations, parameter and error
tables, retry model, final budget, sensitivity to unresolved assumptions,
confirmed overstatements, and unreviewed protocol terms. Never imply that a
budget review established the implementation's algebraic correctness.

Keep the work authorized, source-local, read-only, and defensive. Do not perform
live grinding, generate malicious proofs, or provide operational attack steps.
