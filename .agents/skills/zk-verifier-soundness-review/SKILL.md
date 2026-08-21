---
name: zk-verifier-soundness-review
description: Recompute the concrete computational soundness budget of one named zero-knowledge verifier configuration, proof-system instance, or bounded protocol composition. Use for deep reviews of field and extension-field size, algebraic error, Sumcheck/GKR or AIR/DEEP errors, WHIR/FRI proximity and query security, batching, memory/lookup arguments, challenge bias, Fiat-Shamir retries, PoW grinding, hash security, and union bounds; do not use without exact parameters and a bounded configuration.
---

# Focused Verifier Soundness-Budget Review

Audit one concrete parameterized security claim. Do not infer “100-bit security”
from a feature name, table label, query count, or PoW exponent.

## Require one parameterized target

Resolve:

- one verifier/prover configuration and accepted statement;
- one proof-system instance and exact field/extension/hash/transcript;
- exact degrees, domain/rate/blowup, folds, queries, batches, layers, chunks,
  element bounds, security mode, PoW schedule, and deployed/generated artifact;
- the claimed security notion and adversary/work model.

If the target lacks concrete parameters, ask for the configuration or limit the
result to a symbolic budget with explicit variables. Do not combine every
supported security level or both GKR/WHIR and historical STARK/FRI in one run
unless the user explicitly requests that comparison.

Default to verifier-enforced parameters and bounds. Use prover configuration to
locate intended schedules and omissions, never as evidence that the verifier
enforces them. A prover-first review may validate parameter derivation but must
list every missing verifier-side bound.

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
6. Reconstruct the proximity pipeline: how far an invalid witness/claim is from
   the code after algebraic reduction, which list-decoding/proximity-gap theorem
   applies, and how the exact WHIR/FRI schedule converts that gap into rejection.
7. Model queries exactly: with/without replacement, duplicates, correlations,
   reused indices across batches/rounds, cap/path authentication, and terminal
   polynomial degree. Never substitute an informal `(1-δ)^q` term when the
   protocol theorem has additional round/list/compiler errors.
8. Model PoW as a cost on transcript retries. Verify nonce domain, threshold,
   seed prefix, state update, low-entropy consumed words, and the maximum number
   of affordable attempts. Do not automatically “add PoW bits.”
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
