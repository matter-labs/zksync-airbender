---
name: zk-gkr-whir-verifier-review
description: Defensively audit the algebraic claim chain of one named Sumcheck, GKR, multilinear-polynomial, or WHIR verifier component, generated verifier slice, protocol phase, or immediate GKR-to-PCS handoff. Choose this when the primary question is layer, fold, batching, opening, or Merkle/PCS correctness; include the phase's local transcript dependencies and require a bounded entrypoint rather than auditing every GKR/WHIR path at once.
---

# Focused Sumcheck, GKR, and WHIR Verifier Review

Audit one concrete algebraic reduction deeply, including the transcript ordering
that makes its probabilistic checks sound. Protocol expertise and transcript
expertise are inseparable here.

## Require a bounded target and focus

Resolve one proof-system instance and choose one primary focus:

- one Sumcheck implementation or round family;
- one standard or dimension-reducing GKR layer family;
- one multi-output/final-claim batching step;
- one GKR-to-base-layer/PCS handoff;
- one WHIR commitment, OOD, folding, query, Merkle, or final round;
- one tightly coupled generated verifier path covering a small adjacent chain.

Fingerprint the entrypoint, circuit/configuration, field and extension, variable
order, transcript/hash, security mode, generator output, and caller. If no target
or focus is given, ask for them. Do not silently audit every circuit family,
every generated verifier, or both native and EVM instances.

Default to the verifier. Use the prover to recover honest message formats,
polynomial layout, and intended optimizations only after deriving verifier
behavior. For an explicitly prover-first review, state a provisional verifier
contract and defer acceptance findings.

## Mandatory local transcript contract

For every selected probabilistic check, reconstruct the local interactive rounds
and then the exact Fiat-Shamir schedule. Verify that each round polynomial,
commitment/cap, evaluation vector, next-layer claim, folding oracle, terminal
polynomial, nonce, and query-dependent opening is fixed before the challenge
whose theorem requires it. Do this even if a separate transcript skill ran.

Consume an existing transcript artifact only after checking its rows against the
selected source and protocol. Emit corrected or additional rows as part of this
review.

## Read the applicable references

- Sumcheck or GKR focus:
  [Sumcheck and GKR](../zk-verifier-review/references/sumcheck-and-gkr-expanded.md)
- WHIR or PCS focus:
  [WHIR PCS](../zk-verifier-review/references/pcs-whir-expanded.md)
- Any challenge-dependent focus:
  [Fiat-Shamir](../zk-verifier-review/references/fiat-shamir.md)
- Deep specification recovery:
  [normative sources](../zk-verifier-review/references/normative-sources-expanded.md)
- Matching Airbender target only:
  [architecture](../zk-verifier-review/references/airbender-verifier-architecture.md)
  and [snapshot profile](../zk-verifier-review/references/airbender-gkr-v1-profile.md)

Do not load both GKR and WHIR references unless the selected target includes
their seam.

## Workflow

1. Recover the exact theorem/interactive protocol for the selected optimization:
   claimed polynomial, variable count/order, individual degree, initial claim,
   prover message, verifier identity, sampled challenge, and terminal check.
2. Build the claim chain. Label every claim as statement/setup-derived,
   commitment-authenticated, locally recomputed, previous-round-derived, or
   prover-supplied. Mutual consistency is not provenance.
3. For Sumcheck, check message length/degree, the Boolean-hypercube sum identity,
   absorption before sampling, evaluation/update, variable order, round count,
   and the final evaluation against the actual gate relation.
4. For GKR, check layer wiring, `eq` gating and its added degree, gate semantics,
   selector or random gate batching, batching coefficient order, early stopping,
   hidden/intermediate variables, dimension changes, and next-layer claim
   construction.
5. For multi-output layers, enumerate every output/group/pair, its coefficient,
   offsets, terminal relation, and whether it is checked locally, exported to a
   global argument, or handed to the PCS.
6. For WHIR, trace every oracle cap, OOD sample, fold challenge, domain/coset,
   query index, Merkle leaf/path, final polynomial, and evaluation. Check
   bit-reversal, LSB/MSB order, cap geometry, deduplicated openings, and exact
   proof exhaustion.
7. At the GKR/WHIR seam, prove that the point, claim, batching challenge, base
   polynomial inventory, commitments, and ordering are identical on both sides.
8. Record local soundness terms: degree × variables, batch polynomial degree,
   number of layers/claims, WHIR proximity/query terms, and any exceptional
   challenge events. Do not claim total security bits; hand these terms to the
   soundness-budget specialist.
9. Inspect generated output, not only the generator. Compare a second
   implementation only after classifying it as a same-instance mirror,
   independent outer instance, or recursive wrapper.

## Required artifacts

### Protocol instance and focus

```text
entrypoint; generated artifact; field/extension; transcript; circuit/layer;
variable order; round/folding schedule; focus; incoming and outgoing handoff
```

### Claim-chain table

| Step | Incoming claim/source | Prover message | Required identity/degree | Challenge dependency | Outgoing claim | Final pin |
|---|---|---|---|---|---|---|

### Polynomial/batch inventory

| Item | Shape/degree | Commitment/provenance | Batch coefficient/order | Opened/checked where | Residual freedom |
|---|---|---|---|---|---|

### Local transcript rows and soundness terms

Include every challenge used by the selected phase and quantitative error terms
with assumptions, leaving global composition to the budget review.

## Evidence gate

Confirm a soundness finding only after stating the paper/repository invariant,
identifying the exact prover freedom, tracing every transcript and algebraic
check, establishing the generated/configured path is reachable, and giving a
bounded symbolic accepting assignment for a false claim. Keep it non-executable.
Separate completeness failures and parameter questions.

Preserve an exact but unreachable algebraic or transcript defect as a separate
**latent finding** when its activation condition—such as wiring a generator
branch, emitted verifier, feature, or caller—is concrete. Do not assign deployed
severity or claim present false acceptance. Speculative optimizations and
unfinished ideas without a demonstrated violated identity remain leads; a
reachable producer/completeness failure is not latent.

An exercised kernel or component test does not by itself establish an
end-to-end completeness failure. Check the enclosing prover path for earlier
unconditional `todo!()`, `unimplemented!()`, panic, disabled dispatch, or absent
proof assembly. If the affected value could not yet reach a proof consumer,
preserve the exact defect as latent and name the event that would activate it.
Likewise, a commit labelled `fix` is not evidence for a particular mechanism:
derive the before/after semantics from the implementation contract and exclude
semantically equivalent rewrites from the vulnerability corpus unless runtime
failure evidence establishes a distinct defect.

## Deliverable

Report only the selected component/phase and immediate handoffs. Include
confirmed findings, unresolved leads, closures, claim and batch artifacts, local
transcript rows, local error terms, generated-artifact coverage, and unreviewed
layers or PCS/composition dependencies.

Keep the work authorized, source-local, read-only, and defensive. Do not create
proof forgeries, malicious provers, or live deployment payloads.
