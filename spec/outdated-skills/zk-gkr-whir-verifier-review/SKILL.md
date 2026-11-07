---
name: zk-gkr-whir-verifier-review
description: Defensively audit the algebraic claim chain of one named Sumcheck, GKR, multilinear-polynomial, or WHIR verifier component, generated verifier slice, protocol phase, or immediate GKR-to-PCS handoff. Choose this when the primary question is layer, fold, batching, opening, or Merkle/PCS correctness; include the phase's local transcript dependencies and require a bounded entrypoint rather than auditing every GKR/WHIR path at once.
---

# Focused Sumcheck, GKR, and WHIR Verifier Review

Audit one concrete algebraic reduction deeply, including the transcript ordering
that makes its probabilistic checks sound. Protocol expertise and transcript
expertise are inseparable here.

## Defensive correctness scope

This is an authorized, benign, read-only review of verifier correctness. Its
purpose is to identify implementation flaws so maintainers can patch them.
Limit deliverables to root cause, the precise verifier acceptance or rejection
consequence, remediation, and defensive regression tests. Use only minimal
symbolic counterexamples needed to prove a mismatch. Do not produce executable
demonstrations, operational reproduction procedures, deployment payloads,
network probes, credential/access steps, or live-system instructions.

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

The verifier is mandatory. Use the prover only to recover one needed message
format, polynomial layout, or intended optimization after deriving verifier
behavior. If no matching verifier or generated verifier slice exists, do not
substitute a prover-first review. Producer-only algebra, GPU, opening, or
serialization defects belong to producer-parity history rather than primary
verifier findings.

### Split-verifier baseline

If GKR and WHIR/PCS have separate verifier entrypoints, contracts, transactions,
or binaries, treat them as two local acceptance reviews plus one seam review;
do not audit the whole split implementation as one undifferentiated pass. The
GKR review owns its terminal-output predicates and the exact handoff it emits.
The WHIR review owns the claims, commitments, folds, openings, and success
predicate it consumes. The seam review proves equality of the statement,
commitments, transcript state, evaluation point, claim inventory, batching
challenge, parameters, encoding, and public outputs on both sides. Use separate
reviewers by default when independent delegation is explicitly permitted, then
reconcile their artifacts; otherwise keep separate sequential artifacts. A
focus wholly inside one side may stay local but must name the unreviewed seam
dependency.

### Verifier-first search discipline

Start with the verifier's incoming claim and acceptance predicate, then trace
its round checks, folds, batches, openings, and outgoing claim. Prefer emitted
verifier code over its generator and prefer the generator over prover kernels
only when explaining how the emitted code arose. Consult a prover symbol solely
to decode an already-observed proof message or claimed optimization. A wrong
prover polynomial, GPU index, Merkle path, or serializer is not a finding if the
selected verifier rejects it.

### Prove theory-to-implementation correspondence

For each selected Sumcheck identity, GKR gate/layer relation, batch, fold, or
opening equation, name every logical polynomial, claim, point, and equality
required by the theorem. Enumerate every verifier use of those objects and
resolve it from the selected circuit artifact, JSON, layout, or verifier key
into the emitted verifier expression and the concrete authenticated value it
consumes. This artifact-to-emitted comparison is primary. Inspect generator code
only when needed to explain the emitted behavior, resolve an otherwise opaque
lowering, or ensure regeneration cannot restore the defect; generator parity is
not required to establish a flaw visible in the emitted verifier. Uses of the
same logical object must resolve to the same polynomial, claim, and evaluation
point, or the verifier must enforce an authenticated equality/copy relation
between the distinct objects. Comments, names, types, neighboring indices,
locally plausible roles, and successful execution do not prove this
correspondence. Close the protocol obligation only after every concrete use and
cross-equation join is explicit.

## Mandatory local transcript contract

For every selected probabilistic check, reconstruct the local interactive rounds
and then the exact Fiat-Shamir schedule. Verify that each round polynomial,
commitment/cap, evaluation vector, next-layer claim, folding oracle, terminal
polynomial, nonce, and query-dependent opening is fixed before the challenge
whose theorem requires it. Do this even if a separate transcript skill ran.

Consume an existing transcript artifact only after checking its rows against the
selected source and protocol. Emit corrected or additional rows as part of this
review.

## Mandatory terminal-claim authentication closure

A Sumcheck or GKR consistency check reduces a claim; it does not by itself
authenticate every polynomial evaluation used at the terminal gate. For every
selected layer and especially the GKR-to-PCS seam, enumerate **every** terminal
claim/address and assign exactly one authoritative final pin:

- opened from a transcript-bound commitment through WHIR/PCS;
- deterministically computed by the verifier from the statement, setup, and
  final evaluation point;
- compared with an authenticated public input or constant; or
- checked by a separate defining relation whose own inputs are authenticated.

No claim may remain unclassified, and mutual consistency, transcript
absorption, use inside a gate, or inclusion in a random batch is not a final
pin. Compute the set difference between all claims consumed by the layer and
all claims authenticated by the next phase. Inspect every element of that
difference; finding one defective cached claim does not complete the inventory
or justify stopping.

Treat fixed or `VirtualSetup` polynomials specially. They may legitimately be
uncommitted precisely because the verifier can evaluate them itself. At the
exact final Boolean/MLE point, the verifier must either substitute its own
computed value directly or compare any prover-supplied copy against that value.
Merely using the supplied copy to evaluate the terminal gate proves a relation
over a prover-chosen input. For every virtual-polynomial variant present in the
compiled artifact, locate the emitted closed-form evaluator and equality check;
reject unhandled variants and do not infer coverage from one checked variant.

### Exhaust the bounded implementation slice

Scoping selects one manageable acceptance slice; inside that slice, build a
file-and-symbol ledger from the verifier entrypoint through every reachable
round helper, claim/address selector, parser/cursor operation, generator
definition, emitted artifact, commitment/opening check, and rejection path.
Inspect every acceptance-relevant ledger entry or mark its obligation
unreviewed. Broad or truncated searches, representative samples, relation
counts, and generator/emitted parity are navigation evidence, not coverage.

When that bounded slice is too large for one context and independent delegation
is available and explicitly permitted, partition disjoint files or local
implementation obligations among subagents using the same theorem and claim
definitions. Reserve an integration pass for cross-file claim identity,
transcript continuity, parser-to-equation mappings, generator-to-emitted
behavior, and the GKR/WHIR seam; a local reviewer cannot infer those joins from
another reviewer's labels. Without delegation, narrow the phase further or
inspect the ledger sequentially rather than silently omitting implementation.

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
2. Build the complete claim chain and the mandatory authentication partition
   above. Derive the full consumed-claim set from emitted addresses/gates and
   the PCS-opened set from emitted WHIR indices; reconcile their cardinalities
   and inspect the exact set difference. Label every claim as statement/setup-
   derived, commitment-authenticated, locally recomputed, previous-round-
   derived, or prover-supplied. Mutual consistency is not provenance.
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
   Then prove that every GKR claim omitted from the PCS inventory has a concrete
   verifier-side final pin; omission is an audit obligation, never evidence that
   the claim is irrelevant.
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

### Terminal-claim authentication partition

| Claim/address | Consumed by gate/reduction | PCS-opened | Verifier-computed | Public/constant-bound | Separately constrained | Exact final pin |
|---|---|---|---|---|---|---|

Require complete cardinality reconciliation and an empty unclassified set.
List every fixed/virtual variant separately and cite its generated computation;
do not collapse them into one representative row.

### Local transcript rows and soundness terms

Include every challenge used by the selected phase and quantitative error terms
with assumptions, leaving global composition to the budget review.

## Evidence gate

Confirm a soundness finding only after stating the paper/repository invariant,
identifying the exact prover freedom, tracing every transcript and algebraic
check, establishing the generated/configured path is reachable, and giving a
bounded symbolic accepting assignment for a false claim. Keep it non-executable.
Separate completeness failures and parameter questions.

Preserve an exact but unreachable verifier algebra or transcript defect as a
separate **latent finding** only when the defective emitted verifier/helper and
its activation condition are concrete. A generator branch that emitted no
verifier is implementation history; a prover/GPU/kernel defect rejected by the
verifier is producer parity. Do not assign deployed severity or claim present
false acceptance.

An exercised prover kernel or component test does not establish verifier
completeness or soundness. Likewise, a commit labelled `fix` is not evidence for
a verifier mechanism: derive the before/after acceptance relation and exclude
semantically equivalent rewrites or producer-only runtime failures from the
vulnerability corpus.

## Deliverable

Report only the selected component/phase and immediate handoffs. Include
confirmed findings, unresolved leads, closures, claim and batch artifacts, local
transcript rows, local error terms, generated-artifact coverage, and unreviewed
layers or PCS/composition dependencies.

Keep the work authorized, source-local, read-only, and defensive. Do not create
proof forgeries, malicious provers, or live deployment payloads.
