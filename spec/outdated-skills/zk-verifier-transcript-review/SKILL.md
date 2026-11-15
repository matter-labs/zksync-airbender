---
name: zk-verifier-transcript-review
description: Defensively audit one named verifier transcript state machine or bounded proof-parsing phase for causal Fiat-Shamir binding, serialization, canonicalization, proof exhaustion, and prover-controlled inputs. Choose this when the primary question is what was parsed, absorbed, sampled, or checked and in what order; leave protocol algebra to the matching GKR/WHIR or STARK/FRI specialist and do not use it as a whole-codebase audit.
---

# Focused Verifier Transcript and Proof-Input Review

Audit one concrete transcript state machine deeply. Treat every proof word as
adversarial freedom until timely absorption and a semantic check bind it.

## Defensive correctness scope

This is an authorized, benign, read-only review of verifier correctness. Its
purpose is to identify implementation flaws so maintainers can patch them.
Limit deliverables to root cause, the precise verifier acceptance or rejection
consequence, remediation, and defensive regression tests. Use only minimal
symbolic counterexamples needed to prove a mismatch. Do not produce executable
demonstrations, operational reproduction procedures, deployment payloads,
network probes, credential/access steps, or live-system instructions.

## Require a bounded target

Resolve the user's target to all of:

- one concrete verifier entrypoint;
- one proof-system instance `(field, extension, hash, encoding, parameters)`;
- either its complete transcript or one named phase with an explicit incoming
  state and outgoing handoff;
- one version, build/feature set, security mode, and generated artifact.

If no target is supplied, ask for a verifier entrypoint or transcript phase. Do
not choose the whole repository. Review a small coupled pair only when necessary
to compare mirrors, a serializer/parser pair, or the two sides of one handoff.

The verifier defines acceptance and is mandatory. If the user supplies only a
prover or the matching verifier does not exist yet, ask for the verifier target
or state that this verifier-review skill cannot establish the requested result.
Do not replace the missing acceptance predicate with a provisional prover audit.

After reconstructing verifier behavior, inspect only the smallest prover,
flattener, serializer, or GPU slice needed to explain proof framing, intended
round order, parameter provenance, or an observed parity failure. A producer
defect that the verifier rejects is not a primary finding; record it separately
as producer parity and return to the verifier.

### Verifier-first search discipline

Spend the review context on the selected verifier parser, transcript state,
acceptance checks, generated verifier artifact, and caller. Reconstruct proof
framing from verifier reads before opening producer code. Consult at most the
specific producer/serializer symbols needed to resolve one disputed field or
ordering edge; do not inventory or audit the prover transcript in parallel. A
primary finding must name the verifier operation that absorbs, samples, checks,
or fails to check the adversarial value.

## Preserve protocol expertise

This is not a hash-call grep. Recover the interactive protocol for the selected
phase so that each challenge's required causal dependencies come from Sumcheck,
GKR, WHIR, AIR, DEEP-ALI, FRI, lookup, memory, or recursion theory—not merely
from what the implementation happens to absorb.

When another specialist produced a transcript artifact, verify it against source
before consuming it. When no artifact exists, build it here. A protocol review
may duplicate the local rounds later; that seam overlap is intentional.

### Treat late special-case data as a primary target

Transcript bugs often appear when a normal round is extended with auxiliary,
optional, dynamically discovered, cached, deferred, or branch-specific proof
data. Do not derive a challenge's dependency set merely from the buffer located
next to its draw. Start from every downstream use of the challenge and enumerate
**all** prover-controlled values entering the randomized relation.

Before drawing a batching, folding, lookup, permutation, opening, or other
randomness challenge, every prover-controlled value that the challenge is meant
to randomize must already be fixed. A value is timely fixed only when it has
been canonically absorbed into the transcript, is authenticated by an earlier
commitment already bound into the transcript, or is uniquely recomputable from
public or previously bound data. Reading or absorbing it after the draw is too
late; later transcript updates cannot repair causality.

Apply a strict late-data presumption:

- if the verifier consumes a proof value under a challenge sampled before that
  value was fixed, treat the ordering as a soundness defect unless a concrete
  prior pin uniquely determines the value independently of that challenge;
- a later algebraic check, randomized batch, opening, or consistency relation
  is not by itself a closure. To close the candidate, prove that the late value
  has no remaining choice because earlier authenticated data uniquely fixes it;
- do not dismiss the candidate merely because honest implementations share the
  order or because changing one late value in isolation fails. Correlated or
  adaptive choices are exactly what timely randomization is intended to defeat;
- do not require a complete end-to-end forgery or solve a large system of
  degrees of freedom when the local verifier acceptance relation plainly lets
  the prover choose an input after learning the challenge intended to bind it.
  Establish the local late choice, its challenge-dependent consumer, and the
  absence of a prior unique pin; use deeper algebra only when a purported
  closing relation could actually determine the value uniquely.

## Read the applicable references

Always read:

- [Fiat-Shamir transcript](../zk-verifier-review/references/fiat-shamir.md)
- [proof-input validation](../zk-verifier-review/references/proof-data-validation.md)

Read only what the target needs:

- Rust, generated code, `unsafe`, or nondeterminism parsing:
  [Rust verifier surfaces](../zk-verifier-review/references/rust-verifier-surfaces.md)
- Sumcheck/GKR or WHIR ordering:
  [Sumcheck and GKR](../zk-verifier-review/references/sumcheck-and-gkr-expanded.md)
  and/or [WHIR PCS](../zk-verifier-review/references/pcs-whir-expanded.md)
- AIR/DEEP-ALI/FRI ordering:
  [legacy STARK](../zk-verifier-review/references/stark-deep-fri.md)
- matching Airbender snapshot only:
  [project profile](../zk-verifier-review/references/airbender-gkr-v1-profile.md)

## Workflow

1. Fingerprint the statement, transcript implementation, parser, field API,
   serializer/flattener, features, generated output, and callers.
   Before walking prover messages, build the semantic-context manifest below.
   Enumerate every choice that changes the verified statement or the meaning of
   later bytes: entrypoint, operation, circuit family, protocol/version,
   verifier setup or key, security mode, recursion role, and participant order.
   Hold the absorbed bytes fixed and change one such choice at a time. The seed
   must differ before the first dependent challenge unless an authenticated
   enclosing statement already binds that choice. Parser control flow, a Rust
   enum match, or selecting a different verifier function is not by itself
   transcript binding.

   An authenticated program/setup hash can close this obligation when it
   uniquely identifies a single-mode verifier, as can an authenticated public
   branch selector. A hash of a multi-mode dispatcher authenticates its code,
   but does not by itself bind a prover-controlled runtime branch. Record the
   exact closure instead of demanding a redundant tag or assuming dispatch is
   sufficient. Verifier-known constants may be absorbed directly; they need
   not arrive in the proof.
2. Reconstruct the public-coin interactive protocol before applying
   Fiat-Shamir. For every verifier challenge, identify the prover message that
   must precede it and the relation the challenge protects.
3. Walk actual parse order, not function grouping. Record every read, conversion,
   absorb, draw, PoW step, branch, loop count, check, and later use.
   At every draw, walk forward to all consumers of the challenge, collect every
   prover-controlled input they use, and walk each input backward to its first
   transcript absorption or earlier authenticated pin. Flag any gap before
   analyzing unrelated transcript phases.
4. Model the transcript state exactly: initialization, domain/context binding,
   pending buffers, grouping, active lengths, padding, canonicalization,
   challenge mapping, draw advancement, forks/clones, and PoW mutation.
5. Compare verifier and prover only after deriving the verifier schedule and
   only when needed to resolve one concrete verifier input or mirror. For a
   same-instance mirror, also compare serializer, recursive verifier, generated
   output, or Solidity/Yul implementation byte-for-byte at the semantic level.
6. Search for semantic pins on every duplicate, cache, claimed challenge,
   commitment/cap, evaluation, count, tag, path, and final output. Absorption is
   not validation; validation after a dependent draw is not timely binding.
7. Exercise empty, singleton, optional, padding, alternative-branch, truncated,
   trailing-data, noncanonical, and maximum-length paths symbolically.
8. Finish the selected phase and its immediate incoming/outgoing transcript
   handoffs. List unreviewed prefixes, suffixes, and callers rather than silently
   implying complete-proof coverage. Even after confirming another bug, finish
   the semantic-context manifest and same-instance prefix-parity comparison for
   the bounded phase.

## Required artifacts

Produce:

### Semantic-context manifest

| Semantic choice | Selected by | Changes interpretation of | Bound by authenticated enclosing statement? | Absorbed before first dependent draw? |
|---|---|---|---|---|

For each row, test whether identical absorbed bytes can reach the same
challenge seed while the verifier interprets them as a different relation,
family, mode, or participant.

### Target fingerprint

```text
entrypoint; commit; features/target; generated artifact; field/extension;
hash/transcript; encoding; statement/context; selected phase; callers
```

### Proof-data ledger

| Item | Parsed/converted at | Accepted domain | Required domain | Absorbed when | Semantic pin | Residual freedom |
|---|---|---|---|---|---|---|

### Transcript round table

| Round | Incoming state/claim | Prover message | Exact absorption | Challenge/PoW | Must depend on | First protected check | Outgoing state |
|---|---|---|---|---|---|---|---|

### Challenge-dependency table

| Challenge | Randomized relation/consumer | Complete prover-controlled input set | Fixed before draw by | Late inputs | Valid prior unique pin or defect |
|---|---|---|---|---|---|

Populate this table from challenge consumers, not from adjacent absorb calls.
For every claimed closure, name the earlier authenticated data and the exact
reason it uniquely determines the allegedly late input.

### Branch and implementation map

Record conditional transcript shapes and classify comparisons as same-instance
mirrors, independent instances joined by a statement handoff, or recursive
wrappers. Do not demand proof portability across different fields or hashes.

## Evidence gate

Confirm a soundness finding only after identifying the exact prover freedom,
the protocol-derived ordering/binding invariant, every direct and indirect
closing check, reachable configuration, and a bounded symbolic accepting flow
for a false statement. Keep it non-executable. Demote unresolved items to leads
or specification questions. Distinguish completeness and robustness failures.

For a direct late-ordering violation, the exact prover freedom can be the
ability to select the late value after observing the challenge that is supposed
to randomize it. Confirmation does not require reconstructing a full public
statement forgery when the verifier reaches a concrete challenge-dependent
consumer and no earlier commitment, absorption, or deterministic recomputation
uniquely pins that value. Report the result as local/component soundness and
bound its impact accordingly. Demand deeper degrees-of-freedom analysis only
when a plausible prior or later check may actually eliminate the late choice.

If defective verifier source is active but no consuming acceptance path and no
concrete verifier-caused honest-proof rejection path exists, classify it as an
**implementation-only defect**, not as soundness or completeness. State the
conditional consequence of a future consumer separately.

If only prover, GPU, replay, or serialization code is defective and the selected
verifier remains correct, classify it as **producer parity**, not a verifier
finding. Do not promote it because a hypothetical verifier could copy the bug,
and do not include it in primary verifier blind evaluation.

Do not discard a concrete defect solely because no current caller, feature, or
artifact reaches it. Report it separately as a **latent finding** when the
violated invariant and defective code are exact and the activation condition is
known, but do not assign deployed severity or claim present false acceptance.
A suspicious template, TODO, or hypothetical future misuse without a concrete
defect remains a lead. Keep latent findings distinct from reachable
completeness and robustness failures.

## Deliverable

Report the selected target and phase first, then confirmed findings, unverified
leads, closed candidates, transcript/proof-data artifacts, and exact coverage
limits. Name the concrete verifier entrypoint and acceptance consumer on which
the result is based.

Keep the work authorized, source-local, read-only, and defensive. Do not create
forged proofs, exploit provers, deployment payloads, or live-system procedures.
