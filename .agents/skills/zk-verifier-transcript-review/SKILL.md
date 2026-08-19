---
name: zk-verifier-transcript-review
description: Defensively audit one named verifier transcript state machine or bounded proof-parsing phase for causal Fiat-Shamir binding, serialization, canonicalization, proof exhaustion, and prover-controlled inputs. Choose this when the primary question is what was parsed, absorbed, sampled, or checked and in what order; leave protocol algebra to the matching GKR/WHIR or STARK/FRI specialist and do not use it as a whole-codebase audit.
---

# Focused Verifier Transcript and Proof-Input Review

Audit one concrete transcript state machine deeply. Treat every proof word as
adversarial freedom until timely absorption and a semantic check bind it.

## Require a bounded target

Resolve the user's target to all of:

- one concrete verifier or prover entrypoint;
- one proof-system instance `(field, extension, hash, encoding, parameters)`;
- either its complete transcript or one named phase with an explicit incoming
  state and outgoing handoff;
- one version, build/feature set, security mode, and generated artifact.

If no target is supplied, ask for a verifier entrypoint or transcript phase. Do
not choose the whole repository. Review a small coupled pair only when necessary
to compare mirrors, a serializer/parser pair, or the two sides of one handoff.

Default to the verifier because it defines acceptance. If the user explicitly
targets a prover, or the verifier does not exist yet, audit the prover's claimed
interactive schedule and proof encoding as a provisional contract. Label every
obligation that still requires verifier confirmation; do not report a verifier
soundness finding from prover behavior alone.

## Preserve protocol expertise

This is not a hash-call grep. Recover the interactive protocol for the selected
phase so that each challenge's required causal dependencies come from Sumcheck,
GKR, WHIR, AIR, DEEP-ALI, FRI, lookup, memory, or recursion theory—not merely
from what the implementation happens to absorb.

When another specialist produced a transcript artifact, verify it against source
before consuming it. When no artifact exists, build it here. A protocol review
may duplicate the local rounds later; that seam overlap is intentional.

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
2. Reconstruct the public-coin interactive protocol before applying
   Fiat-Shamir. For every verifier challenge, identify the prover message that
   must precede it and the relation the challenge protects.
3. Walk actual parse order, not function grouping. Record every read, conversion,
   absorb, draw, PoW step, branch, loop count, check, and later use.
4. Model the transcript state exactly: initialization, domain/context binding,
   pending buffers, grouping, active lengths, padding, canonicalization,
   challenge mapping, draw advancement, forks/clones, and PoW mutation.
5. Compare verifier and prover only after deriving the verifier schedule. For a
   same-instance mirror, also compare serializer, recursive verifier, generated
   output, or Solidity/Yul implementation byte-for-byte at the semantic level.
6. Search for semantic pins on every duplicate, cache, claimed challenge,
   commitment/cap, evaluation, count, tag, path, and final output. Absorption is
   not validation; validation after a dependent draw is not timely binding.
7. Exercise empty, singleton, optional, padding, alternative-branch, truncated,
   trailing-data, noncanonical, and maximum-length paths symbolically.
8. Finish the selected phase and its immediate incoming/outgoing transcript
   handoffs. List unreviewed prefixes, suffixes, and callers rather than silently
   implying complete-proof coverage.

## Required artifacts

Produce:

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

## Deliverable

Report the selected target and phase first, then confirmed findings, unverified
leads, closed candidates, transcript/proof-data artifacts, and exact coverage
limits. State explicitly whether the review began from a verifier or only a
provisional prover contract.

Keep the work authorized, source-local, read-only, and defensive. Do not create
forged proofs, exploit provers, deployment payloads, or live-system procedures.
