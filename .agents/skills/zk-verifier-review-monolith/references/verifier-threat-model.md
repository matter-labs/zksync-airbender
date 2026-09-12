# Verifier Threat Model

## The adversary

One adversary: a **malicious prover** with unbounded engineering effort,
bounded computation (no hash collisions, no discrete-log breaks), full
knowledge of the verifier source, and complete freedom over every byte it
sends. It wants one accepted proof of one false statement.

It does *not* need to produce a proof that looks honest. It needs to produce
data that survives the verifier's checks. Those are different targets, and the
gap between them is where verifier bugs live.

Assume the adversary:

- reads the verifier source and the generated verifier;
- computes challenges itself before committing to anything, and retries with
  different messages until a challenge is favourable, paying only the cost the
  grinding parameters impose;
- supplies values outside their intended domain (non-canonical encodings,
  out-of-range limbs, wrong-length structures) whenever the code does not
  reject them;
- supplies internally inconsistent structures — a value in one place that
  contradicts the same value elsewhere — whenever the code does not compare
  them;
- reorders, omits, or duplicates optional protocol elements when the code
  admits it;
- replays a valid proof against a different statement, circuit, chunk index,
  security level, or version whenever the transcript does not separate them.

For an EVM/L1 path, also assume it can choose transaction sender/order/gas,
call every public/fallback/proxy path, submit partial or replayed split proofs,
call helper/registry functions directly, target any caller-supplied address,
and exploit calldata truncation/high bits. It cannot rewrite immutable deployed
code or trusted governance state unless those are explicitly in scope, but it
can exploit any missing authentication between that state and verification.

## What counts as a verifier soundness bug

An accepting run of the verifier on inputs for which the claimed statement is
false. Concretely, at least one of:

- **Unbound prover value** — a value influences the accept decision but nothing
  constrains it to its honest value or domain.
- **Broken Fiat–Shamir** — a challenge can be computed by the prover before it
  has committed to data the soundness argument requires it to depend on, or the
  same challenge serves two roles that must be independent.
- **Wrong check** — a check exists but compares the wrong quantities, uses the
  wrong round/index/parameter, or is algebraically weaker than the paper's.
- **Missing check** — a step the soundness proof requires is absent.
- **Non-rejecting rejection** — the failure path does not actually abort, is
  compiled out, is unreachable, or its result is discarded.
- **Composition failure** — each chunk verifies but the aggregate statement
  does not follow (see `cross-circuit-and-aggregation-expanded.md`).
- **Parameter mismatch** — the verifier enforces a weaker parameter than the
  claimed security level requires, or a parameter is taken from the proof
  rather than from the verifier key.
- **Settlement/authentication failure** — untrusted code or a partial/replayed
  registry state can authorize the same L1 effect as a valid final proof, or a
  verifier failure is ignored by the caller.

A **material completeness bug** is an honest proof of a true statement that the
verifier rejects. Report these separately; they are availability bugs, not
soundness bugs, and they carry no security severity.

Exclude from findings: style, performance, maintainability, and panics on
already-invalid proofs (a panic *is* rejection in a verifier whose contract is
abort-on-invalid — confirm that contract before relying on it).

## What is not in scope by default

This skill targets computational verifier soundness: acceptance of a false
statement beyond the budgeted error. Unless the user expands scope, do not file:

- zero-knowledge/privacy leakage or witness-hiding failures;
- proof-of-knowledge, extraction, or knowledge-soundness gaps that do not also
  permit acceptance of a false statement under the claimed verifier contract.

State those exclusions explicitly. If the system claims no zero knowledge, do
not treat that as a defect.

Assume as sound primitives, and say so in the report:

- field arithmetic and extension-field arithmetic;
- the hash function's collision/preimage resistance at its configured
  parameters — but **not** a reduced-round variant's, unless the repository
  documents the security claim for the reduced variant; record that as an
  explicit dependency;
- the mathematical soundness of sumcheck, GKR, LogUp, permutation/memory
  arguments, FRI, and WHIR *as stated in their papers*;
- the correctness of the circuits themselves (that is `zk-circuit-review`).

None of these excuse the verifier from implementing the construction it claims.
The assumption is the obligation.

## The two questions that generate candidates

For every line of the verifier, ask exactly two things.

**1. What does this let the prover choose?**

Walk the proof stream, not the check list. Every read of prover data is a
degree of freedom until something removes it. Enumerate the freedoms first,
then look for the constraint on each — not the other way round. A checklist of
existing checks will always look complete; a ledger of prover freedoms will
not.

**2. Could the prover have known this challenge before fixing that message?**

For every challenge, list what was absorbed before it and what is used after
it. Anything used after the challenge, whose honest value the prover could
still change, and which is not itself bound by a later check, is a candidate.

## High-yield locations

Ranked by observed frequency in this class of system:

1. **Transcript ordering at phase boundaries** — the handoff between protocol
   phases (setup→GKR, GKR→PCS, per-chunk→aggregate) is where absorb order is
   most often reasoned about locally and wrong globally.
2. **Optimizations that change what is sent.** Batched openings, cap-based
   Merkle trees, early sumcheck termination, deduplicated claims, cached
   relation evaluations, merged commits. Each replaces N checks with one and
   the correctness argument moves into a batching challenge that must bind all
   N items.
3. **Values the verifier both receives and could recompute.** If it recomputes,
   confirm it compares. If it does not recompute, confirm it binds.
4. **Conditional and configuration-dependent paths.** `if num_x > 0`, feature
   flags, security levels, `cfg(target_arch)`, generated-code branches. A
   transcript step inside a conditional creates two different transcripts.
5. **Anything a comment calls subtle, matching, or mirroring the prover.** Such
   comments mark exactly the invariants that a later refactor breaks silently.
   Verify each against the prover rather than trusting the comment.
6. **Index and length arithmetic** in query derivation, Merkle path traversal,
   layer/round indexing, and buffer sizing.
7. **Cross-implementation divergence.** Wherever two implementations of the
   same verifier exist, their differences are unreviewed by construction.

## Rejection mechanics

Before trusting any check, confirm how the verifier signals rejection and that
the signal is honoured:

- Is the check `assert!` or `debug_assert!`? `debug_assert!` is compiled out in
  release. Treat any soundness claim resting on one as broken.
- Does it return `Err`, and does every caller propagate rather than discard?
- Does the check run on the deployed target? Guards behind
  `cfg(test)`/`cfg(feature)` may not exist in production.
- In a recursive verifier compiled to a guest ISA, does a panic actually
  terminate with a distinguishable, non-accepting outcome?
- Where the verifier is generated, does the *generated* code contain the check?
  Read the generator's output shape, not only its input logic.
- In Solidity/Yul, does a low-level call's success bit reach a `revert`, and is
  the target the authenticated verifier/helper? A successful transaction,
  event, or externally writable registry bit is not itself a rejection/acceptance
  mechanism.

## Recursion changes the boundary

When the verifier runs inside another proof (recursive verification), two extra
classes appear:

- **The inner statement must be bound into the outer transcript.** The inner
  verifier key / setup identity and the inner public inputs must be part of
  what the outer proof commits to; otherwise a valid proof of the wrong
  statement is accepted.
- **Verifier bugs become circuit bugs.** An unchecked value inside the guest
  verifier is a value the guest program's prover controls. Apply the same
  ledger to the guest's non-determinism inputs.

## Availability is not the target, but note it

A verifier that can be made to loop, exhaust memory, or read out of bounds on
adversarial input is a real defect and belongs in the report — under a
non-security or completeness heading unless the out-of-bounds behaviour can be
steered into an *accept*. Unsafe indexing on prover-derived indices is the case
where it can, so trace those bounds before classifying.
