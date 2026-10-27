# Verifier Review Report Format

Use exact source locations and distinguish confirmed findings from leads.

## 1. Executive summary

State:

- exact verifier entrypoint, commit/tag, build/features, protocol generation, and security mode;
- for EVM/L1, exact Solidity/Yul generator input, compiler/settings, runtime
  bytecode hash/address, helper/registry/proxy configuration, and settlement caller;
- number of confirmed soundness and material completeness findings;
- separately counted robustness/availability issues;
- major coverage limits and unresolved specification dependencies.

## 2. Scope and accepted-statement dossier

List entrypoints, parser, generated verifier and generator, transcript, PCS, full-statement aggregator, recursion wrappers, prover references, protocol sources, setup/public statement, and excluded components.

For an on-chain path, include a deployment trust map from generated source to
deployed bytecode to the contract that authorizes the state transition. State
whether L1 verifies a base chunk, unified recursion chunk, final recursive proof,
or split GKR/PCS proof pair.

## 3. Protocol reconstruction

Include concise versions of:

- proof-data ledger;
- interactive/transcript schedule;
- challenge dependency ledger;
- claim/composition graph;
- parameter/soundness budget.

Large detailed ledgers may go in an audit artifact, but the report must contain enough to evaluate coverage.

## 4. Confirmed soundness findings

```text
## [SEVERITY] Title

Location and reachability:
Exact files, functions/generated artifacts, lines, build features, external
entrypoint, and—where applicable—deployed bytecode/address, compiler/EVM fork,
authorized callers, transaction ordering, and settlement path.

Target invariant:
Exact protocol or composition rule and its source.

Prover-controlled freedom:
The proof item(s), encoding, parse path, transcript timing, and semantic role.

Observed verifier behavior:
Every relevant absorption, challenge, equation, opening, and downstream/outer check.

Bounded malicious transcript / algebraic mismatch:
A non-executable symbolic construction showing all checks can pass while the intended statement is false. Fix all relevant branches, counts, selectors, claims, and challenge dependencies.

Impact:
Trace the mismatch through PCS/composition to the final accepted statement and assign severity by that effect.

Validation:
Closing checks searched, parameter/feature reachability, and skeptical validation actually performed.

Missing invariant and regression property:
State the defensive binding/check/order requirement and the property a test should assert.
```

Do not provide an exploit prover or operational forgery recipe.

## 5. Confirmed material completeness failures

Use the same structure with a valid intended proof/statement case that the verifier rejects or cannot represent.

## 6. Robustness and availability

Separate malformed-proof panics, unbounded work/allocation, unsafe memory behavior, and parser denial-of-service from cryptographic soundness unless they change acceptance.

## 7. Unverified leads and specification questions

For each item state:

- suspected invariant;
- prover freedom or implementation mismatch;
- exact checks/sources searched;
- missing evidence needed to confirm or close it;
- whether it concerns a paper deviation, deployment selection, or absent system-level anchor.

Do not assign a security severity to unresolved items.

## 8. Composition and trust ledger

| Deferred invariant | Per-proof producer/check | Returned claim | Aggregator/final anchor | Coverage status |
|---|---|---|---|---|

Include setup trust, hash/field assumptions, global memory, delegation, padding/chunks, recursion, and external public-input anchoring.

For EVM/L1 include generator/output/deployment provenance, split-verifier handoff,
registry writer authorization, replay/overwrite rules, low-level-call result
handling, recursion-chain terminus, and the final state-transition consumer.

Include a trusted-constant provenance table for setup caps/keys, imported
generated modules, program or circuit digests, final-PC constants, security
parameters, and their regenerated/deployed values.

Classify every cross-implementation issue as either (a) a same-instance
accepted-language divergence, (b) an unauthenticated statement handoff between
independent instances, or (c) a recursive-wrapper anchoring failure. Do not call
different fields, hashes, or proof encodings a parity failure when proof
portability was never intended.

## 9. Non-security observations

Optionally include performance, maintainability, redundant checks, documentation drift, or test gaps. Keep these last.

## 10. Coverage, candidate disposition, and verified closures

Summarize every material lead as confirmed, closed with exact evidence, or unresolved. State unreviewed protocol rounds, proof classes, feature variants, generated artifacts, and parameter regimes. If there are no findings, say `No confirmed findings`; never lower the evidence gate to fill the report.

For recurring closed leads, include the closing mechanism, exact source/config,
and what change would reopen the issue. Do not present a known closure as a new
candidate, and do not carry it across versions without revalidation.
