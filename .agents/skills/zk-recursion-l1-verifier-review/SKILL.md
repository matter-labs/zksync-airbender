---
name: zk-recursion-l1-verifier-review
description: Defensively audit one named recursive-verifier, verifier-binary, implementation-handoff, or Solidity/Yul/L1 acceptance boundary, including generated artifacts, program/setup identity, recursive-chain anchoring, public outputs, calldata, contract linkage, and settlement authorization. Use for one bounded Rust, guest-binary, recursive, EVM, or deployment path; do not expand a single boundary into every recursion layer and contract.
---

# Focused Recursion, Verifier-Binary, and L1 Review

Audit one boundary where “a verifier ran” becomes a claim trusted by another
proof layer or by settlement. The target is one state/statement transition, not
every binary and contract in the system.

## Require one boundary

Select exactly one primary target:

- source/generator → generated verifier or guest binary;
- inner verifier result → recursive wrapper statement;
- recursion base case, step, no-op, or chain extension;
- final recursive output → L1 verifier input;
- one Solidity/Yul verifier entrypoint and its immediate caller;
- split GKR/PCS transactions → authenticated completion state;
- verifier result/registry state → authorized state transition.

Fingerprint commit, features/target, proof-system instance, program/setup/key,
compiler and generated artifact, public input/output encoding, caller, and final
consumer. For deployed EVM paths include compiler settings, runtime bytecode
hash/address, proxy/helper/registry configuration, chain/fork, and transaction
ordering. Ask for a target when absent; do not choose the whole recursion stack.

Default to the verifier and final consumer. Use prover/chain-construction code to
recover intended formats and missing specifications. If only a prover or
generator is ready, produce a provisional acceptance contract and list the
downstream checks that remain unaudited.

## Local transcript and proof-input obligations

Reconstruct every transcript phase and prover-controlled input that crosses the
selected boundary: inner proof statement, verifier key/program digest, prior
chain value, public output, handoff commitment, calldata copy, registry key, or
returned result. Protocol-specific transcript order remains in scope; an outer
wrapper cannot authenticate a value that the inner proof never bound.

## Read the applicable references

- Any recursion/statement boundary:
  [architecture](../zk-verifier-review/references/airbender-verifier-architecture.md)
  and [Fiat-Shamir](../zk-verifier-review/references/fiat-shamir.md)
- Rust/generated verifier or guest binary:
  [Rust verifier surfaces](../zk-verifier-review/references/rust-verifier-surfaces.md)
- Solidity/Yul, split transactions, registry, deployment, or settlement:
  [EVM/L1 verifier](../zk-verifier-review/references/evm-l1-verifier.md)
- Matching Airbender snapshot only:
  [project profile](../zk-verifier-review/references/airbender-gkr-v1-profile.md)

Load the large EVM reference only when the selected boundary is on-chain.

## Workflow

1. Write the exact precondition and postcondition of the selected boundary.
   State what an accepting upstream verifier established and what the downstream
   consumer assumes.
2. Classify implementations: same-instance mirrors, independent proof-system
   instances joined by a statement boundary, or recursive wrappers. Demand
   proof-language parity only for genuine mirrors; otherwise audit the statement
   handoff.
3. Trace trusted identity: verifier program/binary hash, circuit/setup/key,
   security parameters, final PC, base/step mode, recursion level, previous chain
   value, expected output, version/domain, and deployment/code identity.
4. For generated binaries, compare generator inputs, emitted source, compiled
   artifact, imported constants, features, optimizer behavior, guest exit/panic,
   and outer execution contract. A check is real only if it survives compilation
   and rejection propagates to the consumer.
5. For recursion, enumerate genesis, ordinary extension, no-op/continuation,
   termination, maximum depth, fork/truncation/reordering/replay, and chain digest
   preimage fields. Prove every inner public input/output is bound exactly once.
6. For EVM, map every calldata byte and Yul memory region; check canonical field
   decoding, dirty high bits, zero-padding reads, exact cursor exhaustion,
   256-bit/field arithmetic, memory aliasing, spills, optimizer annotations,
   returndata, and revert behavior.
7. For multi-contract or multi-transaction flows, build the persistent-state
   transition table. Authenticate writers/callees, bind complete handoff state,
   enforce call success and required returndata, and audit partial, reordered,
   duplicate, overwrite, replay, cross-version, and cross-deployment flows.
8. Trace successful verification into the actual state-transition decision. An
   event, successful transaction, registry mark, or unchecked external call is
   not acceptance by itself.
9. Compare source to exact deployed runtime bytecode and activated chain rules.
   Record prototypes/tests not reachable from settlement as exclusions, not
   production findings.

## Required artifacts

### Boundary contract

| Upstream producer | Authenticated input/identity | Check performed | Output/state | Downstream assumption | Final consumer |
|---|---|---|---|---|---|

### Artifact/deployment provenance

| Source/config | Generator output | Compiler/settings | Binary/runtime hash | Selected by | Reproducible? |
|---|---|---|---|---|---|

### Recursion or persistent-state table

| Prior state/chain | Authorized actor | Proof/input | Required checks | New state/chain | Replay/overwrite/finalize rule |
|---|---|---|---|---|---|

### Local transcript/input rows

Include every boundary-crossing prover value, when it was committed, and what
authenticates its semantic meaning.

## Evidence gate

Confirm a soundness finding only when the intended boundary contract, exact
attacker-controlled input/state transition, all upstream/downstream checks,
reachable compiled/deployed path, and final false accepted statement or
unauthorized state transition are established. A suspicious unused template is
an unverified lead, not a production vulnerability.

Confirm completeness only when the affected generated binary, contract, prover,
or wrapper was actually buildable/reachable and a canonical honest artifact is
shown to reject, panic, or fail to compose. A source fragment fixed before the
first compiling verifier is not a historical completeness failure. Likewise,
canonicalization or field-representation hardening is implementation-only unless
an exact consumer distinguishes the old representation in a rejecting or
accepting predicate.

Do not discard a concrete defect merely because the affected source, template,
binary, contract, or boundary is not deployed or called. Report it separately
as a **latent finding** when the violated boundary contract and exact activation
condition are established, but do not assign production severity or imply a
deployed acceptance path. An unused template with only a suspected risk remains
a lead; reachable prototype or test deployments must be labeled by their actual
consumer rather than automatically called latent.

## Deliverable

Report the single boundary, artifacts/deployment, confirmed findings, leads,
closures, tables, and adjacent recursion/contract layers not reviewed. State
whether the result applies to source, generated output, compiled binary, deployed
bytecode, or some subset—never conflate them.

Keep the work authorized, source-local, read-only, and defensive. Do not produce
deployment payloads, forged proofs, live-chain probes, or operational attacks.
