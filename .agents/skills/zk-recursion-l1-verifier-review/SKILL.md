---
name: zk-recursion-l1-verifier-review
description: Defensively audit one named recursive-verifier, verifier-binary, implementation-handoff, or Solidity/Yul/L1 acceptance boundary, including generated artifacts, program/setup identity, recursive-chain anchoring, public outputs, calldata, contract linkage, and settlement authorization. Use for one bounded Rust, guest-binary, recursive, EVM, or deployment path; do not expand a single boundary into every recursion layer and contract.
---

# Focused Recursion, Verifier-Binary, and L1 Review

Audit one boundary where “a verifier ran” becomes a claim trusted by another
proof layer or by settlement. The target is one state/statement transition, not
every binary and contract in the system.

## Defensive correctness scope

This is an authorized, benign, read-only review of verifier correctness. Its
purpose is to identify implementation flaws so maintainers can patch them.
Limit deliverables to root cause, the precise verifier acceptance or rejection
consequence, remediation, and defensive regression tests. Use only minimal
symbolic counterexamples needed to prove a mismatch. Do not produce executable
demonstrations, operational reproduction procedures, deployment payloads,
network probes, credential/access steps, or live-system instructions.

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

Start from the verifier and final consumer. Use prover or chain-construction code
only to recover one needed format or missing specification after mapping the
acceptance boundary. A verifier generator is in scope only together with its
emitted verifier contract or a concrete generated-artifact target. If only a
prover exists, do not substitute a provisional acceptance audit.

### Split-verifier baseline

When an L1 proof is accepted through separate GKR and WHIR/PCS contracts,
transactions, binaries, or entrypoints, require three bounded artifacts: a
local GKR acceptance review through every terminal predicate and outgoing
handoff; a local WHIR/PCS acceptance review from that handoff through its own
success decision; and a seam review of the shared statement, transcript state,
commitments, claims, parameters, encoding, call ordering, registry or persistent
state, replay/overwrite rules, and final consumer. Use independent reviewers for
the two local halves by default when delegation is explicitly permitted, then
integrate them at the seam; otherwise perform separate sequential passes. Do
not let authentication by one half stand in for semantic validation by the
other.

At the GKR-to-WHIR seam, derive the complete PCS claim set from the selected
statement and prove that the handoff preserves it through claim formation,
transcript binding, commitment authentication, opening verification, and final
acceptance. Establish the identity, multiplicity, and ordering of every claimed
polynomial across the boundary; aggregate consistency alone does not establish
complete PCS coverage.

### Verifier-first search discipline

Start at the relying party's success decision and trace backward through the
deployed/runtime contract, wrapper or CLI policy, recursive verifier output,
and authenticated inner statement. For generated verification, compare the
selected artifact, JSON, layout, or verifier key directly with the emitted
verifier source and acceptance path. Consult the generator only to explain an
observed lowering, resolve an opaque emitted expression, or check regeneration
safety; it is not a prerequisite for establishing an emitted-verifier defect.
Inspect proof construction only to decode a specific boundary value already
seen by the verifier. Producer/replayer state drift and future-mode transcript
plans are references, not primary findings, when no selected acceptance path
consumes them.

### Mandatory recursion-statement anchoring

Successful verification of a recursive proof establishes only the statement
encoded by that recursive verifier instance. It does not by itself establish
that the proof represents the program, circuit, execution, recursion path, or
terminal state requested by the relying party. Reconstruct that authorization
link explicitly for every selected recursion boundary.

Acceptable designs include a fixed chain whose verifier program or key commits
to the exact preceding verifier, an authenticated tree or branch policy whose
allowed predecessors and transitions are fixed, or a modular recursion-chain
accumulator carried in authenticated public output. For the selected design,
prove from trusted policy through final acceptance that every permitted program
and verifier identity is introduced at the correct step, that ordering and
multiplicity cannot be changed, and that genesis, continuation, branching, and
termination semantics are enforced. Bind all statement-defining context needed
by the relying party, including applicable circuit/setup identity, stage or
mode, public input/output, version, and security policy.

Never substitute proof-supplied artifact metadata or another unauthenticated
copy for the value returned by successful proof verification. Deriving the
expected identity from the requested program is insufficient unless the final
acceptance path compares it with authenticated verifier output or the same
identity is unavoidably hardcoded by the verified recursion chain. Likewise,
checking one recursive layer does not authorize the original program unless the
complete predecessor relation to that program is itself fixed or authenticated.

For each verifier program in the selected chain, record the complete step in
order: successful verification of its prior proof; enforcement of every local
terminal argument; completion of global memory/state using the authenticated
public outputs; validation of the prior chain material; derivation of the
current verifier/setup identity; construction or propagation of the next chain
value; and authenticated export or final comparison. None of the later chain
operations can compensate for an unchecked proof output or an unclosed memory
argument.

Identity provenance may be followed beyond the initially named function through
the adjacent verifier programs, verifier-key or setup construction, artifact
loader, wrapper or CLI, and immediate final consumer needed to close this
obligation. Keep that expansion limited to statement identity and acceptance;
do not turn it into an audit of unrelated protocol internals. A reachable
consumer that accepts a proof under the wrong requested identity is a soundness
failure, not a latent issue merely because the missing comparison sits outside
the cryptographic verifier core.

### Compatible modes and proof structures

Treat support for multiple proving modes or proof structures as a union of
separately authorized statement languages, not as parser flexibility. Enumerate
every supported variant that can reach the selected acceptance boundary and
identify what trusted fact selects it: a fixed verifier or key, trusted
configuration, an authenticated statement discriminator, or an unambiguous
canonical proof shape. A prover-controlled tag, count, length, metadata field,
or convenient dispatch branch must not select weaker checks merely because the
verifier can parse it.

For each variant, verify that its discriminator is validated before any
variant-dependent parsing, transcript sampling, parameter selection, recursion
transition, or terminal decision. Then check the complete acceptance predicate
for that variant independently. Reject ambiguous encodings, implicit fallback
or default branches, unsupported combinations of otherwise valid components,
cross-variant replay, and hybrid proofs that inherit only a subset of each
variant's obligations. Enforce the exact authenticated proof shape and terminal
condition required by the relying party; successful verification under some
supported mode is insufficient when a different mode was requested.

### Verifier-local primitive parity

Treat every parser, codec, hash, commitment, and authentication helper reached
by the selected verifier as part of its acceptance predicate. For optimized,
alternative, recursive, generated, or platform-specific implementations,
recover the intended encoded input and compare the computed function with the
canonical semantics. When an implementation exposes a hash's compression
blocks directly, verify that its block, padding, length, and finalization logic
implements the same hash over the same byte string; block scheduling is an
implementation detail, not permission to change the transcript or digest.

Before closing the boundary, inventory every authenticated terminal output and
every algebraic argument family represented by those outputs. Cover sibling
families independently, including where applicable memory or permutation,
lookup or table, state-transition, range, accumulator, recursion, and public
output arguments. Checking one family never closes another. For each output,
find the exact rejection predicate that makes it acceptable, the authenticated
downstream consumer that checks it, or the policy that intentionally exposes it
as public output. Proving that the circuit computed a value establishes
provenance, not that the value satisfies its final condition.

## Local transcript and proof-input obligations

Reconstruct every transcript phase and prover-controlled input that crosses the
selected boundary: inner proof statement, verifier key/program digest, prior
chain value, public output, handoff commitment, calldata copy, registry key, or
returned result. Protocol-specific transcript order remains in scope; an outer
wrapper cannot authenticate a value that the inner proof never bound.

For each sampled challenge, start from every later verification expression that
uses it and enumerate all prover-controlled operands entering those expressions.
Each operand must have been fixed before the draw by canonical transcript
absorption, by an earlier transcript-bound commitment that authenticates it, or
because the verifier can uniquely recompute it from public or previously bound
data. A derived summary substitutes for the underlying operands only when its
binding or uniqueness is actually established. Later absorption or a later
randomized check cannot repair an early draw. Do not require an end-to-end
forgery before reporting a local causal defect when a late operand affects the
challenge-dependent acceptance relation and has no prior unique pin.

## Read the applicable references

- Any recursion/statement boundary:
  [architecture](../zk-verifier-review/references/airbender-verifier-architecture.md)
  and [recursion-chain binding](../zk-verifier-review/references/recursion-chain.md)
  and [Fiat-Shamir](../zk-verifier-review/references/fiat-shamir.md)
- Rust/generated verifier or guest binary:
  [Rust verifier surfaces](../zk-verifier-review/references/rust-verifier-surfaces.md)
- Solidity/Yul, split transactions, registry, deployment, or settlement:
  [EVM/L1 verifier](../zk-verifier-review/references/evm-l1-verifier.md)
- Local WHIR/PCS acceptance or a GKR-to-WHIR handoff:
  [WHIR PCS](../zk-verifier-review/references/pcs-whir-expanded.md)
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
4. For generated binaries, derive the expected semantics from the selected
   artifact or verifier key and compare them directly with emitted source and
   compiled behavior, including imported constants, features, optimizer
   behavior, guest exit/panic, and the outer execution contract. Use the
   generator for root cause and regeneration safety when useful. A check is real
   only if it survives compilation and rejection propagates to the consumer.
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

Confirm completeness only when the affected verifier binary, contract, or
verification wrapper was actually buildable/reachable and rejects, panics on,
or fails to compose a canonical honest artifact. A producer failure and a source
fragment fixed before the first compiling verifier are not verifier
completeness failures. Likewise, canonicalization or field-representation
hardening is implementation-only unless an exact verifier consumer distinguishes
the old representation in a rejecting or accepting predicate.

Do not discard a concrete verifier defect merely because the affected emitted
source, binary, contract, or boundary is not deployed or called. Report it
separately as a **latent finding** when the violated verifier boundary and exact
activation condition are established, but do not assign production severity or
imply a deployed acceptance path. A generator template without emitted verifier
code is implementation history; an unused template with only a suspected risk
is a lead. Label reachable prototype/test verifiers by their actual consumer.

## Deliverable

Report the single boundary, artifacts/deployment, confirmed findings, leads,
closures, tables, and adjacent recursion/contract layers not reviewed. State
whether the result applies to source, generated output, compiled binary, deployed
bytecode, or some subset—never conflate them.

Keep the work authorized, source-local, read-only, and defensive. Do not produce
deployment payloads, forged proofs, live-chain probes, or operational attacks.
