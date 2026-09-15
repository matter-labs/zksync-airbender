# Recursive Statement and Chain Binding

## Purpose

A recursive proof is useful to a relying party only when its authenticated
statement is the exact program, verifier stage, execution output, and terminal
policy the relying party requested. Cryptographic verification of an otherwise
valid recursive proof does not establish that authorization by itself.

## Supported chain designs

Recover the selected design rather than assuming one:

- A fixed recursion chain may embed the exact predecessor verifier identity in
  each outer verifier program or verifier key.
- A branching or tree design may authenticate an allowed predecessor set and
  the rule selecting each transition.
- A modular design may carry an explicit chain accumulator in authenticated
  public output and update it at each distinct verifier stage.

All three can be sound. The audit question is whether final acceptance fixes the
complete predecessor relation to the originally requested program and output.

## Inductive acceptance contract

### Base

- Base mode and base program/setup identity come from trusted policy, not a
  proof-supplied tag.
- Successful program termination and the application output are authenticated.
- Any auxiliary chain state has its required genesis value.
- The initial chain identity binds every base-program parameter the next layer
  relies upon, using the target version's exact serialization and hash.

### Recursive step

Treat each verifier program as one indivisible acceptance step:

1. Verify the complete prior proof under the verifier program/key, stage, proof
   type, and security policy selected by trusted context.
2. Check every terminal argument produced by that proof, including each local
   lookup/table or permutation-style output required by the selected statement.
3. Complete and close global memory/state using the authenticated machine state,
   execution context, application output, and other public values.
4. Validate the prior chain link, preimage, or predecessor identity using only
   values authenticated by the successful proof and state closure.
5. Derive the current verifier-stage identity from its trusted program/setup and
   accepted termination context.
6. Append, branch, or propagate that identity according to the target version's
   exact chain rule.
7. Export the resulting chain and application output through authenticated
   public state, or compare them with the trusted final policy.

Check every base, continuation, branch, no-op, and stage-transition path. An
equality between proof metadata and another proof-supplied copy does not replace
an equality against authenticated verifier output or a trusted embedded
identity.

### Terminus

- Final acceptance binds the requested base program, every required verifier
  stage, target mode, security policy, and application output.
- The final consumer checks the authenticated chain terminus or an equivalent
  fixed-verifier authorization, rather than accepting any valid recursive proof.
- A separate authenticated convergence rule is enforced whenever the identity
  chain does not itself encode recursion progress or repeated stages.
- Truncation, stage substitution, omitted branches, replay, and unfinished
  aggregation cannot satisfy the terminal policy.

## Identity is not necessarily progress

The recursion proof nesting authenticates that each outer verifier executed its
immediate predecessor. A public identity chain may instead record only distinct
program/setup transitions and may intentionally propagate unchanged across
repeated uses of the same verifier. Do not infer a recursion-step count from the
identity chain unless the target construction explicitly commits to it.

Recover the actual termination mechanism from the selected version. It may be
an authenticated proof-shape predicate, counter, final marker, branch root, or a
chain update that records every repetition. The verifier or relying party must
enforce that mechanism against trusted target policy after authenticating the
relevant state. Producer orchestration that merely decides when to stop is not
an acceptance check.

## Bounded provenance expansion

Follow statement identity through the adjacent components needed to close the
selected boundary: verifier programs and keys, setup construction, authenticated
outputs, artifact loading, wrapper or CLI policy, and the immediate final
consumer. This expansion is mandatory for identity provenance but does not
authorize an audit of unrelated protocol internals.

For Airbender targets, recover the version-specific rule from the checked-out
architecture document, recursion-chain implementation, verifier binaries,
full-statement verifier, and final wrapper or settlement consumer. Treat design
documents as obligations and verifier behavior as evidence.

## Required chain table

| Stage/branch | Trusted expected identity | Prior proof and terminal predicates | Authenticated prior chain source | Update/propagation rule | Authenticated output | Terminal consumer rule |
|---|---|---|---|---|---|---|

No row is closed merely because the recursive proof verifies. State exactly how
that successful proof is tied to the requested original program and how the
system proves that recursion has reached an authorized terminal state.
