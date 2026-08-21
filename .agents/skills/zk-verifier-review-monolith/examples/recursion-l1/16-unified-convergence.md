# Unified recursion did not enforce terminal convergence

## Classification

- Confirmed historical terminal-statement soundness bug
- Boundary: valid intermediate unified-recursion proof → artifact eligible for final verification/settlement
- Component: proof-family count and security-level-specific convergence policy
- Security character: an intermediate recursion state was accepted as a terminal state
- Fixed by: [`3e53f3f`](https://github.com/matter-labs/zksync-airbender/commit/3e53f3f3ac68fed1fbbcffbf28d4fcc425bd22e3), PR [#329](https://github.com/matter-labs/zksync-airbender/pull/329)
- Vulnerable revision: `bd71d8cef62bde7eb72ea22d353df0c41d551663`

## Boundary context

Unified recursion progressively combines proof families. A proof at an intermediate family count can be cryptographically valid and useful as input to another recursion step without being the terminal artifact authorized for export or settlement. The required terminal count depends on the trusted security-level model; historically the relevant policies converged differently (for example, one family at security 80 and two at security 100).

Acceptance therefore needs two independent predicates:

```text
verify the current unified recursion proof
require proof_family_count == terminal_count(trusted_security_level)
```

The first proves correctness of the current node. The second establishes that the requested workflow has finished.

## Failure

Unified verification accepted any proof valid in that recursion layer without checking whether its family-proof count had reached the terminal shape required by the selected security level. In particular, a partially compressed proof could pass the same verifier used for a final target.

## Adversarial flow

1. Stop recursive aggregation at a valid pre-terminal unified proof.
2. Package that intermediate proof as the final unified artifact.
3. Supply metadata consistent enough to select unified verification.
4. The recursive verifier confirms the intermediate node's algebraic validity.
5. No trusted-policy check asks whether more families must still be combined.
6. The wrapper returns final success for an unfinished recursion chain.

This does not mean the intermediate proof is cryptographically invalid. It means its proven statement is insufficient for the terminal consumer.

## Impact and fix

A partially compressed intermediate artifact could be accepted by the CLI as a
final verification artifact. The fix computes the proof-family count, maps the
trusted security level to its declared terminal shape, and rejects unified
targets that have not converged. The historical path does not establish an L1
settlement consumer, so settlement impact is conditional rather than claimed.

The terminal predicate belongs near the final acceptance boundary. Relying only on a producer loop to continue recursion is insufficient because artifacts can be submitted directly or workflows can be interrupted.

## Regression

- For every supported security level, reject every pre-terminal family count and accept only the declared converged count.
- Test valid intermediate proofs, not merely malformed encodings, to prove the policy check is independent of cryptographic validity.
- Reject over-terminal or structurally impossible counts as well as under-terminal counts.
- Apply the invariant to CLI verification, continuation, recursive binary handoffs, and L1 export/deployment paths.
- Require an explicit terminal-count rule and tests whenever a new security level or proof family is added.

## Reproduction evidence

```sh
git diff bd71d8cef62bde7eb72ea22d353df0c41d551663 3e53f3f3ac68fed1fbbcffbf28d4fcc425bd22e3 -- tools/cli/src/prover_utils.rs
```
