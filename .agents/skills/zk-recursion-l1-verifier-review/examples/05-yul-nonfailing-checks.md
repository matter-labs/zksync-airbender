# Yul Sumcheck failures were stored but never rejected

## Classification

- Confirmed historical fail-open EVM verifier bug
- Boundary: computed Sumcheck/GKR consistency predicates → contract acceptance
- Component: generated per-round and terminal point checks
- Security character: core verification equations had no rejecting control-flow edge
- Fixed by: [`4f8d993`](https://github.com/matter-labs/zksync-airbender/commit/4f8d993a7c3fbea5e52d4b4ef5cb1e3ad1a316e4)
- Vulnerable revision: `16a5cebf46a3ffa378a4dc893a302d33a359d9d7`

## Boundary context

Each Sumcheck round must enforce that the incoming claim equals the round polynomial's Boolean sum, accounting for the current equality-polynomial scale. After all rounds, the verifier must evaluate/batch the actual layer gates at the sampled point and require equality with the final Sumcheck claim.

In Yul, computing a nonzero difference has no effect unless control flow reverts or the value is incorporated into a subsequently enforced equation. Stores used for scratch/cache state are not assertions.

## Intended acceptance contract

For every round:

```text
round_error = claim - eq_scale * (g(0) + g(1)) mod P
if round_error != 0: revert
claim = g(r)
```

For every layer terminal check:

```text
point_error = final_claim - eq_scale * batched_gate_evaluation(point) mod P
if point_error != 0: revert
```

All failures must dominate the final success/registry path.

## Failure

The generated verifier computed these differences into a variable named `dummy_check` and stored them at `GKR_CIRCUIT_CACHE_PTR`. No later branch loaded the value, incorporated it into an authenticated claim, or reverted on nonzero.

The contract continued updating transcript challenges and claims regardless of whether `claim == g(0)+g(1)` or the terminal gate batch matched. Some generated point checks were also incomplete/stale, compounding the fail-open behavior.

## Adversarial flow

1. Supply arbitrary round coefficients inconsistent with the incoming claim.
2. Contract computes a nonzero `dummy_check` and writes it to scratch memory.
3. Continue using transcript-derived `r` to form a new claim from the arbitrary polynomial.
4. At the layer endpoint, supply evaluations inconsistent with the gate relation.
5. Store another nonzero dummy value without rejection.
6. Complete remaining parser/WHIR checks and reach success.

This bypass does not require exploiting probability or breaking a commitment: the logical predicates existed only observationally.

## Impact and fix

Core Sumcheck and GKR terminal verification was unenforced, so invalid layer reductions could pass the on-chain boundary. The fix replaces dummy stores with immediate `if error { revert(0,0) }` checks and regenerates the complete point-gate batches/order.

For generated/Yul verifiers, build a control-flow evidence table for every predicate: computation site, nonzero representation, branch/revert, and dominance of every success exit. Variable names such as `check`, assertions in comments, and unused stores provide no security.

## Regression

- Corrupt every coefficient of every round independently and require revert at that layer.
- Corrupt each terminal point claim/gate output independently.
- Verify failure before registry calls, events, or success returns.
- Inspect compiled bytecode/control flow so optimizer behavior cannot eliminate or bypass checks.
- Add mutation testing that deletes each revert and requires a regression to fail.

## Reproduction evidence

```sh
git diff 16a5cebf46a3ffa378a4dc893a302d33a359d9d7 4f8d993a7c3fbea5e52d4b4ef5cb1e3ad1a316e4 -- verifier_evm/circuit.yul verifier_evm/gkr.sol
```
