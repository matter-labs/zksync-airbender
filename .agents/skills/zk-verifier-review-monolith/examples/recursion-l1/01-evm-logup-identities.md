# Generated EVM verifier omitted all LogUp identity checks

## Classification

- Confirmed soundness bug in the runnable `av_large_field` generated/test contract
- Boundary: generated GKR proof acceptance → lookup-valid circuit statement in the two-transaction Foundry consumer
- Component: terminal output checks in `GkrVerifier`
- Verifier anchor: generated `verifier_evm/src/templates/gkr.sol` contract exercised by the Foundry consumer
- Security character: three lookup arguments were reduced through GKR but never required to close
- Fixed by: [`bf9bd04`](https://github.com/matter-labs/zksync-airbender/commit/bf9bd04f2ac916eb8e65603cdba72f563b98351f)
- Vulnerable revision: `33f2685b8e602eec323c4e470729db09e433f060`

No production deployment or settlement consumer is established by this history;
the finding applies to the generated contract exercised by the branch's Foundry
two-transaction harness.

## Boundary context

GKR proves that circuit layers correctly transform base inputs into output polynomials. It does not automatically assert that every output represents a valid terminal statement. The unified circuit exported ten output columns: memory permutation pair, three LogUp numerator/denominator pairs, and inits/teardowns pair.

For each lookup family, the 16 remaining boundary evaluations represent rational contributions. The verifier must combine them and require the rational sum to be zero. This is the lookup analogue of checking that the final memory permutation products match.

## Intended terminal contract

For each of the three lookup output pairs:

```text
sum = Σ_{j=0}^{15} numerator[j] / denominator[j]
require every denominator product is nonzero
require sum == 0
```

The implementation may accumulate one fraction without inversions:

```text
acc_num' = acc_num * d + n * acc_den
acc_den' = acc_den * d
require acc_num == 0 and acc_den != 0
```

These checks occur after GKR has authenticated the output evaluations and before proof exhaustion/registry success.

## Failure

The EVM contract checked the memory permutation identity but never evaluated any of the three LogUp terminal identities. It parsed and used the output numerator/denominator values as GKR claims, proving that they came from the circuit computation, yet accepted regardless of whether their rational sums were zero.

GKR consistency is not lookup validity: a circuit can correctly compute a nonzero “error output.” Without the final zero condition, that error is merely authenticated rather than rejected.

## Adversarial flow

1. Construct a witness with a lookup multiset inconsistency.
2. Let the GKR circuit honestly propagate that inconsistency into one or more nonzero LogUp output pairs.
3. Prove all layer reductions and base openings correctly.
4. Pass the separately implemented memory permutation identity.
5. Reach contract success because no control-flow edge checks the lookup outputs.

This is a bounded false-statement flow: the prover need not break Sumcheck, WHIR, or Merkle binding; it exploits an omitted terminal predicate.

## Impact and fix

The generated verifier could accept proofs whose 16-bit, timestamp, or generic
lookup argument did not balance. That invalidates range checks and table
membership relied on by the machine circuit within this test-contract boundary.

The fix records the output-evaluation calldata base, accumulates each of the three fixed output pairs as a rational sum, rejects zero denominators, and invokes the checks before `assert_proof_empty` and registry notification.

For every recursive/L1 boundary, inventory outputs as: checked locally, exported to another authenticated consumer, or intentionally public. An output that is merely parsed and transcript-bound is not semantically constrained.

## Regression

- Mutate each lookup family independently while leaving memory products valid.
- Exercise nonzero numerator with valid denominators and a zero-denominator case.
- Keep the GKR layer proof internally consistent so the terminal check is the rejecting edge.
- Derive output offsets from the artifact or assert the fixed ten-column layout.
- Confirm the registry/settlement success path is unreachable after any identity failure.

## Reproduction evidence

```sh
git diff 33f2685b8e602eec323c4e470729db09e433f060 bf9bd04f2ac916eb8e65603cdba72f563b98351f -- verifier_evm/src/templates/gkr.sol
```
