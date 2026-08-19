# Cache-dependency evaluations followed the batching challenge

## Classification

- Confirmed historical Fiat-Shamir ordering bug
- Component: GKR layer-claim batching
- Fixed by: [`4e3142e`](https://github.com/matter-labs/zksync-airbender/commit/4e3142ead72767b21139bcaa2f2acb1da6944739)
- Vulnerable revision: `bf9bd04f2ac916eb8e65603cdba72f563b98351f`

## Failure

The prover absorbed `new_claims`, drew `next_batching_challenge`, and only then absorbed extra prover-provided evaluations required by cache relations. The challenge used to combine the next layer was independent of those values.

## Impact and fix

An adversarial prover retained freedom in cache-dependency claims after learning the batching coefficient. The fix forms one canonical `new_claims ++ extras` message, absorbs it, then draws. The EVM generator required a corresponding fix because two absorbs are not equivalent to one for this transcript.

## Regression

Generate a layer with cache-only dependencies and assert every extra evaluation appears before the first dependent batching squeeze.

```sh
git diff bf9bd04f2ac916eb8e65603cdba72f563b98351f 4e3142ead72767b21139bcaa2f2acb1da6944739 -- prover/src/gkr/prover/sumcheck_loop/mod.rs
```
