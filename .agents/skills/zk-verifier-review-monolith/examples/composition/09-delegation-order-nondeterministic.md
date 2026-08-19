# Delegation data order depended on HashMap iteration

## Classification

- Confirmed historical multi-delegation completeness bug
- Fixed by: [`5c01391`](https://github.com/matter-labs/zksync-airbender/commit/5c01391c67be617c5da53506dc27ac15564203d8), PR [#54](https://github.com/matter-labs/zksync-airbender/pull/54)
- Vulnerable revision: `6a49503916f046d091e1f7134d80fe037ace8ec6`

## Failure

GPU proving unpacked delegation groups directly from hash maps while downstream composition expected ascending delegation-type order. Large, multi-type proofs intermittently paired data with the wrong circuit type.

## Impact and fix

Proof construction became nondeterministic and could fail only at realistic program scale. The fix sorts by delegation ID. Canonical participant order is part of the protocol whenever batching challenges, transcript framing, or verifier tables are positional.

## Regression

Randomize insertion order for several delegation types and require byte-identical ordered outputs and proofs.

```sh
git diff 6a49503916f046d091e1f7134d80fe037ace8ec6 5c01391c67be617c5da53506dc27ac15564203d8 -- gpu_prover/src/execution/prover.rs
```
