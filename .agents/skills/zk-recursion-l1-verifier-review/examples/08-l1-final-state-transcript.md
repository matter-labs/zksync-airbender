# L1 transcript omitted final registers, PC, and timestamp

## Classification

- Confirmed historical L1 public-state binding bug
- Fixed by: [`f15c643`](https://github.com/matter-labs/zksync-airbender/commit/f15c64359f852837c9ffe4fe368a62f34b6e3c89)
- Vulnerable revision: `b75be7bbecc17860dac85a6d875887a7e7fb1396`

## Failure

Merged-and-packed L1 proving re-derived external memory challenges without absorbing the final register values and access timestamps or final PC/timestamp, although those values supply the public machine-state contribution used to close the permutation.

## Impact and fix

The memory challenge did not bind the public terminal state whose reads/writes it authenticated. The fix serializes 32 register triples and the final PC/timestamp triple before setup and argument challenge derivation.

## Regression

Mutate each terminal-state limb while preserving commitments and require a different seed and failed closure.

```sh
git diff b75be7bbecc17860dac85a6d875887a7e7fb1396 f15c64359f852837c9ffe4fe368a62f34b6e3c89 -- prover/src/gkr/prover/mod.rs
```
