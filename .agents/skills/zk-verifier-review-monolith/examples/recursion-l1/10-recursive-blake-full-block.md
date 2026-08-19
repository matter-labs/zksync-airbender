# Recursive Blake leaf verifier mishandled one full block

## Classification

- Confirmed historical verifier-binary hash mismatch
- Fixed by: [`0e81150`](https://github.com/matter-labs/zksync-airbender/commit/0e81150273f40637cd926296139f254a2ac64957)
- Vulnerable revision: `62e23e7cb573251298e9cbb7852e80124fc2c0ba`

## Failure

When input length was an exact Blake2s block, the alternative-compression leaf verifier moved the last full block into final-block processing only if `num_full_rounds > 1`. A one-block input therefore kept both a full-round count and a full final block.

## Impact and fix

Recursive Merkle verification hashed exact-one-block leaves differently from the prover/native verifier. The fix uses `> 0`, ensuring the final block is processed exactly once with finalization semantics.

## Regression

Compare standard and alternative compression at lengths 0, one word below a block, exactly one block, and two blocks.

```sh
git diff 62e23e7cb573251298e9cbb7852e80124fc2c0ba 0e81150273f40637cd926296139f254a2ac64957 -- prover/src/definitions/leaf_inclusion_verifier/blake2s_for_everything_with_alternative_compression.rs
```
