# Memory permutation PoW was hardcoded to zero

## Classification

- Confirmed historical Sec100 security-budget implementation gap
- Fixed by: [`06f6c11`](https://github.com/matter-labs/zksync-airbender/commit/06f6c117dcc039100c6e7cbcc0c5f7db90f0b258), PR [#330](https://github.com/matter-labs/zksync-airbender/pull/330)
- Vulnerable revision: `9aa915265f51f7ac3749681a4d8303fd3fb3c900`
- Reachability: Sec80 required 0 bits; a claimed Sec100 composition required 19

## Failure

`MEMORY_DELEGATION_POW_BITS` remained an inert zero despite the memory/delegation permutation challenge ranging over up to `2^40` elements in a roughly 123-bit field with additional error allowance.

## Impact and fix

The algebraic collision term could not meet a 100-bit target without grinding. The fix derives `max(0, target - (field_bits - element_log - margin))`, single-sources the element bound from timestamp constants, and makes security features mutually exclusive.

## Regression

Recompute expected bits independently for every supported target and maximum element count; assert prover, Rust verifier, recursion binary, and generated constants agree.

```sh
git diff 9aa915265f51f7ac3749681a4d8303fd3fb3c900 06f6c117dcc039100c6e7cbcc0c5f7db90f0b258 -- verifier_common/src/lib.rs full_statement_verifier/src/unrolled_proof_statement.rs
```
