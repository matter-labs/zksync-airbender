# Memory permutation PoW was hardcoded to zero

## Classification

- Confirmed historical higher-security budget implementation gap
- Component: external memory/delegation permutation challenge derivation
- Budget term: Schwartz–Zippel collision probability under a bounded total element count, plus retry grinding
- Reachability: Sec80 required zero derived bits; the intended Sec100 policy required 19
- Fixed by: [`06f6c11`](https://github.com/matter-labs/zksync-airbender/commit/06f6c117dcc039100c6e7cbcc0c5f7db90f0b258), PR [#330](https://github.com/matter-labs/zksync-airbender/pull/330)
- Vulnerable revision: `9aa915265f51f7ac3749681a4d8303fd3fb3c900`

## Security context

All chunks/delegations share random linearization challenges for a global permutation equality. For at most `n` compressed factors, a nonzero product-difference polynomial has total degree at most `n` in the independently sampled challenge variables, giving a Schwartz–Zippel term bounded by approximately `n / |F|`.

The fixing policy used conservative log bounds:

```text
challenge field: BabyBear quartic, floor(log2 |F|) = 123
maximum total permutation elements: n < 2^40
raw algebraic margin: 123 - 40 = 83 bits
explicit conservative slack: 2 bits
budgeted base security: 81 bits
```

The `2^40` policy bound was deliberately hardcoded and runtime-enforced; it was not derived from timestamps because delegation elements can grow independently of cycle timestamps.

## Intended grinding derivation

Under the repository's retry-cost model:

```text
base_bits = field_bits_floor - max_elements_log2 - margin
required_pow = max(0, target_bits - base_bits)

Sec80:  max(0, 80 - 81)  = 0
Sec100: max(0, 100 - 81) = 19
```

This is one local budget term. The final system budget still needs union bounds, other algebraic/proximity failures, hash assumptions, and an explicit adversarial work model.

## Failure

`MEMORY_DELEGATION_POW_BITS` remained an inert zero/TODO independent of security level. For the Sec100 design, the external permutation challenges could therefore be retried without the additional 19-bit per-attempt work assumed by the target calculation.

The full-statement verifier also had only an ad hoc `< 2^40` assertion instead of coupling its accepted element bound to the same policy constant used in the derivation.

## Quantitative impact

With the adopted conservative accounting:

```text
Sec80 target: base 81 bits, no local shortfall
Sec100 target: base 81 bits, 19-bit local shortfall before grinding
vulnerable configured PoW: 0
fixed configured PoW: 19 for Sec100
```

It would be wrong to claim the whole verifier had exactly 81 bits from this example alone. The conclusion is narrower: the memory/delegation collision term did not meet the design's 100-bit retry-cost target under its own stated bound.

## Impact and fix

The higher-security configuration omitted its required memory/delegation grinding. The fix defines the field-size floor, a single `MAX_PERMUTATION_ELEMENTS_LOG2 = 40` policy, conservative margin, and derived PoW function; the full verifier enforces the same element ceiling and security features become mutually exclusive.

Soundness constants must form a closed triangle: theorem formula, verifier-enforced runtime bound, and prover/verifier/generated PoW schedule. A comment or prover limit alone cannot support the budget.

## Regression

- Independently recompute 0 and 19 bits from the policy inputs.
- Test element counts just below and at `2^40` symbolically/through bounded helper tests rather than allocating them.
- Assert prover, Rust verifier, recursion binary, generated constants, and selected feature agree.
- Reject simultaneous Sec80/Sec100 features and record the default feature policy.
- Include this event in a whole-system error ledger rather than adding “19 bits” directly to unrelated advertised bits.

## Reproduction evidence

```sh
git diff 9aa915265f51f7ac3749681a4d8303fd3fb3c900 06f6c117dcc039100c6e7cbcc0c5f7db90f0b258 -- verifier_common/src/lib.rs full_statement_verifier/src/unrolled_proof_statement.rs
```
