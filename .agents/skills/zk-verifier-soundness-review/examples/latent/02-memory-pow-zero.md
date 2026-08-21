# Memory permutation PoW would have been zero in a Sec100 full-statement verifier

## Classification

- Confirmed latent higher-security budget implementation defect
- Component: external memory/delegation permutation challenge derivation
- Budget term: Schwartz–Zippel collision probability under a bounded total element count, plus retry grinding
- Reachability: the library exposed a `security_100` feature, but every full-statement wrapper and generated binary still selected Sec80 component verifiers; no working Sec100 full-statement proof path was established
- Activation condition: import/generate Sec100 component verifiers and expose a matching full-statement caller or binary without first replacing the zero constant
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

`MEMORY_DELEGATION_POW_BITS` remained an inert zero/TODO independent of security level. If the full-statement verifier were instantiated for Sec100, the external permutation challenges could therefore be retried without the additional 19-bit per-attempt work required by the adopted target calculation.

This was consumed in both `unified_circuit_statement.rs` and
`unrolled_proof_statement.rs` after the memory caps and global accumulators had
been collected. It was not an unused prover parameter: the verifier passed the
zero directly to `GKRExternalChallenges::draw_from_transcript_seed`.

The source looked closer to reachable than it was. `full_statement_verifier`
exposed a `security_100` feature, and `tools/cli` attempted to forward Sec100.
However, all full-statement wrapper functions hardcoded `*_sec_80` component
verifiers, `tools/gkr_verifier` declared only `fsv_*_sec_80` binaries, and the
`gkr_test.sh` full-statement step always built the Sec80 binary. The CLI's Sec100
feature also referenced the commented-out/nonexistent
`execution_utils/verifier_100` feature, so it did not supply a working alternate
route. No matching Sec100 full-statement producer/verifier artifact was found.

Accordingly, this is not evidence that a historical verifier accepted false
proofs below an active 100-bit claim. It is an exact latent defect that would
have activated as soon as the already-advertised library mode gained matching
Sec100 component verifiers.

The full-statement verifier also used an ad hoc `< 2^40` assertion instead of
coupling every accepted element bound to the policy constant used in the
derivation.

## Quantitative impact

With the adopted conservative accounting:

```text
Sec80 target: base 81 bits, no local shortfall
Sec100 target: base 81 bits, 19-bit local shortfall before grinding
latent configured PoW: 0
fixed configured PoW: 19 for Sec100
```

It would be wrong to claim the historical verifier had exactly 81 bits from this example alone. The conclusion is narrower and conditional: once activated as a Sec100 full-statement path, the zero-PoW memory/delegation term would not have met the design's 100-bit retry-cost target under its own stated bound.

## Impact and fix

The prospective higher-security configuration omitted its required memory/delegation grinding. The fix defines the field-size floor, a `MAX_PERMUTATION_ELEMENTS_LOG2 = 40` policy, conservative margin, and derived PoW function before a matching Sec100 full-statement artifact was hooked up; it replaces the unrolled verifier's literal bound with that shared constant and makes security features mutually exclusive. The unified verifier retained the numerically identical literal `< 2^40` check at the fixing revision, so its accepted bound was correct but still exposed to future drift.

Soundness constants must form a closed triangle: theorem formula, verifier-enforced runtime bound, and prover/verifier/generated PoW schedule. A comment or prover limit alone cannot support the budget.

## Regression

- Independently recompute 0 and 19 bits from the policy inputs.
- Test element counts just below and at `2^40` symbolically/through bounded helper tests rather than allocating them.
- Assert prover, Rust verifier, recursion binary, generated constants, and selected feature agree.
- Reject simultaneous Sec80/Sec100 features and record the default feature policy.
- Include this event in a whole-system error ledger rather than adding “19 bits” directly to unrelated advertised bits.

## Reproduction evidence

```sh
git diff 9aa915265f51f7ac3749681a4d8303fd3fb3c900 06f6c117dcc039100c6e7cbcc0c5f7db90f0b258 -- verifier_common/src/lib.rs full_statement_verifier/src/lib.rs full_statement_verifier/src/unrolled_proof_statement.rs
```
