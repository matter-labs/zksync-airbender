# WHIR batching zeroed every power but the first

## Classification

- Confirmed historical PCS batching implementation bug
- Component: GKR base-oracle claims → one WHIR polynomial/opening
- Claim-chain location: memory/witness/setup opening inventory → random linear combination
- Security character: missing-polynomial soundness if an accepting verifier shares the reduction; historical prover-only path otherwise yields verifier mismatch
- Fixed by: [`c9d8620`](https://github.com/matter-labs/zksync-airbender/commit/c9d8620d2f549781be154c6813264330b63b8a94)
- Vulnerable revision: `e0b57de405ba1e66dbc8da572e9ac73a8d266726`

## Protocol context

GKR terminates with many base-layer multilinear polynomial evaluations. WHIR proves them together by sampling a batching challenge `γ` after the base commitments and forming one polynomial and one claimed opening with coefficients `1, γ, γ², ...` in the canonical memory/witness/setup order.

The reduction is sound only if every promised opening appears with the same nonzero position-bound coefficient on the polynomial side and claim side. An item with coefficient zero is absent from the PCS theorem regardless of whether its commitment was parsed or transcript-bound.

## Intended batch relation

For committed polynomials `P_i` and claimed evaluations `v_i = P_i(z)`:

```text
B(X) = Σ_i γ^i * P_i(X)
b    = Σ_i γ^i * v_i
WHIR proves B(z) = b
```

The inventory is partitioned into memory, witness, and setup slices only for implementation efficiency; the power sequence must continue across slice boundaries.

## Failure

The code correctly materialized `total_base_oracles` powers and then explicitly filled `challenge_powers[1..]` with zero. Splitting that vector among memory, witness, and setup consequently assigned coefficient one to the first polynomial and zero to every remaining polynomial.

The WHIR reduction proved only the first opening. Later witness/setup claims could be changed without changing `B` or `b` in any implementation that used this batch construction for verification.

## Adversarial or failure flow

1. Commit all base oracles and draw `γ`.
2. Replace the intended power vector by `[1, 0, ..., 0]`.
3. Form the batched polynomial and claim solely from `P_0` and `v_0`.
4. Supply arbitrary or inconsistent claims for `P_1...P_n`.
5. Pass WHIR for `P_0` while the omitted openings remain unproved—if the accepting verifier uses the same zeroed reduction.

If the canonical verifier independently uses running powers, a proof from this honest-prover path fails instead. Because the historical diff is in prover code, an audit must establish verifier/generated-artifact parity before labeling a deployed false acceptance.

## Impact and fix

The base-opening batch collapsed to one item, defeating the intended GKR-to-PCS handoff or causing prover/verifier divergence. The fix removes the zero fill and retains the complete running-power vector before partitioning it among oracle classes.

Review batching with an explicit item ledger. Commitment absorption alone does not prove an opening; each item needs a nonzero coefficient, consistent ordering, and presence in the final PCS claim.

## Regression

- Mutate every base polynomial and claimed evaluation independently and require the batched polynomial/claim to change.
- Assert the coefficient vector equals `[1, γ, γ², ...]` across memory/witness/setup boundaries.
- Use at least one polynomial in every oracle class and more than one item per class.
- Compare prover, Rust verifier, generated verifier, and EVM inventory/order.
- Reject zero or accidentally repeated coefficients except for negligible challenge events explicitly covered by the soundness budget.

## Reproduction evidence

```sh
git diff e0b57de405ba1e66dbc8da572e9ac73a8d266726 c9d8620d2f549781be154c6813264330b63b8a94 -- prover/src/gkr/whir/mod.rs
```
