# Multilinear coefficients were built in the wrong bit order

## Classification

- Confirmed historical MLE-to-Reed-Solomon ordering defect in a pre-assembly prover
- Component: stage-1 base-oracle encoding for WHIR
- Claim-chain location: Boolean-hypercube evaluations → multilinear coefficients → RS codeword commitment
- Security character: latent; the enclosing GKR prover still ended in an unconditional `todo!()` and could not emit a proof
- Fixed by: [`619c6ab`](https://github.com/matter-labs/zksync-airbender/commit/619c6ab4f291f7df2d400edd0389a16c4452dae3)
- Vulnerable revision: `db36e5d771862d22a4538ee9699cfb9b4d8f0451`
- Activation condition: completion of `prove_configured_with_gkr` without independently correcting the stage-1 variable-order seam

## Protocol context

GKR treats a trace column as a multilinear polynomial whose Boolean-hypercube enumeration follows a specific variable order. WHIR commits a Reed-Solomon encoding derived from that polynomial's monomial coefficients. The hypercube-to-coefficient transform and domain encoder used opposite enumeration conventions unless the input was bit-reversed first.

A variable permutation preserves some symmetric test vectors and every vector's length, yet changes evaluation at a general point. The GKR-to-PCS seam therefore needs an explicit variable-order contract.

## Intended handoff relation

For trace evaluations `evals[b_0,...,b_{n-1}]` and GKR point `r`:

```text
ordered = bitreverse_hypercube_enumeration(evals)
coeffs  = multilinear_hypercube_evals_to_coeffs(ordered)
codeword = RS_encode(coeffs)

opening claim at r == evaluate_original_MLE(evals, r under GKR variable order)
```

Every fold order, equality polynomial, and query-domain mapping must use the same bit convention.

## Failure

Stage 1 passed the original evaluation vector directly into the coefficient transform without first bit-reversing its enumeration. The resulting coefficients represented the same table under a different variable permutation from the one used by GKR and WHIR's domain layout.

Field arithmetic, Merkle commitments, and low-degree encoding could all be individually correct while proving an opening of the wrong polynomial.

## Failure flow

1. Choose a nonsymmetric column where variables have distinct effects.
2. Interpret its array index bits in GKR order to derive a base-layer claim.
3. Convert the same array to monomial coefficients under the transform's opposite bit order.
4. Commit the RS codeword of the permuted MLE.
5. Attempt to prove the GKR opening against that commitment.
6. Fail at batched opening/fold consistency, or silently prove a permuted statement if every verifier-side handoff repeats the same mapping.

At this revision `prove_configured_with_gkr` unconditionally terminated with
`todo!()` after invoking WHIR, so this defect did not create an additional
accepted or rejected proof path. It was nevertheless a concrete latent defect:
once proof assembly returned normally, the committed polynomial would disagree
with the GKR claim unless this ordering seam was corrected. A deployed
soundness claim also requires checking the verifier's evaluation-point
coordinate order independently.

## Impact and fix

The committed codeword did not represent the multilinear polynomial named by the incoming GKR claims. The fix calls `bitreverse_enumeration_inplace` before hypercube-evaluation-to-coefficient conversion for each polynomial.

Ordering is part of the polynomial identity. Document it at every transform boundary and test with deliberately asymmetric basis functions rather than random vectors alone.

## Regression

- Use an MLE such as `Σ_i distinct_weight_i * x_i` so every variable permutation is observable.
- Compare all Boolean evaluations and several random-point evaluations before and after RS encoding.
- Exercise LSB-first and MSB-first GKR configurations explicitly.
- Verify CPU/GPU coefficient and codeword parity.
- Assert the GKR opening point coordinate order matches the WHIR tensor/fold order.

## Reproduction evidence

```sh
git diff db36e5d771862d22a4538ee9699cfb9b4d8f0451 619c6ab4f291f7df2d400edd0389a16c4452dae3 -- prover/src/gkr/prover/stages/stage1.rs
```
