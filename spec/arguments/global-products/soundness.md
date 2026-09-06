# GP-SND: Global-product soundness

> States what the standalone product comparison proves. Memory consistency and other
> meanings assigned to the tuples are obligations of the calling modules.

## Imports

- `arguments/global-products/relation.md`
- `arguments/global-products/verifier.md`

## Baseline

The check is a multivariate polynomial fingerprint. For challenge vector
`χ = (β, α_0, …, α_(d-1))`, define

`G(χ) = Π_(r ∈ R) (β + Σ_j α_j r[j]) − Π_(w ∈ W) (β + Σ_j α_j w[j])`.

Unique factorization of monic linear polynomials implies that `G` is the zero
polynomial exactly when `R` and `W` are equal as tuple multisets. This is the
multivariate form of the polynomial fingerprint described in [Thaler, *Proofs,
Arguments, and
Zero-Knowledge*](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf).

## Requirements

### REQ-GP-SND-001 — Tuple fingerprint bound

Let `m = max(|R|, |W|)`. If the tuple multisets differ, `G` is nonzero and has total
degree at most `m`. Sampling every coordinate of `χ` independently and uniformly from
`E` therefore gives, by Schwartz–Zippel,

`Pr[P_R = P_W] ≤ m / |E|`.

The calling soundness budget supplies a bound on `m` and charges this term for every
independently sampled product instance.

### REQ-GP-SND-002 — Zero factors

Do not add a nonzero-factor acceptance condition. A challenge that makes one or both
products zero is simply an evaluation point at which `G` may vanish and is
already counted by `REQ-GP-SND-001`.

## Output

- **OUT-GP-SND-001 — Multiset soundness.** Under `REQ-GP-SND-001..002`, acceptance
  implies `R = W` except with probability at most `m / |E|` per independently sampled
  product instance.

## Metadata

| ID | Authority | Activation | Depends / discharged by | Source |
|---|---|---|---|---|
| `REQ-GP-SND-001` | normative | one product instance | `REQ-GP-REL-001..002`, `REQ-GP-REL-004..005` | multivariate Schwartz–Zippel applied to the tuple fingerprint; [Thaler, Proofs, Arguments, and Zero-Knowledge](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf), polynomial fingerprinting |
| `REQ-GP-SND-002` | normative | one product instance | `REQ-GP-SND-001`, `REQ-GP-VER-005` | roots of the fingerprint-difference polynomial |
| `OUT-GP-SND-001` | normative | accepted product instance | `REQ-GP-SND-001..002` | derived from the multivariate tuple fingerprint |
