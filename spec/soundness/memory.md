# GP-SND: Global-product soundness

> States what the standalone product comparison of the
> [common memory relation](../memory/common.md) proves. Memory consistency and
> every other meaning assigned to the tuples are obligations of the calling modules.
> This module is imported material: it bounds the generic fingerprint only, and does
> not yet compose with [accounting.md](accounting.md).

## Imports

- [memory/common.md](../memory/common.md)

## Baseline

The check is a multivariate polynomial fingerprint. Let
`e = (tag(e), x_e) ∈ Tags × E^d`, where `Tags` embeds injectively into `E`. For
challenge vector `χ = (β, α_0, …, α_(d-1))`, define

```text
L_χ(e) = β + tag(e) + Σ_j α_j x_e[j]
G(χ) = Π_(r ∈ R) L_χ(r) − Π_(w ∈ W) L_χ(w)
```

Each factor is monic in `β`. Injective tags and unique factorization of linear
polynomials imply that `G` is the zero polynomial exactly when `R` and `W` are equal
as event multisets. The tag is a fixed constant term, not another sampled coordinate.
This is the multivariate form of the polynomial fingerprint described in [Thaler,
*Proofs, Arguments, and
Zero-Knowledge*](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf).

## Requirements

### REQ-GP-SND-001 — Tuple fingerprint bound

Let `m = max(|R|, |W|)`. If the event multisets differ, `G` is nonzero and has total
degree at most `m`. Sampling every coordinate of `χ` independently and uniformly from
`E` therefore gives, by Schwartz–Zippel,

```text
Pr[P_R = P_W] ≤ m / |E|
```

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

## Open boundary

- **GAP-GP-SND-001 — Memory-instance error term.** `REQ-GP-SND-001` is stated for one
  generic instance. Supply the concrete `m` and `|E|` of the memory instance selected
  by `GAP-MEM-003`, the number of independently sampled product instances per proof,
  and the union bound over them; then register that term in
  [accounting.md](accounting.md).
- **GAP-GP-SND-002 — Challenge-sampling uniformity.** `REQ-GP-SND-001` assumes every
  coordinate of `χ` is uniform and independent over `E`. The transcript relation that
  would discharge this is not specified in this branch of the specification, so the
  uniformity assumption is currently external.

## Metadata

- spec revision: draft
- implementation: TBD
- profile: all targets

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `REQ-GP-SND-001` | normative | one product instance | `REL-MEM-001..006`; `REL-MEM-008`; `GAP-GP-SND-001..002` | prose | multivariate Schwartz–Zippel applied to the tuple fingerprint; [Thaler, Proofs, Arguments, and Zero-Knowledge](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf), polynomial fingerprinting | — |
| `REQ-GP-SND-002` | normative | one product instance | `REQ-GP-SND-001`; `REL-MEM-001` | prose | roots of the fingerprint-difference polynomial | — |
| `OUT-GP-SND-001` | normative | accepted product instance | `REQ-GP-SND-001..002` | prose | derived from the multivariate tuple fingerprint | — |
| `GAP-GP-SND-001` | open | — | affects `REQ-GP-SND-001` and `OUT-GP-SND-001`; owner: human | — | no concrete multiset size, field, or instance count is bound to the memory instantiation yet | — |
| `GAP-GP-SND-002` | open | — | affects `REQ-GP-SND-001`; owner: human | — | challenge-sampling uniformity has no owning transcript relation in this branch | — |
