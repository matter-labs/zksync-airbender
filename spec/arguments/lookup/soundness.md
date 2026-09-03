# Lookup soundness

## Baseline

The relation follows [Haböck, *Multivariate lookups based on logarithmic
derivatives*](https://eprint.iacr.org/2022/1530) and [Papini and Haböck,
*Improving logarithmic derivative lookups using
GKR*](https://eprint.iacr.org/2023/1284).

## Production deviations

- Three separately checked channels: generic, 16-bit, and timestamp.
- Row compression by `alpha` before additive challenge `beta`.
- Lookup-challenge grinding.
- Fixed 16-way terminal accumulation in the generated verifier.
- Virtual range setups are verifier-derived instead of committed.

## Requirements

- **`REQ-LOOKUP-SND-001` — Characteristic bound.** For each logarithmic-derivative
  identity, the number of accumulated fractions is strictly less than the
  characteristic of the challenge field, or a cited replacement theorem is used.
- **`REQ-LOOKUP-SND-002` — Pole rejection.** The terminal denominator is nonzero.
  This is the pole check; challenge grinding does not replace it.

## Open obligations

- **`GAP-LOOKUP-SND-001` — Row compression.** State the soundness bound for
  compressing one lookup invocation as a function of row width and row count.
- **`GAP-LOOKUP-SND-002` — Fraction bound.** For every supported circuit, state the
  maximum number of fractions accumulated in each channel and establish that it is
  smaller than the BabyBear characteristic.

## Assessed deviation

- **`DEV-LOOKUP-001` — Unenforced characteristic bound.** The assessed implementation
  derives lookup PoW from the cleared-identity degree but does not assert the fraction
  bound in `REQ-LOOKUP-SND-001`.
