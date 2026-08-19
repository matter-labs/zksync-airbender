# Lookup and WHIR batching challenges lacked derived grinding

## Classification

- Confirmed historical higher-security parameterization gap
- Fixed by: [`bc526de`](https://github.com/matter-labs/zksync-airbender/commit/bc526de6cb89840e8b8bfd67c5aab5ffecc04585), PR [#331](https://github.com/matter-labs/zksync-airbender/pull/331)
- Vulnerable revision: `06f6c117dcc039100c6e7cbcc0c5f7db90f0b258`
- Reachability: derived bits are zero for Sec80; necessary for the Sec100 design

## Failure

Lookup challenges and the WHIR base-oracle batching challenge were squeezed without PoW derived from the lookup identity degree or the number of batched polynomials. A nominal higher-security configuration therefore omitted these algebraic/proximity loss terms.

## Impact and fix

The final computational soundness could fall below the advertised target even if WHIR query bits alone were sufficient. The fix derives per-circuit lookup and batched-proximity grinding, places nonces in the proof, and mirrors verification and skip-first-word transcript semantics.

## Regression

For each circuit, independently compute lookup degree, batched-oracle count, target bits, and required PoW; include all terms in a union-bound worksheet.

```sh
git diff 06f6c117dcc039100c6e7cbcc0c5f7db90f0b258 bc526de6cb89840e8b8bfd67c5aab5ffecc04585 -- prover/src/gkr/prover_config/pow_bits.rs verifier_generator/src/gkr/mod.rs
```
