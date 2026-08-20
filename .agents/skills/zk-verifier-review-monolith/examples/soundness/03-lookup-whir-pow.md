# Lookup and WHIR batching challenges lacked derived grinding

## Classification

- Confirmed historical higher-security parameterization gap
- Component: lookup `alpha/gamma` and WHIR base-oracle batching challenge phases
- Budget terms: cleared LogUp identity degree and batched-proximity loss
- Reachability: derived bits were zero for Sec80; the Sec100 prover configuration was still incomplete at the fixing commit
- Fixed by: [`bc526de`](https://github.com/matter-labs/zksync-airbender/commit/bc526de6cb89840e8b8bfd67c5aab5ffecc04585), PR [#331](https://github.com/matter-labs/zksync-airbender/pull/331)
- Vulnerable revision: `06f6c117dcc039100c6e7cbcc0c5f7db90f0b258`

## Security context

Two early challenges had circuit-dependent losses not represented by the WHIR query schedule alone.

For LogUp, clearing all denominators yields a polynomial identity in lookup tuple-compression challenge `alpha` and additive shift `gamma`. The implementation conservatively bounded its degree as:

```text
D = total_fractions * max_tuple_width
base_lookup_bits = 123 - ceil(log2 D)
lookup_pow = max(0, target_bits - base_lookup_bits)
```

`total_fractions` includes per-row generic/range/timestamp lookups and actual/virtual table entries.

For batching `ell` base-oracle columns into WHIR over an LDE domain:

```text
batch_loss = ceil(log2 ell)
base_proximity_bits = 123 - lde_domain_log2 - batch_loss
batch_pow = max(0, target_bits - base_proximity_bits)
```

The latter was tied to the repository's chosen WHIR corollary/model and still needs theorem-hypothesis review in a full budget.

## Failure

The prover and generated verifier squeezed lookup challenges and the WHIR batching challenge without phase-specific PoW derived from the actual circuit degree/oracle count. A nominal higher-security schedule could therefore account for WHIR queries while omitting algebraic lookup and batched-proximity losses.

The transcript format also lacked nonce fields and post-PoW draw semantics for those phases, so this was not merely a missing configuration constant.

## Quantitative impact

The shortfall is circuit-specific:

```text
lookup shortfall = max(0, target - (123 - ceil_log2 D))
WHIR batch shortfall = max(0, target - (123 - domain_log2 - ceil_log2 ell))
```

For realistic Sec80 circuits cited by the fix, both evaluate to zero. Example Sec100 batching values in the added tests range from 8 to 12 bits depending on trace size and `ell`; lookup examples range from 1 to 10 bits as `D` grows. These are local retry-cost requirements, not a completed total-security result.

## Impact and fix

The intended 100-bit design omitted work needed before two challenge families. The fix derives both counts per compiled circuit/security target, adds proof nonces, grinds before the challenges, and has generated verification read/verify PoW then use special draws that skip the consumed PoW word. The zero-bit case follows the same transcript grammar.

The fixing commit explicitly left `config_for_100()` unfinished, so it should be described as closing parameterization mechanisms for the higher-security design rather than proving a deployed Sec100 claim.

## Regression

- Recompute `D`, `ell`, domain size, and required bits from the compiled artifact for every circuit.
- Test power-of-two boundaries and `D/ell + 1` so ceiling-log rounding is conservative.
- Compare nonce placement and post-PoW seed advancement in prover, Rust/generated verifier, GPU, and EVM paths.
- Verify zero-bit phases still consume the agreed proof/transcript framing.
- Place both terms in an error ledger with theorem version, hypotheses, and union/dependency treatment.

## Reproduction evidence

```sh
git diff 06f6c117dcc039100c6e7cbcc0c5f7db90f0b258 bc526de6cb89840e8b8bfd67c5aab5ffecc04585 -- prover/src/gkr/prover_config/pow_bits.rs verifier_generator/src/gkr/mod.rs
```
