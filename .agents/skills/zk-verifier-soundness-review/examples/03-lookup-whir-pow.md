# Lookup and WHIR batching challenges lacked derived grinding

## Classification

- Confirmed historical higher-security parameterization gap
- Component: lookup `alpha/gamma` and WHIR base-oracle batching challenge phases
- Verifier anchor: Sec100 code emitted by `verifier_generator/src/gkr/mod.rs` and consumed by native verifier tests
- Budget terms: cleared LogUp identity degree and batched-proximity loss
- Reachability: derived bits were zero for Sec80; the generator, prover, native verifier tests, and `gkr_test.sh --security-level 100` formed a buildable Sec100 path before the fix, although the fixing PR description inaccurately said `config_for_100` remained unfinished
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

At the vulnerable revision, every supported Sec100 `ProverConfig` hardcoded both
counts to zero. The prover asserted that lookup PoW was zero, left positive
batching PoW as `todo!()`, and drew both challenge phases directly. The generator
emitted the same direct draws. This path was exercised by an explicit Sec100
generator/prover/native-verifier mode; it was not inferred solely from a feature
name or from the later fix.

## Quantitative impact

The shortfall is circuit-specific:

```text
lookup shortfall = max(0, target - (123 - ceil_log2 D))
WHIR batch shortfall = max(0, target - (123 - domain_log2 - ceil_log2 ell))
```

For Sec80, both evaluate to zero for the supported circuits. Recomputing the
fix's formulas over the actual compiled artifacts at vulnerable revision
`06f6c11` gives:

| Circuit | `ceil(log2 D)` | lookup PoW | batched columns `ell` | batching PoW |
|---|---:|---:|---:|---:|
| `add_sub_lui_auipc_mop` | 31 | 8 | 56 | 8 |
| `bigint_with_extended_control` | 31 | 8 | 261 | 9 |
| `blake2_g_function` | 31 | 8 | 121 | 7 |
| `blake2_with_extended_control` | 31 | 8 | 875 | 8 |
| `jump_branch_slt` | 32 | 9 | 65 | 9 |
| `keccak_special5` | 32 | 9 | 274 | 9 |
| `mem_subword_only` | 32 | 9 | 54 | 8 |
| `mem_word_only` | 31 | 8 | 49 | 8 |
| `shift_binop` | 32 | 9 | 68 | 9 |
| `unified_reduced_machine` | 33 | 10 | 115 | 9 |
| `unsigned_mul_div` | 32 | 9 | 59 | 8 |

Thus every compiled circuit in that snapshot had a nonzero local Sec100
shortfall in both phases under the repository's adopted calculation. These are
retry-cost requirements for two local events, not a completed total-security
result and not permission to add the two PoW counts together.

## Impact and fix

The intended 100-bit design omitted work needed before two challenge families. The fix derives both counts per compiled circuit/security target, adds proof nonces, grinds before the challenges, and has generated verification read/verify PoW then use special draws that skip the consumed PoW word. The zero-bit case follows the same transcript grammar.

The fixing PR description said `config_for_100` remained `todo!()`, but the committed source contains concrete Sec100 schedules for trace lengths 20, 22, and 24 both before and after the fix, and the test driver explicitly generated and verified that mode. The accurate conclusion is that the mechanism closed a real gap in the repository's offered Sec100 configuration; it still does not, by itself, prove that a particular Sec100 artifact was deployed or that the complete system met 100 bits after unioning every other error term.

## Regression

- Recompute `D`, `ell`, domain size, and required bits from the compiled artifact for every circuit.
- Test power-of-two boundaries and `D/ell + 1` so ceiling-log rounding is conservative.
- Compare nonce placement and post-PoW seed advancement in prover, Rust/generated verifier, GPU, and EVM paths.
- Verify zero-bit phases still consume the agreed proof/transcript framing.
- Place both terms in an error ledger with theorem version, hypotheses, and union/dependency treatment.

## Reproduction evidence

```sh
git diff 06f6c117dcc039100c6e7cbcc0c5f7db90f0b258 bc526de6cb89840e8b8bfd67c5aab5ffecc04585 -- prover/src/gkr/prover/mod.rs prover/src/gkr/prover_config/example_configs.rs prover/src/gkr/prover_config/pow_bits.rs verifier_generator/src/gkr/mod.rs verifier_generator/tests/generate_verifiers.rs
```
