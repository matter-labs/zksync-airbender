# Historical concrete-soundness, PoW, and field examples

Only four retained-history cases meet the bar for a concrete security-budget or field-arithmetic example. Security-feature additions without a demonstrated prior gap, and performance-model arithmetic bugs, are intentionally excluded.

Each card identifies the exact configuration/reachability boundary, reconstructs the relevant inequality or field invariant, and states what may legitimately be counted as security. Deliberate policy constants are not relabeled as accidental derivations, and latent arithmetic defects are not reported as active bypasses when shipped parameters cannot reach them.

| # | Example | Fix | Primary failure | Reachability |
|---:|---|---|---|---|
| 3 | [Lookup and WHIR batching challenges lacked derived grinding](03-lookup-whir-pow.md) | `bc526de`, PR #331 | LogUp and batching retry-cost gaps | explicit Sec100 generator/prover/verifier path; deployment not established |

## Latent implementation defects

| # | Example | Fix | Primary failure | Activation condition |
|---:|---|---|---|---|
| 1 | [PoW threshold would accept every nonce at the unused 32-bit boundary](latent/01-pow-threshold-shift-32.md) | `bbf919d`, PR #322 | shift overflow / zero grinding | select legal-but-unshipped `pow_bits = 32` |
| 2 | [Memory permutation PoW would have been zero in a Sec100 full-statement verifier](latent/02-memory-pow-zero.md) | `06f6c11`, PR #330 | memory/delegation retry-cost gap | hook Sec100 component verifiers into the full-statement wrapper/binary |
| 4 | [Mersenne31 constructors reduced large values incorrectly](latent/04-mersenne31-reduction.md) | `03c4daf` | field arithmetic bug | verifier-facing large-input caller |

Each entry distinguishes active, configuration-specific, and latent impact; do not report nominal “bits” without checking reachability and all error terms. A concrete-soundness finding should include the full parameter tuple, number of adversarial attempts, every composed error term, and whether grinding cost is actually enforced by the verifier.
