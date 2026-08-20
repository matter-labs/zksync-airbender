# Historical concrete-soundness, PoW, and field examples

Only four retained-history cases meet the bar for a concrete security-budget or field-arithmetic example. Security-feature additions without a demonstrated prior gap, and performance-model arithmetic bugs, are intentionally excluded.

Each card identifies the exact configuration/reachability boundary, reconstructs the relevant inequality or field invariant, and states what may legitimately be counted as security. Deliberate policy constants are not relabeled as accidental derivations, and latent arithmetic defects are not reported as active bypasses when shipped parameters cannot reach them.

| # | Example | Fix | Primary failure | Reachability |
|---:|---|---|---|---|
| 1 | [PoW threshold accepted every nonce at 32 bits](01-pow-threshold-shift-32.md) | `bbf919d`, PR #322 | shift overflow / zero grinding | latent in shipped configs |
| 2 | [Memory permutation PoW was hardcoded to zero](02-memory-pow-zero.md) | `06f6c11`, PR #330 | Sec100 budget gap | Sec100 path |
| 3 | [Lookup and WHIR batching challenges lacked derived grinding](03-lookup-whir-pow.md) | `bc526de`, PR #331 | degree/proximity budget gap | Sec100 design |
| 4 | [Mersenne31 constructors reduced large values incorrectly](04-mersenne31-reduction.md) | `03c4daf` | field arithmetic bug | input-dependent |

Each entry distinguishes active, configuration-specific, and latent impact; do not report nominal “bits” without checking reachability and all error terms. A concrete-soundness finding should include the full parameter tuple, number of adversarial attempts, every composed error term, and whether grinding cost is actually enforced by the verifier.
