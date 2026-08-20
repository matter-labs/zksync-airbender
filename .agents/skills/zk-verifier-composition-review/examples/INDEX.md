# Historical cross-circuit and global-composition examples

These cases isolate failures in invariants that span proofs, chunks, circuit families, memory products, delegation streams, or machine-state transitions. Each case distinguishes an accepted-proof soundness gap from prover/verifier parity, reachability, and honest-proof completeness. Prover-only cases are included only when they construct data consumed by the global verifier relation.

| # | Example | Fix | Primary failure |
|---:|---|---|---|
| 1 | [Delegation setup was checked only for the first proof](01-delegation-setup-check-once.md) | `32edde7`, PR #21 | setup identity gap |
| 2 | [Unified machine-state challenge was not compared](02-unified-machine-state-challenge.md) | `8ef06cf`, PR #225 | cross-proof challenge gap |
| 3 | [A delegation chunk could be emitted before its circuit counter](03-delegation-counter-order.md) | `80e37e8` | chunk metadata/data mismatch |
| 4 | [Timestamp boundary checks reused a legacy u16-limb parser](04-timestamp-u16-truncation.md) | `97dbacf`, PR #81 | stale state-layout assumption |
| 5 | [Unified circuit sequence used a dead legacy field](05-unified-circuit-sequence.md) | `85c4925` | wrong chunk identity check |
| 6 | [Unified inits/teardowns used placeholder address windows](06-unified-it-address-windows.md) | `1581753`, PR #389 | wrong global RAM partition |
| 7 | [Unified GPU permutation lost the prior accumulator](07-unified-permutation-prior-accumulator.md) | `361e73f`, PR #167 | grand-product chain break |
| 8 | [Setup/teardown chunk index never advanced](08-it-chunker-index.md) | `9bb1607`, PR #85 | chunk coverage bug |
| 9 | [Delegation data order depended on HashMap iteration](09-delegation-order-nondeterministic.md) | `5c01391`, PR #54 | participant ordering mismatch |
| 10 | [Exact-multiple replay dropped the final full chunk](10-exact-multiple-final-chunk.md) | `0a918ce`, PR #325 | boundary completeness failure |
| 11 | [Padding rows used PC zero instead of PC_STEP](11-padding-row-pc.md) | `e5815c5` | padding state contamination |
| 12 | [ROM page was omitted from inits/teardowns](12-rom-page-it-omission.md) | `46c58c9` | global memory closure gap |
| 13 | [Replay early return skipped the timestamp increment](13-replay-timestamp-order.md) | `6538ff5` | state continuity bug |
| 14 | [Blake delegation timestamps used the wrong round count](14-blake-delegation-timestamps.md) | `e30029f` | delegation/state mismatch |
| 15 | [Cached GKR memory tuples inverted the address-space tag](15-address-space-selector-inversion.md) | `b5021bc` | RAM/register domain inversion |

Transcript framing is owned by the transcript corpus; local algebraic gate bugs remain in the circuit or GKR corpora.
