# Historical cross-circuit and global-composition examples

These cases isolate failures in invariants that span proofs, chunks, circuit
families, memory products, delegation streams, or machine-state transitions.
The main table contains only reachable verifier soundness or concrete
honest-proof/completeness failures. The latent table keeps exact broken
boundaries whose harmful consumer was not connected in the reviewed revision.
Each case distinguishes accepted-proof soundness from producer/verifier parity
and reachability.

| # | Example | Fix | Primary failure |
|---:|---|---|---|
| 1 | [Delegation setup was checked only for the first proof](01-delegation-setup-check-once.md) | `32edde7`, PR #21 | setup identity gap |
| 2 | [Unified machine-state challenge was not compared](02-unified-machine-state-challenge.md) | `8ef06cf`, PR #225 | cross-proof challenge gap |
| 5 | [Unified circuit sequence used a dead legacy field](05-unified-circuit-sequence.md) | `85c4925` | wrong chunk identity check |
| 6 | [Unified inits/teardowns used placeholder address windows](06-unified-it-address-windows.md) | `1581753`, PR #389 | wrong global RAM partition |
| 7 | [Unified GPU permutation could not hand off the prior accumulator](07-unified-permutation-prior-accumulator.md) | `361e73f`, PR #167 | fail-closed grand-product handoff |
| 8 | [Setup/teardown chunk index never advanced](08-it-chunker-index.md) | `9bb1607`, PR #85 | chunk coverage bug |
| 9 | [Delegation data order depended on HashMap iteration](09-delegation-order-nondeterministic.md) | `5c01391`, PR #54 | participant ordering mismatch |
| 10 | [Exact-multiple replay dropped the final full chunk](10-exact-multiple-final-chunk.md) | `0a918ce`, PR #325 | boundary completeness failure |
| 11 | [Padding rows used PC zero instead of PC_STEP](11-padding-row-pc.md) | `e5815c5` | padding state contamination |
| 12 | [ROM page was omitted from inits/teardowns](12-rom-page-it-omission.md) | `46c58c9` | global memory closure gap |
| 13 | [Replay self-loop termination skipped the timestamp increment](13-replay-timestamp-order.md) | `6538ff5` | state continuity bug |
| 14 | [Blake delegation timestamps used the wrong round count](14-blake-delegation-timestamps.md) | `e30029f` | delegation/state mismatch |

## Latent implementation defects

These contain an exact broken implementation and activation condition, but the
historical review did not establish a proof-producing caller or accepting
artifact at the vulnerable revision.

| # | Example | Fix | Activation risk |
|---:|---|---|---|
| 3 | [JIT trace callback observed the CSR-family counter before its increment](latent/03-delegation-counter-order.md) | `80e37e8` | a proof-producing callback derives per-chunk work from callback-time counters |
| 15 | [Cached GKR memory tuples would invert the address-space tag when activated](latent/15-address-space-selector-inversion.md) | `b5021bc` | cached dynamic register/RAM lowering becomes proof-producing |

The former timestamp-parser card was removed after validation: in the only
affected branch the semantic requirement was that both timestamp limbs equal
zero. The old checked u16 reconstruction and the replacement field-wise zero
checks accept exactly the same canonical field inputs there, so the diff was
correctness cleanup rather than a demonstrated active or latent bug.

Transcript framing is owned by the transcript corpus; local algebraic gate bugs remain in the circuit or GKR corpora.
