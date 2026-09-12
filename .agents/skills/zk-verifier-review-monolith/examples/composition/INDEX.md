# Historical cross-circuit and global-composition examples

These cases isolate failures in invariants that span proofs, chunks, circuit
families, memory products, delegation streams, or machine-state transitions.
The main table contains only reachable verifier soundness or verifier-caused
honest-proof/completeness failures. Producer, GPU, replay, compiler, and
serialization defects remain under `producer-parity/` as protocol seam history,
but are excluded from verifier-centric blind evaluation unless a concrete
accepting verifier consumed the same defect.

| # | Example | Fix | Primary failure |
|---:|---|---|---|
| 1 | [Delegation setup was checked only for the first proof](01-delegation-setup-check-once.md) | `32edde7`, PR #21 | setup identity gap |
| 2 | [Unified machine-state challenge was not compared](02-unified-machine-state-challenge.md) | `8ef06cf`, PR #225 | cross-proof challenge gap |
| 5 | [Unified circuit sequence used a dead legacy field](05-unified-circuit-sequence.md) | `85c4925` | wrong chunk identity check |

## Producer-parity history

These cards remain valuable when tracing the producer-to-verifier seam, but a
correct verifier rejects their malformed or inconsistent output. They are not
verifier vulnerabilities and are not blind-evaluation targets.

| # | Example | Fix | Producer-side failure |
|---:|---|---|---|
| 3 | [JIT trace callback observed the CSR-family counter before its increment](producer-parity/03-delegation-counter-order.md) | `80e37e8` | latent callback state drift |
| 6 | [Unified inits/teardowns used placeholder address windows](producer-parity/06-unified-it-address-windows.md) | `1581753`, PR #389 | wrong proof-input RAM partition |
| 7 | [Unified GPU permutation could not hand off the prior accumulator](producer-parity/07-unified-permutation-prior-accumulator.md) | `361e73f`, PR #167 | fail-closed accumulator handoff |
| 8 | [Setup/teardown chunk index never advanced](producer-parity/08-it-chunker-index.md) | `9bb1607`, PR #85 | proof-input chunk loss |
| 9 | [Delegation data order depended on HashMap iteration](producer-parity/09-delegation-order-nondeterministic.md) | `5c01391`, PR #54 | nondeterministic producer ordering |
| 10 | [Exact-multiple replay dropped the final full chunk](producer-parity/10-exact-multiple-final-chunk.md) | `0a918ce`, PR #325 | replay completeness failure |
| 11 | [Padding rows used PC zero instead of PC_STEP](producer-parity/11-padding-row-pc.md) | `e5815c5` | malformed padding witness |
| 12 | [ROM page was omitted from inits/teardowns](producer-parity/12-rom-page-it-omission.md) | `46c58c9` | incomplete boundary witness |
| 13 | [Replay self-loop termination skipped the timestamp increment](producer-parity/13-replay-timestamp-order.md) | `6538ff5` | replay state mismatch |
| 14 | [Blake delegation timestamps used the wrong round count](producer-parity/14-blake-delegation-timestamps.md) | `e30029f` | delegated witness mismatch |
| 15 | [Cached GKR memory tuples would invert the address-space tag when activated](producer-parity/15-address-space-selector-inversion.md) | `b5021bc` | latent compiler tuple defect |

The former timestamp-parser card was removed after validation: in the only
affected branch the semantic requirement was that both timestamp limbs equal
zero. The old checked u16 reconstruction and the replacement field-wise zero
checks accept exactly the same canonical field inputs there, so the diff was
correctness cleanup rather than a demonstrated active or latent bug.

Transcript framing is owned by the transcript corpus; local algebraic gate bugs remain in the circuit or GKR corpora.
