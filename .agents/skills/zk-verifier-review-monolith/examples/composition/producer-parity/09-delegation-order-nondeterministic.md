# Delegation data order depended on HashMap iteration

## Classification

- Producer-parity history: confirmed historical multi-delegation completeness bug
- Invariant: every positional delegation vector uses one canonical type order
- Component: GPU execution prover commitment/proof handoff
- Security character: nondeterministic participant misassociation; soundness depends on whether the verifier authenticates type ownership rather than position alone
- Fixed by: [`5c01391`](https://github.com/matter-labs/zksync-airbender/commit/5c01391c67be617c5da53506dc27ac15564203d8), PR [#54](https://github.com/matter-labs/zksync-airbender/pull/54)
- Vulnerable revision: `6a49503916f046d091e1f7134d80fe037ace8ec6`

## Composition context

Programs can invoke several delegation circuit types. Execution proving collects per-type memory commitments and later per-type proofs in hash maps, while downstream trace splitting and full-statement composition represent those groups as positional vectors expected in ascending delegation-type order.

The order affects more than presentation. It determines which verifier/setup is associated with each cap and contribution and, when the vector is absorbed positionally, which semantic owner is bound to each transcript slot.

## Intended invariant

At every map-to-vector boundary:

```text
keys = sort_ascending(nonempty delegation type IDs)
commitment_vector[i] belongs to keys[i]
proof_vector[i] belongs to keys[i]
verifier/setup/transcript tag at i also belongs to keys[i]
```

Commitment and proof phases must derive their order from the same canonical key list, not from independent iterations that merely happen to be deterministic in one process.

## Failure

GPU proving unpacked delegation memory commitments and delegation proofs directly from `HashMap` iteration. Downstream code expected sorted delegation IDs. With multiple types, vector position could therefore associate a cap/proof with the wrong circuit type or disagree between stages.

Hash-map iteration can appear stable in small tests and change with insertion order, allocator state, process randomization, or realistic program scale. A one-type proof is vacuously ordered and cannot expose the bug.

## Failure flow

1. Execute calls to delegation types `a` and `b` in an insertion order that yields map order `[b, a]`.
2. Convert commitments or proofs to a positional vector without retaining/authenticating keys.
3. Downstream composition interprets index zero as type `a` and index one as type `b`.
4. Setup checks, transcript slots, or accumulator ownership no longer match the data.
5. Honest verification fails intermittently, potentially only after the global product or transcript challenge has diverged.

The historical report is a completeness bug because downstream sorted-order assertions/checks caught the mismatch. If any consumer trusts position without type tags and uses proof-supplied setup, the same class becomes semantic substitution and must be assessed separately.

## Impact and fix

Multi-type GPU proofs were nondeterministic and failed at realistic scale. The fix collects and sorts delegation IDs, then uses that canonical order for both memory commitments and proof groups.

Canonical ordering is a protocol rule whenever maps cross serialization, transcript, batching, setup selection, or accumulator boundaries. Prefer carrying explicit `(type, value)` pairs and absorbing the tag even when sorted position is also checked.

## Regression

- Build the same logical delegation map under many insertion orders and require byte-identical vectors, transcript traces, and proofs.
- Use at least three types so reversal-only assumptions do not pass.
- Assert commitments and proofs are keyed by the same sorted ID list.
- Swap two values while retaining their explicit tags and require rejection.
- Verify the outer participant roster and setup table agree with the canonical vector.

## Reproduction evidence

```sh
git diff 6a49503916f046d091e1f7134d80fe037ace8ec6 5c01391c67be617c5da53506dc27ac15564203d8 -- gpu_prover/src/execution/prover.rs
```
