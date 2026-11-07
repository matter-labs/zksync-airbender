# Exact-multiple replay dropped the final full chunk

## Classification

- Producer-parity history: confirmed historical proving completeness bug
- Invariant: replay chunking conserves every family/delegation call for all cardinalities
- Component: three unrolled witness-replay helpers
- Security character: externally triggerable proving denial/failure, not a verifier false-acceptance bug
- Fixed by: [`0a918ce`](https://github.com/matter-labs/zksync-airbender/commit/0a918ceb9c10279505cf4e5b3cb611fba2f335e4), PR [#325](https://github.com/matter-labs/zksync-airbender/pull/325)
- Vulnerable revision: `b566d65ce9b1f9b7ee9cae6d4325adc5528f38c0`

## Composition context

Witness replay groups per-family or per-delegation calls into fixed-capacity proving chunks. The final chunk may be partial, but when a positive call count is an exact multiple of capacity, the final chunk is full. Zero calls are handled by a separate early return.

Three helpers repeated the same cardinality calculation, so the defect affected several participant families rather than one circuit implementation.

## Intended invariant

For `num_calls > 0` and `capacity > 0`:

```text
num_chunks = ceil(num_calls / capacity)
last_chunk_len = if num_calls % capacity == 0 {
    capacity
} else {
    num_calls % capacity
}
sum(chunk lengths) == num_calls
every source call appears in exactly one chunk
```

The zero-call case must remain distinct: it should not manufacture a full chunk merely because its remainder is zero.

## Failure

The replay helpers unconditionally set the final chunk length to `num_calls % capacity`. For every positive exact multiple, the remainder was zero even though the already-created last chunk represented a full capacity of calls. The helper truncated it to length zero and then failed its coverage assertion/panicked.

Tests concentrated below capacity and on partial remainders, leaving the modulo-zero discontinuity unexercised. Production-sized capacities made the trigger rare in casual testing but program behavior can control the relevant call counts.

## Failure flow

1. Execute exactly `k * capacity` calls for an affected family, with `k >= 1`.
2. Replay constructs `k` chunks and fills the final chunk completely.
3. Finalization computes remainder zero and truncates the last chunk to zero length.
4. Reconstructed event count becomes `(k - 1) * capacity` or the internal consistency assertion fails immediately.
5. The prover cannot produce the complete participant set for an otherwise valid execution.

This is a denial/completeness issue. It should not be reported as omitted-call soundness unless an accepting path bypasses the coverage assertion and the verifier lacks an independent global closure check.

## Impact and fix

Programs whose family/delegation call count landed exactly on a positive chunk multiple could not be proved. The fix maps a zero remainder to `capacity` after the existing zero-call early return, in all three helpers.

Any chunk-sizing review should use a cardinality matrix rather than a few example sizes: zero, one, `capacity-1`, `capacity`, `capacity+1`, and several exact/partial multiples.

## Regression

- Test `0`, `1`, `C-1`, `C`, `C+1`, `2C-1`, `2C`, and `2C+1` for every replay helper.
- Assert total lengths equal input count and source indices form an exact partition.
- Verify zero calls produce no unintended full chunk.
- Use production capacities or parameterized equivalents so arithmetic matches deployment.
- Include end-to-end programs that control affected delegation/family counts.

## Reproduction evidence

```sh
git diff b566d65ce9b1f9b7ee9cae6d4325adc5528f38c0 0a918ceb9c10279505cf4e5b3cb611fba2f335e4 -- prover/src/witness_evaluator/unrolled/mod.rs
```
