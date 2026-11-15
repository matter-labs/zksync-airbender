# Circuit-sequence timestamp bound was hardcoded to u16

## Classification

- Producer-parity history: confirmed historical large-trace proving completeness bug
- Component: cached timestamp-high contribution for circuit sequencing
- Reduction location: chunk/circuit index → timestamp limb contribution → memory quotient witness
- Security character: stale host assertion aborted valid proofs; no verifier false acceptance
- Fixed by: [`3f67e32`](https://github.com/matter-labs/zksync-airbender/commit/3f67e3229d3a74d1e6d5071752c22b8597e4984f), PR [#178](https://github.com/matter-labs/zksync-airbender/pull/178)
- Vulnerable revision: `9ed79293e45136eb9929dee9751fe5c181d84366`

## Protocol context

Legacy unrolled proving embeds circuit sequence into timestamp limbs so memory events from different chunks occupy distinct global time regions. The contribution shifts `circuit_sequence` by a layout-derived amount based on trace length, timestamp index bits, and `TIMESTAMP_COLUMNS_NUM_BITS`.

The valid bound is the configured timestamp limb domain, not the storage width of an old implementation type.

## Intended bound

```text
sequence_contribution = circuit_sequence << circuit_sequence_bits_shift
require sequence_contribution < 2^TIMESTAMP_COLUMNS_NUM_BITS
```

The verifier/circuit must enforce the same timestamp-domain limit. The host prover may reject values outside it but must not impose a smaller unrelated bound.

## Failure

Cached-data construction asserted `sequence_contribution <= u16::MAX`. Timestamp width had become configurable, so configurations with more than 16 timestamp bits admitted valid contributions that the prover rejected.

The actual subsequent field construction could represent the value, and the protocol domain allowed it; only the outdated assertion prevented progress.

## Failure flow

1. Prove an execution with enough cycles/chunks that shifted `circuit_sequence` exceeds `2^16 - 1`.
2. Keep the contribution below the configured `2^TIMESTAMP_COLUMNS_NUM_BITS` bound.
3. Reach cached-data construction.
4. Abort on the stale u16 assertion before quotient generation.

This is an externally triggerable proving failure for high-cycle batches, not an accepted false statement. It should remain classified separately from verifier timestamp truncation.

## Impact and fix

Otherwise valid large executions could not be proved. The fix compares the shifted value against `1 << TIMESTAMP_COLUMNS_NUM_BITS`, restoring the actual protocol bound.

Bounds in prover caches, serializers, verifiers, and circuits must cite the semantic parameter they enforce. Host types such as `u16` are not protocol specifications.

## Regression

- Test the largest valid sequence contribution and the first invalid one.
- Cover timestamp widths below, equal to, and above 16.
- Exercise multiple trace lengths because they change the shift.
- Compare host assertion, circuit range constraint, verifier reconstruction, and memory tuple encoding.
- Include a high-cycle end-to-end proof rather than testing arithmetic alone.

## Reproduction evidence

```sh
git diff 9ed79293e45136eb9929dee9751fe5c181d84366 3f67e3229d3a74d1e6d5071752c22b8597e4984f -- prover/src/prover_stages/cached_data.rs
```
