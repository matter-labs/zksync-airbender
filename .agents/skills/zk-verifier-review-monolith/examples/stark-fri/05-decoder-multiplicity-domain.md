# Decoder multiplicities used timestamp-domain size

## Classification

- Confirmed historical legacy lookup-argument bug
- Fixed by: [`6869368`](https://github.com/matter-labs/zksync-airbender/commit/686936886e3330b50aa1965264f2ec04d7ace70c)
- Vulnerable revision: `1b29c81d08da5b122ddb30212dca0b5e5503663d`

## Failure

Decoder multiplicity buffers and writes were sized by `1 << TIMESTAMP_COLUMNS_NUM_BITS` (and elsewhere a literal `1 << 20`) rather than `executor_family_decoder_table_size`.

## Impact and fix

The lookup multiplicity polynomial could include unrelated rows, omit valid decoder rows, or index past the actual table contract. The fix single-sources the decoder-table bound and requires multiplicities outside it to be zero.

## Regression

Exercise decoder table sizes both smaller and larger than the timestamp table; assert buffer length, row writes, and quotient contribution share one bound.

```sh
git diff 1b29c81d08da5b122ddb30212dca0b5e5503663d 686936886e3330b50aa1965264f2ec04d7ace70c -- prover/src/witness_evaluator/mod.rs prover/src/prover_stages/unrolled_prover/stage2.rs
```
