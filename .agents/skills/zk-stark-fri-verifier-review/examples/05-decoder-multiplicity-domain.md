# Decoder multiplicities used timestamp-domain size

## Classification

- Confirmed historical legacy lookup-argument construction bug
- Component: decoder lookup multiplicity buffers and stage-2 contribution
- Reduction location: executor decoder accesses → table-row multiplicity polynomial → lookup quotient
- Security character: prover-side domain mismatch causing omission, unrelated rows, or out-of-contract indexing; verifier severity requires matching accepted relation analysis
- Fixed by: [`6869368`](https://github.com/matter-labs/zksync-airbender/commit/686936886e3330b50aa1965264f2ec04d7ace70c)
- Vulnerable revision: `1b29c81d08da5b122ddb30212dca0b5e5503663d`

## Protocol context

The legacy decoder lookup argument associates one multiplicity with each row of the executor-family decoder table. The multiplicity polynomial's logical domain is the table's configured row count, `executor_family_decoder_table_size`, even though it is embedded in a trace whose timestamp range-check table may have a different size.

The lookup identity relies on exact row alignment:

```text
Σ execution lookups compressed at challenge
= Σ_{decoder table row i} multiplicity[i] / (table_value[i] + gamma)
```

Buffer allocation, counter writes, trace placement, and stage-2 reads must share the decoder-table bound.

## Intended domain relation

```text
decoder_multiplicities.len() == executor_family_decoder_table_size
write rows 0 .. decoder_table_size
for trace rows >= decoder_table_size, decoder multiplicity contribution == 0
```

Timestamp-table size is relevant only to timestamp lookups.

## Failure

Decoder multiplicity allocation/writes used `1 << TIMESTAMP_COLUMNS_NUM_BITS` and another path used a literal `1 << 20`. These values were unrelated to `executor_family_decoder_table_size`.

When the domains differed, the producer could omit valid decoder rows, include unrelated trace rows, or rely on buffer/index behavior outside the table contract. The quotient stage lacked an explicit assertion that multiplicity contributions beyond the decoder table were zero.

## Failure flow

1. Configure a decoder table whose size differs from the timestamp table.
2. Count decoder accesses into a buffer sized under the timestamp assumption.
3. Copy that buffer into trace rows using the wrong bound.
4. Build lookup quotient contributions where row `i` no longer corresponds to decoder table entry `i`, or valid rows are missing.
5. Fail the lookup identity for honest execution—or expose missing table coverage if an accepting verifier also uses the wrong inventory.

The historical diff repairs prover construction and adds self-checking. A false-acceptance claim needs proof that the verifier's table/opening relation omitted the same rows rather than rejecting the malformed product.

## Impact and fix

Decoder lookup multiplicities were not guaranteed to match their setup-table polynomial. The fix derives one `bound` from `executor_family_decoder_table_size`, asserts buffer length equality, writes exactly that range, and asserts stage-2 multiplicity is zero beyond the table.

Every lookup table needs a row-domain ledger. Similar powers-of-two do not make timestamp, decoder, range-check, or generic table domains interchangeable.

## Regression

- Test decoder tables smaller and larger than the timestamp domain.
- Assert buffer length, counter indexing, trace write range, setup table length, and quotient read range all equal the configured decoder size.
- Put sentinel nonzero values immediately outside the domain and require self-check failure.
- Compare total multiplicity sum with the number of decoder lookup accesses.
- Close the complete lookup identity for boundary table rows.

## Reproduction evidence

```sh
git diff 1b29c81d08da5b122ddb30212dca0b5e5503663d 686936886e3330b50aa1965264f2ec04d7ace70c -- prover/src/witness_evaluator/mod.rs prover/src/prover_stages/unrolled_prover/stage2.rs
```
