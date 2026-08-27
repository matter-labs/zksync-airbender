# Decoder multiplicities used timestamp-domain size

## Classification

- Producer-parity history: confirmed historical hardcoded-domain defect; affected active configuration not established
- Component: decoder lookup multiplicity buffers and stage-2 contribution
- Reduction location: executor decoder accesses → table-row multiplicity polynomial → lookup quotient
- Security character: latent configuration bug; the old constants equal the principal tracked decoder-table size, and smaller tables merely wrote zero padding in the evidence reviewed
- Fixed by: [`6869368`](https://github.com/matter-labs/zksync-airbender/commit/686936886e3330b50aa1965264f2ec04d7ace70c)
- Vulnerable revision: `1b29c81d08da5b122ddb30212dca0b5e5503663d`
- Activation condition: a supported decoder table whose nonzero row domain exceeds or otherwise conflicts with the fixed `2^20` allocation or `2^TIMESTAMP_COLUMNS_NUM_BITS` write range

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

Decoder multiplicity allocation used a literal `1 << 20`, while postprocessing wrote `1 << TIMESTAMP_COLUMNS_NUM_BITS` rows. These bounds were not derived from `executor_family_decoder_table_size`.

This is structurally unsafe for configurable decoder tables. A larger table can exceed the counter capacity or leave valid rows outside the write range. A smaller table, however, does not itself prove a bad lookup: the oversized counter buffer was zero-initialized, so writing additional zero multiplicities can be semantically harmless. The quotient stage lacked the new explicit assertion that multiplicity contributions beyond the decoder table were zero, but absence of that diagnostic is not itself a proof failure.

## Failure flow

1. Configure a decoder table with a nonzero row outside the old fixed counter or write range.
2. Execute a decoder lookup targeting that row.
3. Either index beyond the fixed counter allocation or fail to copy its multiplicity into the witness trace.
4. Build a lookup product missing that execution count.
5. A completed proof attempt then panics, corrupts construction, or fails the lookup identity.

The reviewed history shows the unsafe parameter coupling and its repair, but not a same-revision active configuration satisfying step 1. Tracked principal unrolled layouts used a `2^20` decoder table; some smaller serialized layouts do not establish failure because excess entries remain zero. A false-acceptance claim would additionally require proof that the verifier omitted the same rows rather than rejecting the malformed product.

## Impact and fix

Decoder lookup multiplicities were coupled to unrelated global constants rather than their table parameter. The fix derives one `bound` from `executor_family_decoder_table_size`, asserts buffer length equality, writes exactly that range, and asserts stage-2 multiplicity is zero beyond the table.

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
