# GPU query drawing advanced the seed by one digest block too many

## Classification

- Confirmed historical Fiat-Shamir squeeze-length mismatch
- Component: GPU WHIR query-index drawing and PoW seed evolution
- Security character: CPU/GPU transcript parity failure at digest-block boundaries
- Fixed by: [`c1e0576`](https://github.com/matter-labs/zksync-airbender/commit/c1e0576ec77ded9a2436dfe74475d97986527d94)
- Vulnerable revision: `1b653f86adf8f6d2e12cba664f7ce10f085d381`

## Protocol context

The query phase expands a hash seed into enough bits for all query indices. The implementation reserves one 32-bit word for the PoW/header convention and pads the total word count to a full hash-output block. Even if only a prefix of those words is exposed as query indices, every squeezed block advances the rolling seed used by the next protocol challenge.

Transcript parity therefore depends on the expansion length, not merely on equality of the bits that callers consume.

## Intended calculation

For `query_bits = num_queries * query_index_bits`, the CPU/verifier convention was:

```text
query_words = ceil(query_bits / 32)
required_words = next_multiple_of_8(query_words + 1 header word)
```

The vulnerable GPU path effectively used:

```text
total_bits = query_bits + 32 header bits
required_words = next_multiple_of_8(ceil(total_bits / 32) + 1 header word)
```

so the header was counted twice.

## Failure

When the correct count landed exactly on a digest-block boundary, the extra word forced the GPU to squeeze an additional eight-word block. For example, `9 * 22 = 198` query bits require seven query words; adding one header gives exactly eight. The GPU calculation added another header and rounded to sixteen.

The query indices still matched because they consumed only the common prefix. The hidden difference was the post-expansion seed. The first visible mismatch appeared later at delinearization, making the failure look like an algebra or OOD bug far from the actual off-by-one.

## Failure flow

1. CPU/verifier and GPU begin from the same post-PoW seed.
2. Both expose the same first seven words as query bits.
3. CPU/verifier stop after one eight-word block; GPU expands a second block.
4. All query indices compare equal.
5. The next challenge is squeezed from different rolling states and verification fails downstream.

This historical defect is a completeness/parity bug. It does not show a malicious proof bypassing a canonical verifier, but it exposes a class that can become security-relevant if different verifier environments disagree on seed evolution.

## Impact and fix

GPU proofs failed only for parameter combinations near output-block boundaries, with symptoms delayed until the next challenge. The fix computes the number of words from query bits alone and adds the skipped header exactly once before block padding.

Audit sponge/hash expansion as a state machine. Comparing challenge outputs that happen to consume a shared prefix is insufficient; compare the resulting seed/counter after every variable-length draw.

## Regression

- Test word counts immediately below, exactly at, and immediately above every eight-word digest boundary.
- Compare query indices and the post-query rolling seed.
- Derive and compare at least one subsequent challenge, such as delinearization.
- Cover `query_bits = 0`, exact 32-bit multiples, and partial final words.
- Differential-test CPU, GPU, recursive, and L1 implementations from a shared transcript event vector.

## Reproduction evidence

```sh
git diff 1b653f86adf8f6d2e12cba664f7ce10f085d381 c1e0576ec77ded9a2436dfe74475d97986527d94 -- gpu/circuit_prover/src/prover/pow.rs
```
