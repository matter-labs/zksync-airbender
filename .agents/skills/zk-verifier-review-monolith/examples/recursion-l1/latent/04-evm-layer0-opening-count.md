# Latent: EVM layer-0 opening list stopped at 72 instead of 113

## Classification

- Exact latent GKR verifier defect in the unfinished EVM port
- Boundary: layer-0 base polynomial evaluations → next batched claim and WHIR opening inventory
- Component: generated point-claim count, transcript helper, and calldata cursor
- Security character: 41 base evaluations would be outside the randomized handoff batch if this source were selected
- Fixed by: [`16a5ceb`](https://github.com/matter-labs/zksync-airbender/commit/16a5cebf46a3ffa378a4dc893a302d33a359d9d7)
- Vulnerable revision: `fe19aa23dce1c5bdac100756cc2a51f15f6af29e`

## Boundary context

Layer 0 consumes openings of committed memory, witness, and setup/base polynomials at the final GKR point. After checking the layer gate relation, the verifier absorbs all those evaluations, draws a batching coefficient, forms the next/base opening claim, and advances to the subsequent proof data.

The compiled artifact exposed 113 non-cache base inputs for this layer. The count determines transcript bytes, Horner batching, next cursor, and the GKR-to-WHIR polynomial inventory.

## Intended handoff contract

```text
points = memory_width + witness_width + setup_width = 113
absorb exactly points field encodings
next_alpha binds all 113 evaluations
next_claim = Horner_batch(evaluations[0..113], next_alpha)
next_ptr = ptr + 113 * encoded_field_bytes
WHIR opening inventory names the same 113 base values/columns
```

Cache/virtual values are separately recomputed and must not distort the committed base count.

## Failure

The hand-written/generated layer-0 code set `points := 72`, called `transcript72to1`, batched only that prefix, and advanced the cursor by 72 field elements. The parser's `previous_input_count` was also derived from incorrect group accounting rather than the actual memory+witness+setup widths.

Forty-one base evaluations used by the current artifact were therefore outside the point-claim batch, while subsequent proof parsing began at an offset inconsistent with the true layer message.

## Why latent rather than historical acceptance

This revision belonged to the June prototype sequence. The later `4f8d993`
commit describes its generated large-pointer variant as the first passing build;
the vulnerable revision has only compiler/stat scripts and no generated-contract
or end-to-end consumer. The algebraic defect is exact, but history does not show a
compiled verifier reaching success or a canonical proof reaching this parser.

## Adversarial flow

1. Supply the first 72 base evaluations that satisfy the checked prefix/batch.
2. Choose remaining base evaluations without affecting `next_alpha` or `next_claim`.
3. Use those values in layer-0 gate expressions or let them be reinterpreted as later calldata because the cursor advances too little.
4. Continue the GKR/WHIR handoff without a PCS opening claim for the omitted polynomial inventory.

The exact accepting assignment depends on later parser alignment, but an opening absent from the randomized PCS handoff is unproved even if a point check read it transiently.

## Impact and fix

Had this unfinished verifier been compiled and selected, it would not have bound
the complete layer-0 input vector and would have parsed the remainder under the
wrong grammar. The fix updates the count to 113, adds a matching one-shot
transcript function, advances by 113 encodings, and derives the count from
`memory + witness + setup` width.

At every recursion/L1 seam, derive counts from the artifact and prove equality among parser length, transcript absorption, algebraic batch, commitment inventory, and cursor advance.

## Regression

- Derive the count from the compiled artifact and reject any generated literal mismatch.
- Mutate the first, 72nd, 73rd, and 113th evaluations independently.
- Assert exact transcript bytes and post-layer cursor.
- Compare the layer-0 batch to a Rust direct Horner calculation over all openings.
- Verify WHIR proves every memory/witness/setup polynomial represented by the 113 evaluations.

## Reproduction evidence

```sh
git diff fe19aa23dce1c5bdac100756cc2a51f15f6af29e 16a5cebf46a3ffa378a4dc893a302d33a359d9d7 -- verifier_evm/circuit.yul verifier_evm/parse.rs
```
