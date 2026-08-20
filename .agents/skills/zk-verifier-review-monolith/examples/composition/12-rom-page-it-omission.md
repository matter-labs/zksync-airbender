# ROM page was omitted from inits/teardowns

## Classification

- Confirmed historical global-memory coverage bug
- Invariant: every touched address region participates in both execution accesses and memory boundary closure
- Component: GPU RAM tracking and inits/teardowns generation
- Security character: missing global-memory participant for page zero; historical producer behavior generally prevents closure, while a verifier must ensure coverage is not prover-selectable
- Fixed by: [`46c58c9`](https://github.com/matter-labs/zksync-airbender/commit/46c58c9f95179f0f14af4ebe1105e1da4511bbc1)
- Vulnerable revision: `65c3704ffd45a5fdea3185bdabde789d7ecf3c3d`

## Composition context

The global RAM argument pairs execution reads/writes with inits/teardowns entries for touched words. Page zero is the ROM/program region. Its value semantics differ from mutable RAM—teardown values remain zero/immutable—but its accesses and timestamps are still part of the memory history.

A special value policy does not remove an address space from the permutation. The boundary stream must retain enough timestamp/access information to pair every execution-side contribution.

## Intended invariant

For every word with a nonzero touched timestamp on any page, including page zero:

```text
word appears exactly once in the relevant I/T enumeration
initial value follows memory initialization policy
final timestamp equals the tracked last access
final value follows region policy:
    ROM -> canonical immutable/zero teardown value
    RAM -> tracked mutable value
```

Touched-word counting and iteration must enumerate the same set.

## Failure

The GPU RAM tracker skipped page zero in `get_touched_words_count` and inits/teardowns iteration. `read_word` also only marked touches for non-ROM addresses. ROM reads performed by execution were therefore absent from the boundary participant set.

The omission mixed up “ROM cannot be mutated” with “ROM need not appear in memory consistency.” Timestamp evolution still makes ROM reads observable to the global argument.

## Adversarial or failure flow

1. Execute one or more instruction/data reads from page zero.
2. Produce execution-side RAM contributions containing those address/timestamp tuples.
3. Omit page zero from touched counts and I/T enumeration.
4. Aggregate only mutable-page boundary products.
5. Leave the ROM execution factors unmatched at final memory closure—or, if a verifier lets the prover choose the participant set without an independently fixed endpoint, create an unproved address region.

The historical fix closes producer completeness. The verifier audit must still establish that program/ROM commitments, address-space tags, and final product identity force page-zero inclusion rather than trusting a touched-page manifest.

## Impact and fix

Execution accesses and I/T closure described different address sets, breaking the global memory product for programs touching ROM. The fix tracks reads on all pages, counts/enumerates page zero, preserves its last timestamp, and specializes only its teardown value to the immutable zero policy.

For every excluded region in a global argument, demand an algebraic reason why its contributions are identity. A semantic label such as ROM, MMIO, register, or precompile is not such a proof.

## Regression

- In one execution, touch ROM and mutable RAM and assert every nonzero timestamp appears once in the I/T stream.
- Read the first and last words of page zero and cross page boundaries.
- Verify ROM teardown values follow immutable policy while timestamps reflect accesses.
- Compare touched-word count with iterator cardinality and with row-derived execution contributions.
- Remove one ROM I/T item from an otherwise valid proof campaign and require global closure failure.

## Reproduction evidence

```sh
git diff 65c3704ffd45a5fdea3185bdabde789d7ecf3c3d 46c58c9f95179f0f14af4ebe1105e1da4511bbc1 -- gpu_prover/src/execution/ram.rs
```
