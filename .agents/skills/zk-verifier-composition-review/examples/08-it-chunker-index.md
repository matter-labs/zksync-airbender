# Setup/teardown chunk index never advanced

## Classification

- Confirmed historical chunk-coverage bug
- Invariant: every source inits/teardowns item belongs to exactly one correctly sized output chunk
- Component: `SetupAndTeardownChunker` fill and skip paths
- Security character: confirmed honest-proof generation/completeness failure in
  the active GPU execution worker
- Fixed by: [`9bb1607`](https://github.com/matter-labs/zksync-airbender/commit/9bb1607452baa6c1c018a47567fcbb4bb8cbbc38), PR [#85](https://github.com/matter-labs/zksync-airbender/pull/85)
- Vulnerable revision: `d4fc8163d0d6934323af3bcef2b1bafa9064865d`

## Composition context

The inits/teardowns trace is split into power-of-two proof chunks. Chunk position affects how the source is sliced, including special handling for the first chunk's padding and the final partial chunk. The same chunker supports both materializing a chunk and skipping one while coordinating parallel work.

`next_chunk_index` is therefore part of the coverage state machine. Advancing the source iterator without advancing that index makes subsequent sizing logic describe the wrong region.

## Intended invariant

For both `populate_next_chunk` and `skip_next_chunk`:

```text
current = next_chunk_index
consume exactly source_range(current)
next_chunk_index = current + 1
```

Over the complete run, source ranges must be ordered, disjoint, and cover every required I/T event exactly once, including left padding and the final partial chunk.

## Failure

Both the fill and skip paths consumed a chunk without incrementing `next_chunk_index`. Later operations continued to apply first-chunk or stale-position sizing rules. In particular, special first-chunk padding could be repeated and final-chunk calculations could target the wrong source region.

Because source position and logical chunk index could drift independently, simply counting emitted chunks would not detect the mismatch.

## Failure flow

1. Populate or skip logical chunk zero.
2. Advance the underlying source cursor but leave `next_chunk_index == 0`.
3. Treat the next source range as another first chunk, reapplying its padding/size convention.
4. Repeat through a final partial region whose expected size is computed from the wrong index.
5. Emit duplicated, omitted, or mis-sized boundary events into proofs that are later multiplied into global RAM closure.

`gpu_prover/src/execution/cpu_worker.rs` actively called both methods in the
production chunk loop. Repeated first-chunk padding/consumption either exhausted
the source incorrectly, emitted malformed boundary chunks, or prevented the
canonical final memory product from closing. No accepting verifier bypass was
established.

## Impact and fix

Multi-chunk inits/teardowns generation could not guarantee exact coverage and could fail global RAM closure. The fix increments `next_chunk_index` on both consume and skip paths.

Every chunking state machine needs a conservation proof: source items in, padding items introduced under an explicit rule, chunks out, and an exhaustion assertion. Parallel skip APIs must maintain the same logical state as fill APIs.

## Regression

- Exercise fill/fill, skip/fill, fill/skip, and skip/skip interleavings through the last chunk.
- Record source ranges and assert ordered disjoint union equals the required source set.
- Cover zero, one, exact-multiple, and partial-final chunk sizes.
- Assert first-chunk padding occurs once and only once.
- Close the global RAM product using the emitted chunks and reject duplicate/omitted source items.

## Reproduction evidence

```sh
git diff d4fc8163d0d6934323af3bcef2b1bafa9064865d 9bb1607452baa6c1c018a47567fcbb4bb8cbbc38 -- gpu_prover/src/execution/tracer.rs
git show d4fc8163d0d6934323af3bcef2b1bafa9064865d:gpu_prover/src/execution/cpu_worker.rs
```
