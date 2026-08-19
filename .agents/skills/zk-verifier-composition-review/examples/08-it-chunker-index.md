# Setup/teardown chunk index never advanced

## Classification

- Confirmed historical chunk-coverage bug
- Fixed by: [`9bb1607`](https://github.com/matter-labs/zksync-airbender/commit/9bb1607452baa6c1c018a47567fcbb4bb8cbbc38), PR [#85](https://github.com/matter-labs/zksync-airbender/pull/85)
- Vulnerable revision: `d4fc8163d0d6934323af3bcef2b1bafa9064865d`

## Failure

`SetupAndTeardownChunker` filled or skipped a chunk without incrementing `next_chunk_index`. Final-chunk sizing and subsequent reads therefore continued to use the first chunk's position.

## Impact and fix

Multi-chunk inits/teardowns could duplicate, skip, or mis-size address events, preventing or corrupting global RAM closure. The fix increments on both consume and skip paths.

## Regression

Exercise fill/skip interleavings through the last partial chunk and assert each source item is covered exactly once.

```sh
git diff d4fc8163d0d6934323af3bcef2b1bafa9064865d 9bb1607452baa6c1c018a47567fcbb4bb8cbbc38 -- gpu_prover/src/execution/tracer.rs
```
