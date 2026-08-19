# ROM page was omitted from inits/teardowns

## Classification

- Confirmed historical global-memory coverage bug
- Fixed by: [`46c58c9`](https://github.com/matter-labs/zksync-airbender/commit/46c58c9f95179f0f14af4ebe1105e1da4511bbc1)
- Vulnerable revision: `65c3704ffd45a5fdea3185bdabde789d7ecf3c3d`

## Failure

The GPU RAM tracker skipped page zero when counting touched words and producing inits/teardowns. Reads in the ROM region were not represented; the repair includes touched timestamps while forcing teardown values to zero for ROM.

## Impact and fix

The global memory product omitted a reachable address region, so execution accesses and closure did not describe the same set. The fix tracks every page and specializes only the immutable value semantics.

## Regression

Touch ROM and RAM pages in one execution and assert every nonzero timestamp appears once in the I/T stream with the correct value policy.

```sh
git diff 65c3704ffd45a5fdea3185bdabde789d7ecf3c3d 46c58c9f95179f0f14af4ebe1105e1da4511bbc1 -- gpu_prover/src/execution/ram.rs
```
