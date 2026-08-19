# A delegation chunk could be emitted before its circuit counter

## Classification

- Confirmed historical cross-chunk construction bug
- Fixed by: [`80e37e8`](https://github.com/matter-labs/zksync-airbender/commit/80e37e81e43ffaccf52294a2c3c4957cc2df41e8)
- Vulnerable revision: `137db93f1c88e246454f8c52611457ad53b1dfd8`

## Failure

The JIT recorded the number of cycles attributed to a shift/binary delegation only after `check_to_save_trace!`. At a chunk boundary, that check could hand the completed trace to downstream proving before its circuit-type counter was updated.

## Impact and fix

The emitted chunk's execution rows and its circuit-participation metadata could describe different work. That can misroute or undercount the delegation proof needed to close the global argument. The fix records the counter before any operation that can publish the chunk.

## Regression

End a trace chunk exactly on a shift/binary CSR delegation and compare the emitted counter manifest with the delegation rows. Repeat immediately before and after the boundary.

```sh
git diff 137db93f1c88e246454f8c52611457ad53b1dfd8 80e37e81e43ffaccf52294a2c3c4957cc2df41e8 -- riscv_transpiler/src/jit/impls.rs
```
