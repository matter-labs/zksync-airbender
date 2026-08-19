# Blake delegation timestamps used the wrong round count

## Classification

- Confirmed historical delegation/state-composition bug
- Fixed by: [`e30029f`](https://github.com/matter-labs/zksync-airbender/commit/e30029fb28b99e2146652c746d2ece6fd4953919)
- Vulnerable revision: `26cde91b9446226414e73b12350d21e0195f80c4`

## Failure

Blake replay calculated its upper-bound read time with the Keccak delegation-call constant and placed final register timestamps one full `TIMESTAMP_STEP` too late. Reduced and full Blake rounds therefore reported the wrong state boundary.

## Impact and fix

Delegation memory events and the CPU's final register state no longer met at the same timestamp, so the global state/memory argument could fail or compose the wrong history. The fix uses `num_rounds - 1` consistently.

## Regression

Check reduced/full Blake in replay and non-replay modes, comparing every artificial read and final register timestamp.

```sh
git diff 26cde91b9446226414e73b12350d21e0195f80c4 e30029fb28b99e2146652c746d2ece6fd4953919 -- riscv_transpiler/src/replayer/delegations/blake2_round_function.rs riscv_transpiler/src/vm/delegations/blake2_round_function.rs
```
