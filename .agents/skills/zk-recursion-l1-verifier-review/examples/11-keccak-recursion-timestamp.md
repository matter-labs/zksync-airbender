# Keccak recursion boundary timestamp was one cycle late

## Classification

- Confirmed historical recursive public-state bug
- Boundary: delegated Keccak execution → register-memory events and recursion-visible terminal machine state
- Component: `keccak_special5` x10/x11 timestamp assignment
- Security character: an implementation/replay transition disagreed with the zero-indexed internal-call schedule
- Fixed by: [`93e124e`](https://github.com/matter-labs/zksync-airbender/commit/93e124e704bd330795288ab9800db41c495a0441)
- Vulnerable revision: `38baa31aec8ed87041c5fcc98bd9b8c15a563434`

## Boundary context

Delegated Keccak expands one architectural operation into a fixed number of internal calls. Memory/register events inside the delegation use offsets from the entry timestamp, while the outer VM cycle still performs its default post-cycle transition. Recursion and global-memory composition depend on every implementation agreeing which component owns the final increment.

For `NUM_CALLS` zero-indexed internal calls, the last call index is `NUM_CALLS - 1`. Its x10/x11 events occur at:

```text
entry_timestamp + (NUM_CALLS - 1) * TIMESTAMP_STEP + 3
```

The next architectural timestamp is a separate outer-state transition.

## Failure

The Keccak delegation VM placed the final x10/x11 events at `entry + NUM_CALLS * TIMESTAMP_STEP + 3`, one internal-call stride beyond the last valid call. This effectively charged the final progression twice: once in the delegation offset and once in the outer cycle's normal transition.

## Failure flow

1. Enter the Keccak delegation at timestamp `t`.
2. Circuit/replayer events enumerate internal calls `0 .. NUM_CALLS-1`.
3. The vulnerable VM assigns the terminal return-register events using the nonexistent call index `NUM_CALLS`.
4. The outer machine applies its ordinary after-cycle update.
5. Register last-access timestamps, global memory tuples, and the recursion-visible terminal state no longer describe the same execution boundary.

With an independent circuit/verifier enforcing the canonical memory/state transition, this is normally an honest-prover/replay failure. A false-acceptance claim requires showing that all accepting implementations share the late timestamp while a settlement consumer interprets it canonically; do not infer that from producer parity alone.

## Impact and fix

The terminal register state could not compose cleanly with the delegation's memory events and the following chunk/recursive state. The fix uses `(NUM_CALLS - 1) * TIMESTAMP_STEP + 3`, leaving the outer transition to advance state exactly once.

This class should be audited as an ownership problem: list every implicit and explicit timestamp increment and prove that each transition is represented once across VM, trace, delegation circuit, memory argument, recursion output, and L1 public input.

## Regression

- Compare VM, replayer, circuit output, global memory events, and recursion public state for first and final internal calls.
- Compose a Keccak chunk directly before and after a non-Keccak chunk and check exact timestamp continuity.
- Check x10 and x11 last-access timestamps independently.
- Exercise entry timestamps near limb boundaries and the maximum supported range.
- Assert algebraically that the final internal-call index is `NUM_CALLS-1` and the outer update is applied once.

## Reproduction evidence

```sh
git diff 38baa31aec8ed87041c5fcc98bd9b8c15a563434 93e124e704bd330795288ab9800db41c495a0441 -- riscv_transpiler/src/vm/delegations/keccak_special5.rs
```
