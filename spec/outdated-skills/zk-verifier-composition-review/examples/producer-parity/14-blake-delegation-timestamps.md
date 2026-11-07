# Blake delegation timestamps used the wrong round count

## Classification

- Producer-parity history: confirmed historical delegation/state-composition bug
- Invariant: CPU state, artificial delegation reads, and specialized Blake work share one round-indexed timestamp schedule
- Component: Blake2 replay and VM delegation implementations
- Security character: confirmed honest-proof/replay completeness failure for
  reduced and full round modes
- Fixed by: [`e30029f`](https://github.com/matter-labs/zksync-airbender/commit/e30029fb28b99e2146652c746d2ece6fd4953919)
- Vulnerable revision: `26cde91b9446226414e73b12350d21e0195f80c4`

## Composition context

A Blake delegation call represents several internal rounds while connecting CPU register state and delegated memory events. Full mode uses ten rounds and reduced mode seven. With zero-based round indexing, the final round occurs at offset `num_rounds - 1`, and final register writes/read upper bounds use that last round's timestamp plus the within-cycle register slot.

The same schedule must be implemented in normal VM execution, replay, delegation data generation, and circuit expectations. Borrowing constants from another precompile silently changes the global state history.

## Intended invariant

For entry timestamp `t`:

```text
last_round_timestamp = t + (num_rounds - 1) * TIMESTAMP_STEP
final x10/x11/x12 timestamp = last_round_timestamp + 3
upper_bound_read_timestamp = last_round_timestamp + 3
artificial_read_timestamp follows the declared ordering after that bound
num_rounds = 7 in reduced mode, 10 in full mode
```

All artificial reads and final register values must compose at this same boundary.

## Failure

The replay path calculated `upper_bound_read_timestamp` using
`NUM_DELEGATION_CALLS_FOR_KECCAK_F1600` instead of Blake's actual `num_rounds`.
That value determined the artificial RAM-read timestamp, not merely a debug
bound. Separately, the VM placed final x10/x11/x12 timestamps at
`t + num_rounds * TIMESTAMP_STEP + 3`, one full step after the zero-based final
round.

The two errors made Blake's CPU-side final state, replay-generated delegation data, and specialized round schedule disagree. Reduced and full modes amplified the problem differently because their correct counts are seven and ten.

## Failure flow

1. Enter a Blake delegation at timestamp `t`.
2. Specialized work accounts for rounds `0 .. num_rounds-1`.
3. Replay computes an artificial-read bound from Keccak's unrelated call count.
4. VM stamps final registers using `num_rounds` rather than `num_rounds-1`.
5. Global RAM/machine-state composition attempts to join events whose purported final times do not coincide.

Depending on which implementation produced or checked each boundary, this causes honest proof failure or an inconsistent history that must be rejected by timestamp and memory closure. The historical fix is strong evidence of parity/correctness, not by itself proof of accepted timestamp forgery.

## Impact and fix

Delegation memory events and CPU final registers did not meet at the same logical time. The fix uses the mode-specific `num_rounds - 1` expression for both replay upper bounds and VM final register timestamps and clarifies the final-value variable naming.

Audit each precompile/delegation from a shared event timeline. Constants with similar names from Keccak, Blake, SHA, or other circuits are not interchangeable even when their APIs match.

## Regression

- Test reduced (7-round) and full (10-round) Blake in replay and non-replay modes.
- Compare every artificial read, final register timestamp, and final x12 value.
- Assert the final timestamp difference between modes equals three `TIMESTAMP_STEP`s.
- Test entry timestamps near limb/counter boundaries.
- Compose a CPU request and specialized Blake proof into the full memory/state closure, not only local replay equality.

## Reproduction evidence

```sh
git diff 26cde91b9446226414e73b12350d21e0195f80c4 e30029fb28b99e2146652c746d2ece6fd4953919 -- riscv_transpiler/src/replayer/delegations/blake2_round_function.rs riscv_transpiler/src/vm/delegations/blake2_round_function.rs
```
