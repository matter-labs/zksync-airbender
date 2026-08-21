# Replay self-loop termination skipped the terminal timestamp increment

## Classification

- Confirmed historical machine-state continuity bug
- Invariant: replay, execution, and circuit traces charge the same timestamp step for every executed cycle
- Component: `replay_basic_unrolled` self-loop termination
- Security character: confirmed honest-proof/replay completeness failure,
  especially at chunk and delegation boundaries
- Fixed by: [`6538ff5`](https://github.com/matter-labs/zksync-airbender/commit/6538ff5a4c58ace853d9c6b7eadc4199579d1097)
- Vulnerable revision: `e30029fb28b99e2146652c746d2ece6fd4953919`

## Composition context

Replay reconstructs machine state and memory events used by later circuit
proving. Each executed instruction consumes one `TIMESTAMP_STEP`, including the
canonical terminal self-loop instruction. The loop saves the instruction's
starting PC as `pc`, executes it, and treats `state.pc == pc` afterward as
termination. The resulting timestamp becomes the starting boundary for later
replay segments/chunks and labels register/RAM events in the global memory
argument.

Stopping is an observation made after a cycle completes; it must not cancel the state transition associated with that cycle.

## Intended invariant

For each loop iteration:

```text
execute instruction at current PC
apply all register, memory, and PC effects
timestamp += TIMESTAMP_STEP
if resulting PC equals the instruction's starting PC:
    return completed post-state
```

After `n` executed cycles, `final_timestamp = initial_timestamp + n * TIMESTAMP_STEP`, independent of why replay stopped.

## Failure

The replayer tested `state.pc == pc` and returned before incrementing the
timestamp. On the terminal self-loop, the cycle modified machine/memory state
but consumed no global time in `state.timestamp`.

This produced a hybrid boundary: post-instruction PC/register values paired with a pre-instruction timestamp. Subsequent chunks could start at a timestamp already used by the terminal cycle, violating the uniqueness/ordering assumptions of state and RAM tuples.

## Failure flow

1. Begin replay at timestamp `t` and execute the terminal self-loop instruction.
2. Apply its PC, register, and memory effects, some labeled within cycle `t`.
3. Observe the stop PC and return with `state.timestamp` still equal to `t`.
4. Start the next replay/proof segment from `t` rather than `t + TIMESTAMP_STEP`.
5. Produce boundary state inconsistent with canonical execution and potentially overlap memory/register timestamps across segments.

The historical result is proof/replay incompleteness. A verifier soundness audit must independently confirm that monotonic timestamp constraints and global memory closure reject any maliciously supplied duplicate/rewound boundary.

## Impact and fix

Final PC/timestamp state and access timing diverged between replay and circuit execution, breaking cross-chunk and delegation composition. The fix increments the timestamp immediately after executing the instruction and only then evaluates the stop condition.

Review every early return, break, exception, trap, and delegation handoff relative to the VM's atomic cycle transition. Boundary APIs should return either a complete pre-state or a complete post-state, never a mixture.

## Regression

- Test one-cycle and multi-cycle replay ending in the canonical self-loop, with
  a non-self-loop instruction as a control.
- Compare final timestamp and every register/RAM event with the canonical VM trace.
- Concatenate two replay segments and assert the second starts at exactly the first's post-cycle timestamp.
- Audit trap, delegation, chunk-full, and any other early exits separately
  against the same complete-cycle rule.
- Verify timestamp monotonicity and global memory closure over the concatenated proof chunks.

## Reproduction evidence

```sh
git diff e30029fb28b99e2146652c746d2ece6fd4953919 6538ff5a4c58ace853d9c6b7eadc4199579d1097 -- riscv_transpiler/src/replayer/mod.rs
git show e30029fb28b99e2146652c746d2ece6fd4953919:prover/src/witness_evaluator/unrolled/mod.rs
```
