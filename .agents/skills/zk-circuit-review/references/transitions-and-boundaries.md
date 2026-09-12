# Transition and Boundary Constraints

## Transition Invariant

Every next-state component must be correctly related to the previous state and the selected operation.

Inspect:

```text
state[i] -> state[i+1]
```

Check each state component independently, including values that are supposed to remain unchanged.

## Boundary Invariant

The first and final states must be bound to the intended values or to the appropriate global argument.

Check:

- initial state
- final state
- program counter
- register state commitments
- initial/final accumulators
- first-row selectors
- last-row selectors
- chunk boundaries
- padding boundaries

A correct transition relation is insufficient if the prover may freely choose the initial state or terminate in an arbitrary final state.

## Chunked Execution

If execution is split into chunks, identify which state continuity requirements are local and which depend on a global or inter-circuit argument.

Local wiring should be checked; system-wide continuity may be marked `REQUIRES_GLOBAL_AUDIT`.
