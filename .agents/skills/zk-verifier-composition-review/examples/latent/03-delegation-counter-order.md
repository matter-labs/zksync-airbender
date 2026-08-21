# JIT trace callback observed the CSR-family counter before its increment

## Classification

- Confirmed historical latent callback-ordering defect
- Invariant: a callback that snapshots machine counters after an instruction
  must observe every counter increment caused by that instruction
- Component: JIT trace callback at shift/binary CSR delegation boundaries
- Reachability: the callback edge was executable, but the only in-repository
  `ContextImpl` ignored counters in `receive_trace`; no proof-producing consumer
  of the stale callback state was established
- Security character if activated: delegation/family work undercount at a
  chunk-publication boundary
- Fixed by: [`80e37e8`](https://github.com/matter-labs/zksync-airbender/commit/80e37e81e43ffaccf52294a2c3c4957cc2df41e8)
- Vulnerable revision: `137db93f1c88e246454f8c52611457ad53b1dfd8`

## Composition context

The JIT maintains cumulative circuit-family/delegation counters in
`MachineState`. `check_to_save_trace!` can call `ContextImpl::receive_trace`
with that state when a trace buffer fills. A future proof-producing context
could use those counters to decide how much specialized work belongs to the
published trace.

At the vulnerable revision, however, the repository's only implementation was
`DefaultContextImpl`; its `receive_trace` used the trace length and reset the
buffer but ignored `machine_state.counters`. The counter increment still ran
after the callback returned and was present in the final machine state.

## Intended invariant

For every executed CSR-family event `e` and any callback that snapshots
counter state:

```text
execute all trace/delegation effects for e
increment machine_state.counters[e.type] by e.cycles_taken
if chunk is now full:
    invoke receive_trace(trace, state_with_incremented_counter)
```

Across the program, the sum of published counts must equal the specialized delegation rows and the CPU-side requests for each type.

## Failure

The JIT recorded `ShiftBinaryCsr` cycles only after
`check_to_save_trace!`. If the delegated CSR filled the trace buffer, the
callback therefore received a `MachineState` whose counter did not yet include
that instruction. The increment occurred only after the callback returned.

This is an exact observation-order defect, but the historical card previously
overstated it as an emitted manifest mismatch. No manifest was built at this
site, and `DefaultContextImpl::receive_trace` did not inspect the stale field.

## Failure flow

1. Fill a JIT trace so a shift/binary CSR call reaches the boundary.
2. Execute the call and enter `check_to_save_trace!`.
3. Invoke `receive_trace` with the pre-increment counter state.
4. Return from the callback and increment `ShiftBinaryCsr` normally.
5. A future callback that derives per-chunk work from the observed counters
   would undercount the just-published chunk.

The last step had no in-repository consumer in this revision. Final-state
counters remained correct, so neither honest-proof rejection nor verifier
acceptance of missing work was established.

## Impact and fix

The immediate historical impact was a stale value observable through a public
callback interface. The fix records the circuit type and cycle count before any
operation that may invoke that callback. This becomes composition-relevant if a
proof-producing context uses callback-time counters to partition work.

Composition review must include producer lifecycle edges—flush, rotate,
enqueue, serialize—but must also prove that a real consumer observes the stale
state before assigning vulnerability impact.

## Why this is latent

Repository-wide search at `137db93f` found only `DefaultContextImpl` as an
in-repository implementation of the callback. Its `receive_trace` ignores
`machine_state.counters`; proof orchestration did not use this JIT callback to
publish a counter manifest. The broken ordering was concrete, but its harmful
observation required a consumer that did not yet exist.

## Regression

- End a trace exactly on a shift/binary CSR delegation and inspect the callback's
  counter snapshot.
- Repeat one row before and one row after the boundary.
- Add a proof-producing callback test before connecting counters to chunk
  manifests or specialized-proof allocation.
- Require final cumulative counters and every callback delta to conserve all
  executed events.

## Reproduction evidence

```sh
git diff 137db93f1c88e246454f8c52611457ad53b1dfd8 80e37e81e43ffaccf52294a2c3c4957cc2df41e8 -- riscv_transpiler/src/jit/impls.rs
git grep -n 'impl.*ContextImpl' 137db93f1c88e246454f8c52611457ad53b1dfd8 -- '*.rs'
```
