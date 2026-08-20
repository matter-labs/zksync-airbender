# A delegation chunk could be published before its circuit counter

## Classification

- Confirmed historical cross-chunk construction bug
- Invariant: published chunk metadata accounts for every delegation row contained in that chunk
- Component: JIT trace production at shift/binary CSR delegation boundaries
- Security character: prover-side manifest/trace inconsistency; outer-verifier risk depends on whether missing work is independently derived
- Fixed by: [`80e37e8`](https://github.com/matter-labs/zksync-airbender/commit/80e37e81e43ffaccf52294a2c3c4957cc2df41e8)
- Vulnerable revision: `137db93f1c88e246454f8c52611457ad53b1dfd8`

## Composition context

Delegation is split across CPU execution chunks and specialized circuit proofs. The trace producer records how many cycles of each delegation circuit type occurred so downstream orchestration can allocate, route, and prove the matching specialized work. Chunk publication is a state boundary: once a completed trace is handed off, all metadata describing its rows must already be finalized.

The `check_to_save_trace!` macro could publish a full chunk. Any bookkeeping placed after that call belongs to the next producer state even if it conceptually describes the just-executed instruction.

## Intended invariant

For every executed delegation event `e`:

```text
append CPU/delegation interaction rows for e
increment chunk.circuit_type_count[e.type] by e.cycles_taken
if chunk is now full:
    publish trace plus finalized count manifest atomically
```

Across the program, the sum of published counts must equal the specialized delegation rows and the CPU-side requests for each type.

## Failure

The JIT recorded `ShiftBinaryCsr` cycles only after `check_to_save_trace!`. If the CSR delegation completed exactly at a chunk boundary, the macro could release the chunk before its circuit-type counter was updated. The trace rows and metadata visible to downstream proving then described different sets of work.

This is a classic publication-order bug: all local statements eventually execute, but the state mutation occurs after ownership of the affected object may have transferred.

## Failure flow

1. Fill a CPU trace so a shift/binary CSR call produces the boundary row.
2. Execute the call and reach `check_to_save_trace!`.
3. Publish the full trace and its still-old delegation-count manifest.
4. Increment the counter only after publication, potentially on reset/new-chunk state or too late for the consumer.
5. Downstream orchestration underallocates or misroutes the specialized delegation proof relative to the CPU request set.

If the verifier derives required delegation multiplicity solely from prover-supplied manifests, this class can become a missing-participant soundness bug. If global memory/delegation closure independently exposes the mismatch, it becomes honest-proof failure. Both paths must be checked rather than assumed.

## Impact and fix

Boundary-aligned executions could publish a chunk whose rows and circuit-participation metadata disagreed, threatening completeness of delegation coverage and causing nondeterministic proof failures or undercounting. The fix records the circuit type and cycle count before any operation that may save/publish the trace.

Composition review must include producer lifecycle edges—flush, rotate, enqueue, serialize—not only verifier arithmetic. Metadata that controls which proofs exist is part of the global soundness surface.

## Regression

- End a trace exactly on a shift/binary CSR delegation and compare row-derived counts with the emitted manifest.
- Repeat one row before and one row after the boundary.
- Aggregate several chunks and require per-type CPU request count = manifest count = specialized proof row count.
- Exercise both synchronous and queued/asynchronous publication paths.
- Reject a final statement whose manifest omits a delegation participant that appears in CPU memory/delegation contributions.

## Reproduction evidence

```sh
git diff 137db93f1c88e246454f8c52611457ad53b1dfd8 80e37e81e43ffaccf52294a2c3c4957cc2df41e8 -- riscv_transpiler/src/jit/impls.rs
```
