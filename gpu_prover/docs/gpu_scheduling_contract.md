# GPU Scheduling Contract

This contract governs the async scheduling model used by GPU prover subsystems
(GKR, WHIR, and related proving workflows). It does **not** cover higher-level
orchestration concurrency.

## Stream ordering

All GPU prover allocations, frees, callbacks, descriptor uploads, and kernel
launches are logically ordered on the **exec stream**. The stream serializes
execution, so no explicit synchronization is needed between these operations.

## Memory lifetime rules

There are three categories of memory, each with distinct lifetime semantics:

### Device allocations

Device allocations are **stream-ordered**: their logical lifetime is determined
by the already-queued exec-stream work, not by Rust ownership. A
`DeviceAllocation` handle may be dropped after scheduling returns — the
GPU-side data remains valid for all previously enqueued operations.

### Transient host allocations

Allocated via `alloc_transient_host_uninit_slice`. These follow the **same
stream-ordered lifetime** as device allocations. They are used to stage data
for async H2D copies and callback-populated uploads. Once the copy or callback
is enqueued on the exec stream, the transient buffer's lifetime is governed by
the stream, not by Rust's `Drop`.

### Persistent host allocations

Allocated via `alloc_host_uninit_slice`. These **survive beyond scheduling** and
are owned by the enclosing prover job. They are used for proof output buffers
where the host must read back results after the exec stream completes. They must
remain alive until the results have been consumed on the CPU side.

## Callback restrictions

Host callbacks (the `Callbacks` system) execute on a CPU thread when the stream
reaches their enqueue point. They may **only** compute challenge-dependent host
data (e.g., filling descriptor buffers with transcript-derived challenges).

Callbacks must **not**:
- Call any CUDA API — the CUDA runtime itself will return an error if a CUDA
  API call is made from within a stream callback.
- Create or destroy any allocation backed by one of the context's memory pools
  (device or host). Pool operations are not safe to perform from callback
  context.
