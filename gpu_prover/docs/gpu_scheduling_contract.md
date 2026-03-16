# GPU Scheduling Contract

This contract governs the async scheduling model used by GPU prover subsystems
(GKR, WHIR, and related proving workflows). It does **not** cover higher-level
orchestration concurrency.

## Stream ordering

All GPU prover allocations, frees, callbacks, H2D/D2H copies and kernel
launches are logically ordered on the **exec stream**. The stream serializes
execution, so no explicit synchronization is needed between these operations.

## Memory lifetime rules

There are three categories of memory, each with distinct lifetime semantics:

### Device allocations

Device allocations are **stream-ordered**: their logical lifetime is determined
by the already-queued exec-stream work, not by Rust ownership. A
`DeviceAllocation` handle may be dropped after scheduling returns — the
GPU-side data remains valid for all previously enqueued operations.

### Host allocations

Allocated via `alloc_host_uninit_slice` / `alloc_host_uninit`. All context host
allocations follow the **same stream-ordered lifetime** as device allocations.

The logical lifetime of a host allocation is defined by stream execution order:

- Once all stream operations that *use* a buffer have been **scheduled** (not
  completed), the Rust handle may be dropped. Pool recycling is safe because any
  subsequent write to a recycled pool block is enqueued via a callback that runs
  after the current scheduling point — stream ordering prevents races.

- The only hard Rust-lifetime obligation: a handle must **not** be dropped
  before the stream operation that holds a raw `UnsafeAccessor` pointer into it
  has been scheduled.

**Caller obligations:**

- Writes to a host buffer must go through the callback system, not through
  synchronous CPU writes during the scheduling phase. Synchronous reads of host
  pool memory during scheduling are equally forbidden.

- H2D staging buffers (written by callback + copied to device) may be dropped
  immediately after `memory_copy_async` is scheduled.

- D2H readback buffers (copied from device, then read by a subsequent callback)
  must remain alive until the read callback is scheduled.

**Proof output buffers**: All proof data is assembled inside callbacks into
non-pool heap memory (`Vec`, `BTreeMap`, `Arc<Mutex<Option<Proof>>>`). No
context host allocation needs to outlive the scheduling phase.

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
