# GPU Scheduling Contract

This contract governs the async scheduling model used by GPU prover subsystems
(GKR, WHIR, and related proving workflows). It does **not** cover higher-level
orchestration concurrency.

## Streams

The prover maintains three streams:

- **exec stream** (`exec_stream`): the single reference stream for all GPU work.
  Kernel launches, pool allocations, pool frees, and host callbacks are all
  ordered relative to this stream. When the contract says "stream-ordered", it
  always means exec-stream-ordered.

- **H2D stream** (`h2d_stream`): an auxiliary stream used to overlap
  host-to-device transfers with exec-stream compute. It is **not** the default
  path for H2D copies — see *H2D copies* below.

- **aux stream** (`aux_stream`): allocated but currently unused.

A dedicated D2H stream may be added in the future to overlap device-to-host
transfers with exec work, following the same pattern as h2d_stream.

**Rule for auxiliary streams**: any operation on an auxiliary stream must be
explicitly ordered with respect to exec_stream using CUDA events. The driver
gives independent streams no implicit ordering guarantees.

## Stream ordering

All kernel launches, pool allocations, pool frees, and host callbacks are
logically ordered on the **exec stream**. The stream serializes these
operations, so no explicit synchronization is needed between them.

H2D copies are an exception when routed through h2d_stream — they require
explicit event fencing (see *H2D copies* below).

## Memory lifetime

Device allocations and host allocations share **identical** lifetime semantics.

**Stream-ordered lifetime**: the logical lifetime of an allocation is determined
by the already-queued exec-stream work, not by Rust ownership. A handle may be
dropped as soon as all exec-stream operations that *use* it have been
**scheduled** (not completed). The GPU-side data remains valid for all
previously enqueued exec-stream operations; pool recycling is safe because any
subsequent operation on a recycled block is enqueued after the current
scheduling point.

**Hard Rust-lifetime obligation**: a handle must **not** be dropped before any
exec-stream operation that holds a raw pointer into it — via `UnsafeAccessor`,
`UnsafeMutAccessor`, or any struct embedding such a pointer — has been
**scheduled**.

**H2D staging buffers** (written by callback, then copied to device): may be
dropped after `memory_copy_async` is scheduled. The copy holds its own
reference to the source data.

**D2H readback buffers** (copied from device, then read by a subsequent
callback): must remain alive until the read callback has been scheduled on
exec_stream.

**Proof output buffers**: all proof data is assembled inside exec-stream
callbacks into non-pool heap memory (`Vec`, `BTreeMap`,
`Arc<Mutex<Option<Proof>>>`). No context allocation needs to outlive the
scheduling phase.

## H2D copies

H2D copies can be scheduled on either stream:

**On exec_stream (default)**: call `memory_copy_async` directly on exec_stream.
This is the simplest and correct choice when the copied data will be consumed
immediately by a subsequent exec-stream operation, or when copy/compute overlap
is not needed. No additional fencing is required.

**On h2d_stream (for copy/compute overlap)**: use the `Transfer` struct
(`gpu_prover/src/primitives/transfer.rs`) or follow the same two-fence pattern
it implements. This is only worthwhile when meaningful exec-stream compute can
be overlapped with the transfer.

```text
exec_stream: alloc device buffer D
exec_stream: record E_alloc          ("buffer D is allocated")
h2d_stream:  wait_event(E_alloc)     ("don't copy before D exists")
h2d_stream:  memory_copy_async(D, src)
h2d_stream:  schedule keepalive cb   (holds src alive until copy completes)
h2d_stream:  record E_xfer           ("copy complete")
exec_stream: wait_event(E_xfer)      ("don't use D before data arrives")
```

The E_alloc fence ensures h2d_stream does not start writing to a device buffer
before it has been allocated on the exec side. The E_xfer fence ensures exec
kernels do not read a buffer that is still being transferred.

## H2D keepalive callbacks

`Transfer::schedule` places a callback on h2d_stream that holds an `Arc`
reference to the source buffer alive until h2d_stream executes past the copy.
These callbacks are distinct from exec-stream callbacks:

- They do **not** compute challenge data.
- They are not subject to transcript-ordering restrictions.
- They may **not** call CUDA APIs (same rule applies to all stream callbacks).

## Stream fence at end of prove()

At the end of each `prove()` call, two separate things are recorded on
exec_stream:

1. An **exec→h2d fence**: exec_stream records an event; h2d_stream waits for
   it. This prevents the GPU driver or hardware from *back-spilling* h2d_stream
   copies scheduled for the next prove call backwards across the boundary, which
   could cause unwanted implicit synchronizations between otherwise independent
   operations. This fence is about stream ordering only, not allocation lifetime.

2. **`is_finished_event.record(exec_stream)`**: stored in the returned
   `GpuGKRProofJob` so that `finish()` can block the host thread until all GPU
   work for this proof is complete. This is a general completion signal,
   separate from the fence above.

## Callback restrictions

Host callbacks (the `Callbacks` system) execute on a CPU thread when exec_stream
reaches their enqueue point. They may **only** compute challenge-dependent host
data (e.g. filling descriptor buffers with transcript-derived challenges).

Callbacks must **not**:

- Call any CUDA API — the CUDA runtime itself will return an error if a CUDA
  API call is made from within a stream callback.
- Create or destroy any allocation backed by one of the context's memory pools
  (device or host). Pool operations are not safe to perform from callback
  context.
