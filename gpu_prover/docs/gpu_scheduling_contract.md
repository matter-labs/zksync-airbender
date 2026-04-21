# GPU Scheduling Contract

This contract governs the async scheduling model used by GPU prover subsystems
(GKR, WHIR, and related proving workflows). It does **not** cover higher-level
orchestration concurrency.

## Streams

The prover maintains four streams:

- **exec stream** (`exec_stream`): the single reference stream for all GPU work.
  Kernel launches, pool allocations, pool frees, and host callbacks are all
  ordered relative to this stream. When the contract says "stream-ordered", it
  always means exec-stream-ordered.

- **H2D stream** (`h2d_stream`): an auxiliary stream used to overlap
  host-to-device transfers with exec-stream compute. It is **not** the default
  path for H2D copies — see *H2D copies* below.

- **D2H stream** (`d2h_stream`): an auxiliary stream used to overlap
  device-to-host transfers (and any host callbacks that consume those D2Hs) with
  exec-stream compute. Ownership is transferred to `d2h_stream` via a fork event
  and returned to `exec_stream` via a join event — see *D2H copies* below.

- **aux stream pool** (`aux_streams`): a fixed-size pool of `AUX_STREAM_POOL_SIZE`
  auxiliary streams (currently 8), used by subsystems that want to dispatch
  independent work in parallel. Consumers pick streams by index and must fork/join
  against exec_stream with explicit events (see rule below). Pool streams have
  no intrinsic ordering with each other or with exec_stream.

**Rule for auxiliary streams**: any operation on an auxiliary stream
(h2d_stream, d2h_stream, or an aux_streams entry) must be explicitly ordered
with respect to exec_stream using CUDA events. The driver gives independent
streams no implicit ordering guarantees.

## Stream ordering

All kernel launches, pool allocations, pool frees, and host callbacks are
logically ordered on the **exec stream**. The stream serializes these
operations, so no explicit synchronization is needed between them.

H2D copies are an exception when routed through h2d_stream — they require
explicit event fencing (see *H2D copies* below).

## Memory lifetime

Device allocations and host allocations share **identical** lifetime semantics.

### Access rule

Pool-backed allocations (device and host) are **reservations for stream-side
access**. Every read and write must be expressed as a stream operation — a
kernel launch, `memory_copy_async`, or a host callback scheduled via
`Callbacks::schedule` / `launch_host_fn`.

**The scheduling thread** — the Rust code currently enqueueing work — **must
NOT dereference the memory.** That includes raw pointers, `UnsafeAccessor::get()`,
`UnsafeMutAccessor::get_mut()`, `&*host_alloc`, slice indexing,
`copy_from_slice`, and any other direct access. The scheduling thread has no
synchronization with the stream: a previously-scheduled op may still be
executing through the same pointer (or its DMA not yet complete), and the host
pool allocator is not stream-aware — a freshly-allocated block may still be
the target of an unfinished DMA from its prior owner.

A common mistake is to fill a host staging buffer with `.copy_from_slice(...)`
right after allocating it, then enqueue the `memory_copy_async`. This appears
to work when the stream is idle but breaks as soon as the buffer's pool block
has recently been recycled: the scheduling-thread overwrite races the prior
owner's outstanding DMA.

Accessors (`UnsafeAccessor`, `UnsafeMutAccessor`) exist to be **captured by
value into stream-scheduled closures** or passed into `memory_copy_async`
slots. Dereferencing them (`get()`, `get_mut()`) is only valid inside a
stream-scheduled operation. The scheduling thread treats them as opaque.

### Lifetime rules

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
**scheduled**. These accessors are for capture into stream-scheduled closures
or into the source/dest slots of `memory_copy_async`; dereferencing them
(`get()`, `get_mut()`) is only valid inside a stream op.

**H2D staging buffers**: fill the buffer by scheduling a host callback that
writes to it (via an `UnsafeMutAccessor` captured by the closure). The callback
runs as a stream op, so the subsequent `memory_copy_async` reads what the
callback wrote. Once the memcpy is scheduled, the host handle may be dropped.
**Do not fill the buffer from the scheduling thread.**

**D2H readback buffers**: consume the buffer by scheduling a host callback that
reads it after the `memory_copy_async` has written it. The handle must remain
alive until the consuming callback has been scheduled on exec_stream. **Do not
read the buffer from the scheduling thread.**

**Proof output buffers**: all proof data is assembled inside exec-stream
callbacks into non-pool heap memory (`Vec`, `BTreeMap`, `Option<Proof>` held in
owned host-backed state). No context allocation needs to outlive the scheduling
phase.

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

## D2H copies

D2H copies can be scheduled on either stream:

**On exec_stream (default)**: call `memory_copy_async` directly on exec_stream.
No additional fencing is required.

**On d2h_stream (for copy/compute overlap)**: follow the fork/join/drop rules
below. This is worthwhile when the D2H source is written well before any host
consumer reads the destination, and meaningful exec-stream compute can run in
parallel with the transfer.

### Fork/join/drop ownership rules

Pool-backed `DeviceAllocation` and `HostAllocation` handles are always allocated
and dropped with **exec_stream** ordering; that never changes. A secondary
stream (h2d_stream, d2h_stream, or an aux_streams entry) may access these
allocations between a fork event and a join event, after which ordering returns
to exec_stream for the drop.

1. **Fork**: exec_stream records a `CudaEvent` after the last op that writes the
   source; the secondary stream calls `wait_event` on that event before issuing
   its first op on the source.
2. **Join**: the secondary stream records a `CudaEvent` after its last op on
   any shared buffer; exec_stream calls `wait_event` on that event before any
   subsequent op that conflicts with the secondary stream's activity (see
   write-exclusivity below) and before the allocation's Rust-level drop.
3. **Drop always on exec_stream**: pool-backed allocations are freed on
   exec_stream regardless of which streams accessed them. The Rust-level drop
   must occur after the join wait has been scheduled on exec_stream;
   stream-ordered pool free then guarantees the block is not recycled until the
   secondary stream has finished. Skipping the join before drop is a
   use-after-free.
4. **Write-exclusivity**: within a fork/join window, writes to any shared
   buffer (pool-backed allocation or `UnsafeMutAccessor` target such as shared
   host state) must be done by exactly one stream. Concurrent reads across
   streams are fine; concurrent writes, or a read on one stream racing a write
   on another, are not. If the secondary stream writes a buffer, exec_stream
   must not also write (or read) it inside the window. If both streams only
   read, no coordination beyond fork/join is needed.

```text
exec_stream:   kernels write source buffer S and/or update shared host state X
exec_stream:   record E_src_ready                ("S is written")
d2h_stream:    wait_event(E_src_ready)           ("don't read S before it's written")
d2h_stream:    memory_copy_async(H, S)           ("D2H into pinned host H")
d2h_stream:    schedule consumer callback        ("reads H, writes X")
d2h_stream:    record E_d2h_done                 ("X updated, H complete")
exec_stream:   wait_event(E_d2h_done)            ("don't read X or drop S yet")
exec_stream:   (subsequent ops / S drop)
```

The E_src_ready fence ensures the secondary stream does not read S before
exec_stream has finished writing it. The E_d2h_done fence ensures exec_stream
does not read X, recycle H's pool block, or free S before the secondary stream
has finished with them.

**CUDA event handle lifetime**: `cudaEventRecord` and `cudaStreamWaitEvent`
hold internal refcounts. The Rust `CudaEvent` handle may be dropped immediately
after its last `record` / `wait_event` call — no explicit keepalive is needed.

**HostAllocation keepalive across streams**: pinned host slabs must live until
their last scheduled op on any stream. Handles stored in execution keepalive
structs automatically satisfy this because those structs outlive the
final join.

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

`prove()` itself must stay enqueue-only: it may add stream waits/fences/events,
but it must not block the host thread waiting for exec_stream progress. Host
blocking is reserved for `GpuGKRProofJob::finish()` via `is_finished_event`.

In particular, debug or profiling instrumentation inside `prove()` must not
introduce `stream.synchronize()` or similar host waits just to sample memory
usage or timing mid-workflow.

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
