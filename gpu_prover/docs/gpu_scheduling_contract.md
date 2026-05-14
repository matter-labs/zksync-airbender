# GPU Scheduling Contract

This contract governs the async scheduling model used by GPU prover subsystems
(GKR, WHIR, and related proving workflows). It does **not** cover higher-level
orchestration concurrency.

## Rules at a glance

The rules below are the ones most often violated. They are a summary — the
sections that follow are the source of truth and describe the reasoning,
edge cases, and wiring behind each rule.

- **MUST NOT** dereference pool-backed device or host allocations from the
  scheduling thread. All reads and writes must be expressed as stream ops:
  kernel launches, `memory_copy_async`, or host callbacks scheduled via
  `Callbacks::schedule` / `launch_host_fn`. `UnsafeAccessor::get()` /
  `UnsafeMutAccessor::get_mut()` are only valid inside stream-scheduled
  closures.
- **MUST** fill stream-ordered H2D staging buffers via a scheduled host
  callback (captured `UnsafeMutAccessor`). `.copy_from_slice(...)` right after
  allocation races the prior pool owner's outstanding DMA, even when it
  appears to work.
- **`SchedulerHostAllocator` is the separate pinned host pool for immutable,
  scheduling-time-known H2D sources** (compiled kernel descriptors, recipe
  tables, etc.). Its access rule is **inverted** relative to the stream-ordered
  pool: the scheduling thread writes once during construction, and every stream
  operation thereafter only reads. See *SchedulerHostAllocator* below for the
  construction invariant and what belongs there.
- **MUST** consume D2H readback buffers via a scheduled host callback, never
  from the scheduling thread.
- **MUST** fork/join any op on an auxiliary stream (`h2d_stream` or `d2h_stream`)
  against `exec_stream` with explicit CUDA events. The driver gives independent
  streams no implicit ordering.
- **MUST** allocate and drop pool-backed handles on `exec_stream`. If a
  secondary stream touched the allocation, the `exec_stream` join wait must be
  scheduled before the Rust drop — otherwise it is a use-after-free.
- **MUST** observe write-exclusivity within any fork/join window: exactly one
  stream writes a shared buffer. Concurrent reads are fine; concurrent writes,
  or a read racing a write across streams, are not.
- **MUST** keep a Rust handle alive until every op holding a raw pointer into
  it (via accessors or embedding structs) has been **scheduled**. Scheduling
  is enough — completion is not required.
- **MUST NOT** call any CUDA API from within a host callback, and callbacks
  must not create or destroy pool-backed allocations. Callbacks exist to
  compute challenge-dependent host data only.
- **MUST** keep `prove()` enqueue-only. No `stream.synchronize()`, no host
  blocking for `exec_stream` progress — not even for profiling or logging.
  Host blocking belongs in `GpuGKRProofJob::finish()`.
- **Default to `exec_stream`** for H2D/D2H copies. Use `h2d_stream` /
  `d2h_stream` only when meaningful copy/compute overlap justifies the
  fork/join machinery.

## Streams

The prover maintains three streams:

- **exec stream** (`exec_stream`): the single reference stream for all GPU work.
  Kernel launches, pool allocations, pool frees, and host callbacks are all
  ordered relative to this stream and serialize against each other without
  explicit synchronization. When the contract says "stream-ordered", it always
  means exec-stream-ordered.

- **H2D stream** (`h2d_stream`): an auxiliary stream used to overlap
  host-to-device transfers with exec-stream compute. It is **not** the default
  path for H2D copies — see *H2D copies* below.

- **D2H stream** (`d2h_stream`): an auxiliary stream used to overlap
  device-to-host transfers (and any host callbacks that consume those D2Hs) with
  exec-stream compute. Ownership is transferred to `d2h_stream` via a fork event
  and returned to `exec_stream` via a join event — see *D2H copies* below.

**Rule for auxiliary streams**: any operation on an auxiliary stream
(h2d_stream or d2h_stream) must be explicitly ordered with respect to
exec_stream using CUDA events. The driver gives independent streams no
implicit ordering guarantees.

## Memory lifetime

Device allocations and host allocations share **identical** lifetime semantics.

Two pinned host pools coexist with **opposite** access rules:

- The **stream-ordered host pool** (the default; what *Access rule* and
  *Lifetime rules* below describe) is for any buffer the stream *writes* —
  H2D staging filled in a callback, D2H destinations, mutable scratch. The
  scheduling thread treats it as opaque.
- **`SchedulerHostAllocator`** is for H2D *sources* whose contents are fully
  determined at scheduling time. The scheduling thread writes them once during
  construction, and the stream only reads them. See *SchedulerHostAllocator*
  below.

Unless otherwise stated, "host pool" / "pool-backed" below means the
stream-ordered pool.

### Access rule

Pool-backed allocations (device and stream-ordered host) are **reservations
for stream-side access**. Every read and write must be expressed as a stream
operation — a kernel launch, `memory_copy_async`, or a host callback scheduled
via `Callbacks::schedule` / `launch_host_fn`.

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

**Filling and consuming**: H2D staging is filled by a callback writing through
a captured `UnsafeMutAccessor`; D2H readbacks are consumed by a callback
reading the destination after the `memory_copy_async`. Drop the host handle
once the *next* stream op holding the pointer (the memcpy after a fill, the
consumer callback after a readback) has been **scheduled**. Never fill or read
from the scheduling thread.

**Proof output buffers**: proof data is assembled inside exec-stream callbacks
into non-pool heap memory (`Vec`, `BTreeMap`, owned `Option<Proof>`). No
context allocation needs to outlive the scheduling phase.

### SchedulerHostAllocator

`SchedulerHostAllocator` is the second pinned host pool, with **inverted
access semantics** vs. the stream-ordered pool above: the scheduling thread
writes once during construction, and every stream operation thereafter only
reads.

**Why a second pool.** The "fill via callback" rule guards against a
scheduling-thread write racing a prior owner's outstanding DMA on a recycled
block. That hazard only exists for buffers the stream *writes*.
Scheduling-time-known H2D inputs — recipe headers and terms, combined-claim
descriptors, lookup-and-constraint constants, similar compiled-kernel inputs
— are never written by the GPU; staging them through a callback is pure
overhead (an extra CPU hop, a serialization point on `exec_stream`, profile
noise).

**Construction invariant.** Fill the buffer with direct scheduling-thread
writes during construction (e.g. `scheduler_host_from_slice`). Once any
`memory_copy_async` reading it has been **enqueued**, the buffer is frozen:
no further scheduling-thread mutation, no callback writes, no use as a DMA
destination, no kernel writes. The buffer stays owned by its handle until
drop — it is not stream-recycled into and out of active service the way
stream-ordered blocks are, so a late prior DMA cannot corrupt content nobody
writes again. This is the **only** circumstance in which the scheduling
thread may dereference pinned-host pool memory; the *Access rule* still
holds for everything else.

**What belongs where:**

| Use                                              | Pool                       |
| ------------------------------------------------ | -------------------------- |
| H2D source for transcript-derived challenge data | stream-ordered host pool   |
| H2D source for compiled / scheduling-time data   | `SchedulerHostAllocator`   |
| D2H readback destination                         | stream-ordered host pool   |
| Callback-populated staging                       | stream-ordered host pool   |
| Mutable scratch on the stream side               | stream-ordered host pool   |

Rule of thumb: if a buffer needs **any** stream-side write — DMA target,
callback fill, transcript-dependent content — it does not belong in
`SchedulerHostAllocator`.

**Lifetime and concurrency.** Same scheduled-not-completed rule as the
stream-ordered pool: keep the handle alive until the last H2D reading it has
been scheduled. In practice, attach to a keepalive that outlives all
in-flight prove() work; the pool is concurrent on the allocator side, so
drops may happen on a thread distinct from the scheduling thread. Do not
allocate scheduler-host memory for an empty input — skip the H2D, or keep an
existing one-element dummy device buffer when a kernel signature requires a
valid pointer.

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

> The terminal proof-slab D2H in `prove()` runs on exec_stream because it is
> the last scheduled op before the assembly callback, so there is no
> concurrent exec-stream work to overlap with. Per-layer D2Hs that feed WHIR
> host setup continue to use d2h_stream via the fork/join pattern below.

### Fork/join/drop ownership rules

Pool-backed `DeviceAllocation` and `HostAllocation` handles are always allocated
and dropped with **exec_stream** ordering; that never changes. A secondary
stream (h2d_stream or d2h_stream) may access these allocations between a fork
event and a join event, after which ordering returns to exec_stream for the
drop.

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
4. **Write-exclusivity**: within a fork/join window, exactly one stream
   writes any shared buffer (pool-backed allocation or `UnsafeMutAccessor`
   target such as shared host state); the other side may only read.
   Concurrent reads are fine. If the secondary stream writes, exec_stream
   must not also touch the buffer inside the window.

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

`prove()` itself must stay enqueue-only: stream waits/fences/events are fine,
but no host blocking on exec_stream progress — including for debug or
profiling instrumentation. Host blocking is reserved for
`GpuGKRProofJob::finish()` via `is_finished_event`.

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
