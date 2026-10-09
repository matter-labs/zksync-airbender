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
- **MUST NOT** pin host memory per request. Small per-request H2D sources go
  through `Transfer::stage` and the context's fixed staging buffer.
- **MUST** consume D2H readback buffers via a scheduled host callback, never
  from the scheduling thread.
- **MUST** fork/join any op on an auxiliary stream (`h2d_stream`)
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
- **Default to `exec_stream`** for copies. Use `h2d_stream` only when meaningful
  H2D overlap justifies the fork/join machinery.

## Streams

`ProverContext` (`gpu/prover_context/src/context.rs`) owns two streams:

- **exec stream** (`exec_stream`): the single reference stream for all GPU work.
  Kernel launches, pool allocations, pool frees, and host callbacks are all
  ordered relative to this stream and serialize against each other without
  explicit synchronization. When the contract says "stream-ordered", it always
  means exec-stream-ordered.

- **H2D stream** (`h2d_stream`): an auxiliary stream used to overlap
  host-to-device transfers with exec-stream compute. It is **not** the default
  path for H2D copies — see *H2D copies* below.

**Rule for H2D work**: operations on h2d_stream must be explicitly ordered
with respect to exec_stream using CUDA events. The driver gives independent
streams no implicit ordering guarantees. All compute kernels use exec_stream.

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

Each `StaticPinnedBox` (`alloc_static_pinned_box_uninit`) is its own
`cudaHostAlloc`, released with `cudaFreeHost` on drop. Use it only for data
allocated once per context or circuit (setup, decoder); per-request sources use
`Transfer::stage` (see *H2D copies*).

**Why a second pool.** The "fill via callback" rule guards against a
scheduling-thread write racing a prior owner's outstanding DMA on a recycled
block. That hazard only exists for buffers the stream *writes*.
Scheduling-time-known H2D inputs — recipe headers and terms, combined-claim
descriptors, lookup-and-constraint constants, similar compiled-kernel inputs
— are never written by the GPU; staging them through a callback is pure
overhead (an extra CPU hop, a serialization point on `exec_stream`, profile
noise).

**Construction invariant.** Fill the buffer with direct scheduling-thread
writes during construction (e.g. `alloc_static_pinned_box_uninit` +
`copy_from_slice`). Once any
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
| Small per-request H2D source                     | `Transfer::stage`          |
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
(`gpu/prover_context/src/transfer.rs`) or follow the same two-fence pattern
it implements. This is only worthwhile when meaningful exec-stream compute can
be overlapped with the transfer.

```text
exec_stream: alloc device buffers D_i
exec_stream: record E_alloc          ("buffers D_i are allocated")
h2d_stream:  fill staging cb         (only if values were staged)
h2d_stream:  wait_event(E_alloc)     ("don't copy before D_i exist"), once per bundle
h2d_stream:  memory_copy_async(D_i, staging or src_i)
h2d_stream:  record E_xfer           ("copies complete")
exec_stream: wait_event(E_xfer)      ("don't use D_i before data arrives")
```

The E_alloc fence ensures h2d_stream does not start writing to a device buffer
before it has been allocated on the exec side. The E_xfer fence ensures exec
kernels do not read a buffer that is still being transferred.

A `Transfer` issues the `E_alloc` wait once, at its first copy or at
`record_transferred`.

**Per-request sources.** Small inputs that change with every request (top bits,
external challenges, the unified memory cap) are recorded with
`Transfer::stage` before any direct copy of the bundle. They are packed into
the context's fixed pinned staging buffer (`H2D_STAGING_BYTES`) by one
`h2d_stream` callback enqueued ahead of the wait, and copied right after it.
Each bundle's fill sits behind every earlier staged copy on the in-order
`h2d_stream`, so all bundles reuse the same buffer.

## D2H copies

D2H copies run on `exec_stream`. Schedule the consumer callback after the copy.
The stream-ordered host-pool destination may be released once that callback is
scheduled. Keep the callback owner alive until stream or event synchronization
confirms completion: the CUDA callback dispatch holds only a weak reference.

## H2D source lifetime

A `Transfer` owns the `Arc` sources of its direct copies and its staging fill
callback. `Transfer::into_keepalive` hands them to the job, which must keep
them until stream or event synchronization confirms completion (`finish()`).
Dropping them sooner can release a source while its copy is in flight, or skip
the fill. This differs from the scheduled-use lifetime of stream-ordered pool
reservations.

The staging fill callback is distinct from exec-stream callbacks:

- It does **not** compute challenge data.
- It is not subject to transcript-ordering restrictions.
- It may **not** call CUDA APIs (same rule applies to all stream callbacks).

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
