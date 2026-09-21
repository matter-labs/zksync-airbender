use fft::GoodAllocator;

/// Allocator backing one finite, reusable host trace block.
///
/// Trace production is bounded by handing producers a fixed number of these
/// blocks and taking one back only once its trace has been consumed, so an
/// implementation must represent a block of *known, finite* capacity — the
/// credit the producer budget is denominated in. `std::alloc::Global` is a
/// legitimate allocator for setup and proof scratch but deliberately does NOT
/// implement this trait: unbounded here would silently remove the backpressure
/// that keeps simulation and consumption in step.
pub trait HostTraceAllocator: GoodAllocator {
    /// Usable bytes in this block. Producers divide it by the row size to size
    /// a chunk, so it must not change over the allocator's lifetime.
    fn capacity(&self) -> usize;
}
