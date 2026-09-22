use fft::GoodAllocator;

/// Allocator for one reusable trace block of fixed capacity.
pub trait HostTraceAllocator: GoodAllocator {
    fn capacity(&self) -> usize;
}
