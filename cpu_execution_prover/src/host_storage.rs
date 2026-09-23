use riscv_transpiler::jit::{JitRunnerRam, MemoryHolder, TraceChunk};
use std::alloc::Global;
use std::ops::{Deref, DerefMut};

/// Guest RAM for one simulation; `MemoryHolder::allocate_zeroed` owns the
/// layout, including its 2 MiB alignment.
pub struct BoxedMemoryHolder(Box<MemoryHolder>);

impl BoxedMemoryHolder {
    pub(crate) fn new(ram_config: JitRunnerRam) -> Self {
        Self(MemoryHolder::allocate_zeroed(ram_config, Global))
    }
}

impl Deref for BoxedMemoryHolder {
    type Target = MemoryHolder;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for BoxedMemoryHolder {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

pub struct BoxedTraceChunk(Box<TraceChunk>);

impl Default for BoxedTraceChunk {
    fn default() -> Self {
        // SAFETY: `TraceChunk` is plain data whose all-zero bit pattern is the
        // empty chunk; zeroing in place avoids moving megabytes through the stack.
        Self(unsafe { Box::<TraceChunk>::new_zeroed().assume_init() })
    }
}

impl Deref for BoxedTraceChunk {
    type Target = TraceChunk;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for BoxedTraceChunk {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
