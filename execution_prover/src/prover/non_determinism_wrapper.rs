use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::vm::{NonDeterminismCSRSource, RamPeek};

/// Records the values read from the inner source, so the same responses can be served again.
/// A source that provides flattened responses is not read through `read`, so nothing is
/// recorded for it; it is not consumed either, and it is served again as is.
pub(super) struct NonDeterminismWrapper<N> {
    inner: N,
    values: Vec<u32>,
}

impl<N: NonDeterminismCSRSource> NonDeterminismWrapper<N> {
    pub(super) fn new(inner: N) -> Self {
        Self {
            inner,
            values: Vec::new(),
        }
    }

    pub(super) fn into_replay_source(self) -> NonDeterminismReplaySource<N> {
        if N::PROVIDES_FLATTENED_NON_DETERMINISM {
            assert!(self.values.is_empty());
            NonDeterminismReplaySource::Flattened(self.inner)
        } else {
            NonDeterminismReplaySource::Recorded(QuasiUARTSource::new_with_reads(self.values))
        }
    }
}

impl<N: NonDeterminismCSRSource> NonDeterminismCSRSource for NonDeterminismWrapper<N> {
    const PROVIDES_FLATTENED_NON_DETERMINISM: bool = N::PROVIDES_FLATTENED_NON_DETERMINISM;

    fn nondeterminism_as_raw_ptr(&self) -> Option<*const u32> {
        self.inner.nondeterminism_as_raw_ptr()
    }

    fn read(&mut self) -> u32 {
        let value = self.inner.read();
        self.values.push(value);
        value
    }

    fn write_with_memory_access<R: RamPeek + ?Sized>(&mut self, ram: &R, value: u32) {
        self.inner.write_with_memory_access(ram, value)
    }

    fn write_with_memory_access_raw(&mut self, ram: &[u32], value: u32) {
        self.inner.write_with_memory_access_raw(ram, value)
    }

    fn write_with_memory_access_dyn(&mut self, ram: &dyn RamPeek, value: u32) {
        self.inner.write_with_memory_access_dyn(ram, value)
    }
}

/// Serves the responses of the run that went through `NonDeterminismWrapper` once again.
/// The variant is fixed by `N::PROVIDES_FLATTENED_NON_DETERMINISM`.
pub(super) enum NonDeterminismReplaySource<N> {
    Recorded(QuasiUARTSource),
    Flattened(N),
}

impl<N: NonDeterminismCSRSource> NonDeterminismCSRSource for NonDeterminismReplaySource<N> {
    const PROVIDES_FLATTENED_NON_DETERMINISM: bool = N::PROVIDES_FLATTENED_NON_DETERMINISM;

    fn nondeterminism_as_raw_ptr(&self) -> Option<*const u32> {
        match self {
            Self::Recorded(..) => None,
            Self::Flattened(inner) => inner.nondeterminism_as_raw_ptr(),
        }
    }

    fn read(&mut self) -> u32 {
        match self {
            Self::Recorded(inner) => inner.read(),
            Self::Flattened(inner) => inner.read(),
        }
    }

    // writes were already served to the inner source during the recorded run
    fn write_with_memory_access<R: RamPeek + ?Sized>(&mut self, _ram: &R, _value: u32) {}
    fn write_with_memory_access_raw(&mut self, _ram: &[u32], _value: u32) {}
    fn write_with_memory_access_dyn(&mut self, _ram: &dyn RamPeek, _value: u32) {}
}
