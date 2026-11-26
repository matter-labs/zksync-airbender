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

    #[cfg(any(test, not(target_arch = "x86_64")))]
    fn flattened_words(&self) -> Option<&[u32]> {
        self.inner.flattened_words()
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

    #[cfg(any(test, not(target_arch = "x86_64")))]
    fn flattened_words(&self) -> Option<&[u32]> {
        match self {
            Self::Recorded(..) => None,
            Self::Flattened(inner) => inner.flattened_words(),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::workers::simulation_runner::tests::{
        addi, lui, nd_read, nd_write, sw, Simulator, HALT, RAM_BASE,
    };
    use riscv_transpiler::vm::FlatResponsesSource;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;

    #[test]
    fn flattened_simulator_responses_restart_for_every_pass() {
        let mut simulator = Simulator::new(&[nd_read(1), nd_write(1), nd_read(2), HALT]);
        let source = FlatResponsesSource::new_with_reads(vec![9, 27]);
        let (source, first, reads) = simulator.run_vm(NonDeterminismWrapper::new(source));
        assert_eq!(reads, [(9, 0), (27, 0)]);
        assert_eq!(first.registers[1].value, 9);
        assert_eq!(first.registers[2].value, 27);
        let (source, second, reads) = simulator.run_vm(source.into_replay_source());
        assert_eq!(reads, [(9, 0), (27, 0)]);
        assert_eq!(first, second);
        let (_, third, reads) = simulator.run_vm(source);
        assert_eq!(reads, [(9, 0), (27, 0)]);
        assert_eq!(first, third);
    }

    #[test]
    #[should_panic(expected = "VM flattened non-determinism exhausted at index 2 (length 2)")]
    fn flattened_simulator_reports_first_exhausted_read() {
        let mut simulator = Simulator::new(&[nd_read(1), nd_read(2), nd_read(3), HALT]);
        let source = FlatResponsesSource::new_with_reads(vec![9, 27]);
        simulator.run_vm(NonDeterminismWrapper::new(source));
    }

    struct FlatWithWrite(FlatResponsesSource);

    impl NonDeterminismCSRSource for FlatWithWrite {
        const PROVIDES_FLATTENED_NON_DETERMINISM: bool = true;

        fn flattened_words(&self) -> Option<&[u32]> {
            self.0.flattened_words()
        }

        fn read(&mut self) -> u32 {
            panic!("flattened reads use the bounded words")
        }

        fn write_with_memory_access<R: RamPeek + ?Sized>(&mut self, _: &R, _: u32) {
            panic!("flattened writes must be skipped")
        }

        fn write_with_memory_access_raw(&mut self, _: &[u32], _: u32) {
            panic!("flattened writes must be skipped")
        }

        fn write_with_memory_access_dyn(&mut self, _: &dyn RamPeek, _: u32) {
            panic!("flattened writes must be skipped")
        }
    }

    #[test]
    fn flattened_simulator_skips_writes() {
        let mut simulator = Simulator::new(&[nd_read(1), nd_write(1), nd_read(2), HALT]);
        let source = FlatWithWrite(FlatResponsesSource::new_with_reads(vec![9, 27]));
        let (_, _, reads) = simulator.run_vm(NonDeterminismWrapper::new(source));
        assert_eq!(reads, [(9, 0), (27, 0)]);
    }

    struct ReadRamOnWrite {
        response: Option<u32>,
        writes: Arc<AtomicUsize>,
    }

    impl NonDeterminismCSRSource for ReadRamOnWrite {
        fn read(&mut self) -> u32 {
            self.response
                .take()
                .expect("callback must receive a write before read")
        }

        fn write_with_memory_access<R: RamPeek + ?Sized>(&mut self, ram: &R, address: u32) {
            self.writes.fetch_add(1, Ordering::Relaxed);
            self.response = Some(ram.peek_word(address));
        }

        fn write_with_memory_access_raw(&mut self, ram: &[u32], address: u32) {
            self.write_with_memory_access(ram, address);
        }

        fn write_with_memory_access_dyn(&mut self, ram: &dyn RamPeek, address: u32) {
            self.write_with_memory_access(ram, address);
        }
    }

    #[test]
    fn simulator_records_memory_dependent_callback_once() {
        let mut simulator = Simulator::new(&[
            lui(1, RAM_BASE),
            addi(2, 0, 19),
            sw(2, 1, 0),
            nd_write(1),
            nd_read(3),
            HALT,
        ]);
        let writes = Arc::new(AtomicUsize::new(0));
        let source = ReadRamOnWrite {
            response: None,
            writes: writes.clone(),
        };
        let (source, first, reads) = simulator.run_vm(NonDeterminismWrapper::new(source));
        assert_eq!(reads, [(0, 0), (19, 0)]);
        assert_eq!(first.registers[3].value, 19);
        assert_eq!(writes.load(Ordering::Relaxed), 1);
        simulator.memory.reset_buffer();
        let (_, second, reads) = simulator.run_vm(source.into_replay_source());
        assert_eq!(reads, [(0, 0), (19, 0)]);
        assert_eq!(first, second);
        assert_eq!(writes.load(Ordering::Relaxed), 1);
    }
}
