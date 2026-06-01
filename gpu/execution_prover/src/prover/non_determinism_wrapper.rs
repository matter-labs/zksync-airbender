use riscv_transpiler::vm::{NonDeterminismCSRSource, RamPeek};

pub(super) struct NonDeterminismWrapper<N> {
    inner: N,
    values: Vec<u32>,
}

impl<N> NonDeterminismWrapper<N> {
    pub(super) fn new(inner: N) -> Self {
        Self {
            inner,
            values: Vec::new(),
        }
    }

    pub(super) fn into_values(self) -> Vec<u32> {
        self.values
    }
}

impl<N: NonDeterminismCSRSource> NonDeterminismCSRSource for NonDeterminismWrapper<N> {
    fn read(&mut self) -> u32 {
        let value = self.inner.read();
        self.values.push(value);
        value
    }

    fn write_with_memory_access<R: RamPeek>(&mut self, ram: &R, value: u32) {
        self.inner.write_with_memory_access(ram, value)
    }

    fn write_with_memory_access_dyn(&mut self, ram: &dyn RamPeek, value: u32) {
        self.inner.write_with_memory_access_dyn(ram, value)
    }
}
