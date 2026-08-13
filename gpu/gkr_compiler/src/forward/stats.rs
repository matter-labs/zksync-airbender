//! Metrics collected from emitted forward programs.

#[derive(Clone, Debug, Default, PartialEq)]
pub(crate) struct CompileStats {
    pub instrs: usize,
    pub dram_traffic: usize,
}
