use std::path::PathBuf;

/// Runtime knobs for VM flamegraph generation.
///
/// We intentionally separate collection (cheap, during execution) from
/// symbolization/rendering (heavier, after execution). These values tune both
/// phases.
#[derive(Clone, Debug)]
pub struct FlamegraphConfig {
    /// ELF/object file that provides symbols and DWARF info for PC resolution.
    pub symbols_path: PathBuf,
    /// Destination SVG written by `inferno`.
    pub output_path: PathBuf,
    /// Controls whether stacks are rendered in reverse order.
    pub reverse_graph: bool,
    /// Collect one sample every `frequency_recip` VM cycles.
    ///
    /// Larger values reduce runtime overhead but may hide short-lived frames.
    pub frequency_recip: usize,
}

impl FlamegraphConfig {
    pub fn new(symbols_path: PathBuf, output_path: PathBuf) -> Self {
        // Defaults bias toward low overhead while keeping a readable graph.
        Self {
            symbols_path,
            output_path,
            reverse_graph: false,
            frequency_recip: 100,
        }
    }
}

/// Sampling counters that help estimate profiler effectiveness.
///
/// `samples_total` tracks how many sampling points were attempted, while
/// `samples_collected` tracks how many produced a non-empty stack trace.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FlamegraphSampleStats {
    pub samples_total: usize,
    pub samples_collected: usize,
}
