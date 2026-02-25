use super::collapse::build_collapsed_stack_lines;
use super::config::{FlamegraphConfig, FlamegraphSampleStats};
use super::ram::FlamegraphReadableRam;
use super::stacktrace::collect_stacktrace_raw;
use super::symbolizer::Addr2LineContext;
use crate::vm::{Counters, State};

/// Coordinates the flamegraph pipeline:
/// 1) collect lightweight raw samples during execution,
/// 2) symbolize and render once execution finishes.
pub struct VmFlamegraphProfiler {
    config: FlamegraphConfig,
    symbol_binary: Vec<u8>,
    raw_frames: Vec<(u32, Vec<u32>)>,
    stats: FlamegraphSampleStats,
}

impl VmFlamegraphProfiler {
    pub fn new(config: FlamegraphConfig) -> std::io::Result<Self> {
        // Zero would both disable progress and cause division-by-zero.
        if config.frequency_recip == 0 {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "frequency_recip must be greater than zero",
            ));
        }

        let symbol_binary = std::fs::read(&config.symbols_path)?;

        Ok(Self {
            config,
            symbol_binary,
            raw_frames: Vec::new(),
            stats: FlamegraphSampleStats::default(),
        })
    }

    pub fn stats(&self) -> FlamegraphSampleStats {
        self.stats
    }

    #[inline(always)]
    pub fn sample_cycle<C: Counters, R: FlamegraphReadableRam>(
        &mut self,
        state: &State<C>,
        ram: &R,
        cycle: usize,
    ) {
        // Sampling is on the VM hot path, so we keep this branch and data
        // collection minimal and defer expensive work to finalization.
        if cycle % self.config.frequency_recip != 0 {
            return;
        }

        self.stats.samples_total += 1;

        let (pc, frames) = collect_stacktrace_raw(state, ram);
        if frames.is_empty() == false {
            // Empty stacks are expected when we cannot reconstruct a valid frame
            // chain; they are tracked via stats but not emitted.
            self.stats.samples_collected += 1;
            self.raw_frames.push((pc, frames));
        }
    }

    pub fn write_flamegraph(&mut self) -> std::io::Result<()> {
        // Symbolization is deferred to here to keep execution-time sampling
        // overhead predictable and low.
        let symbolizer = Addr2LineContext::new(&self.symbol_binary)?;

        let collapsed_lines = build_collapsed_stack_lines(&self.raw_frames, &symbolizer);

        let collapsed_lines = if collapsed_lines.is_empty() {
            // Produce a minimal graph instead of failing when no usable samples
            // were collected.
            vec![String::from("no_samples 1")]
        } else {
            collapsed_lines
        };

        let output_file = std::fs::File::create(&self.config.output_path)?;
        let mut options = inferno::flamegraph::Options::default();
        options.reverse_stack_order = self.config.reverse_graph;
        inferno::flamegraph::from_lines(
            &mut options,
            collapsed_lines.iter().map(String::as_str),
            output_file,
        )
        .map_err(|error| {
            std::io::Error::new(
                std::io::ErrorKind::Other,
                format!("while attempting to generate flamegraph: {error}"),
            )
        })?;

        // The profiler can be reused across VM runs with the same config.
        self.raw_frames.clear();

        Ok(())
    }
}
