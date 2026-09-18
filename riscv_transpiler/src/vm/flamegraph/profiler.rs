use std::collections::HashMap;

use rayon::prelude::*;

use super::collapse::build_collapsed_stack_lines;
use super::config::{FlamegraphConfig, FlamegraphSampleStats};
use super::ram::FlamegraphReadableRam;
use super::stacktrace::collect_stacktrace_into;
use super::symbolizer::Addr2LineContext;
use crate::vm::{Counters, State};

/// Coordinates the flamegraph pipeline:
/// 1) during execution, unwind the frame-pointer chain of every sampled cycle and
///    count identical raw stacks, so memory grows with the number of distinct
///    stacks rather than with the number of samples,
/// 2) once execution finishes, symbolize the distinct addresses and collapse the
///    distinct stacks in parallel (rayon's global pool), then render.
pub struct VmFlamegraphProfiler {
    config: FlamegraphConfig,
    symbol_binary: Vec<u8>,
    /// Distinct raw stacks (sampled `pc` first, then callsite addresses up the
    /// chain) with the number of samples that produced each of them.
    stacks: HashMap<Vec<u32>, usize>,
    /// Reused unwinding buffer; a stack is only copied out of it on its first
    /// occurrence.
    scratch: Vec<u32>,
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
            stacks: HashMap::new(),
            scratch: Vec::with_capacity(64),
            stats: FlamegraphSampleStats::default(),
        })
    }

    pub fn stats(&self) -> FlamegraphSampleStats {
        self.stats
    }

    /// Number of distinct raw stacks seen so far.
    pub fn distinct_stacks(&self) -> usize {
        self.stacks.len()
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

        collect_stacktrace_into(state, ram, &mut self.scratch);
        if self.scratch.is_empty() {
            // Empty stacks are expected when we cannot reconstruct a valid frame
            // chain; they are tracked via stats but not emitted.
            return;
        }
        self.stats.samples_collected += 1;

        // Look up by slice first so a repeated stack costs a hash and a compare,
        // and allocates nothing.
        if let Some(count) = self.stacks.get_mut(self.scratch.as_slice()) {
            *count += 1;
        } else {
            self.stacks.insert(self.scratch.clone(), 1);
        }
    }

    pub fn write_flamegraph(&mut self) -> std::io::Result<()> {
        // Symbolization is deferred to here to keep execution-time sampling
        // overhead predictable and low. Validate the symbols file once up front
        // so a broken file is reported as an error rather than an empty graph.
        Addr2LineContext::new(&self.symbol_binary)?;

        let stacks: Vec<(&[u32], usize)> = self
            .stacks
            .iter()
            .map(|(stack, count)| (stack.as_slice(), *count))
            .collect();

        // Every address is symbolized exactly once, in parallel. The addr2line
        // context is not shareable across threads, so each rayon worker builds
        // its own from the same binary.
        let mut addresses: Vec<u32> = stacks
            .iter()
            .flat_map(|(stack, _)| stack.iter().copied())
            .collect();
        addresses.sort_unstable();
        addresses.dedup();
        let symbols: HashMap<u32, Vec<String>> = addresses
            .par_iter()
            .map_init(
                || Addr2LineContext::new(&self.symbol_binary).ok(),
                |symbolizer, pc| {
                    let frames = match symbolizer {
                        Some(symbolizer) => symbolizer.collect_frames(*pc),
                        None => Vec::new(),
                    };
                    (*pc, frames)
                },
            )
            .collect();

        let collapsed_lines = build_collapsed_stack_lines(&stacks, &symbols);

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
        self.stacks.clear();

        Ok(())
    }
}
