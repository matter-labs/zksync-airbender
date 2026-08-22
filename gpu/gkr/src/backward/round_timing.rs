//! Opt-in CUDA-event recorder for backward sumcheck rounds. Inert unless
//! `GKR_BWD_FIRST3_TIMING_OUT` is set.
//!
//! Event records are enqueue-only on the exec stream (contract-safe).
//! `dump_first3_timing` must run only after the enclosing proof has
//! synchronized; it synchronizes each terminal event before reading.
//!
//! Per layer: a start event, one event after each of the first three round
//! tails (as many as the layer has), and one event after the final round's
//! tail. This yields r0/r1/r2 and the layer's total backward time.

use std::io::Write;
use std::sync::{Mutex, OnceLock};

use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;

pub struct RoundTimingEntry {
    pub kind: &'static str,
    pub thread: String,
    pub layer_idx: usize,
    pub folding_steps: usize,
    pub events: Vec<CudaEvent>,
}

// SAFETY: CUDA event handles are process-global and valid on any host thread.
unsafe impl Send for RoundTimingEntry {}

static OUT_PATH: OnceLock<Option<String>> = OnceLock::new();
static SINK: Mutex<Vec<RoundTimingEntry>> = Mutex::new(Vec::new());

pub fn first3_timing_out() -> Option<&'static str> {
    OUT_PATH
        .get_or_init(|| std::env::var("GKR_BWD_FIRST3_TIMING_OUT").ok())
        .as_deref()
}

pub struct First3Recorder {
    entry: RoundTimingEntry,
    round_marks: usize,
}

impl First3Recorder {
    /// Records the interval-start event immediately; call right before the
    /// layer's round-0 work is scheduled. Returns `None` when disabled.
    pub fn begin(
        kind: &'static str,
        layer_idx: usize,
        folding_steps: usize,
        stream: &CudaStream,
    ) -> CudaResult<Option<Self>> {
        if first3_timing_out().is_none() {
            return Ok(None);
        }
        let start = CudaEvent::create()?;
        start.record(stream)?;
        Ok(Some(Self {
            entry: RoundTimingEntry {
                kind,
                thread: format!("{:?}", std::thread::current().id()),
                layer_idx,
                folding_steps,
                events: vec![start],
            },
            round_marks: 0,
        }))
    }

    /// Records a round-boundary event; call right after the fused tail of
    /// each round. Only the first three rounds are marked.
    pub fn mark_round_end(&mut self, stream: &CudaStream) -> CudaResult<()> {
        if self.round_marks >= 3 {
            return Ok(());
        }
        let event = CudaEvent::create()?;
        event.record(stream)?;
        self.entry.events.push(event);
        self.round_marks += 1;
        Ok(())
    }

    /// Records the layer-end event; call right after the final round's tail.
    pub fn finish(mut self, stream: &CudaStream) -> CudaResult<()> {
        let event = CudaEvent::create()?;
        event.record(stream)?;
        self.entry.events.push(event);
        SINK.lock().unwrap().push(self.entry);
        Ok(())
    }
}

/// Synchronizes, converts, appends JSONL rows to the configured path, and
/// clears the sink. Returns the number of rows written.
pub fn dump_first3_timing() -> Result<usize, Box<dyn std::error::Error>> {
    let Some(path) = first3_timing_out() else {
        return Ok(0);
    };
    let entries = std::mem::take(&mut *SINK.lock().unwrap());
    let mut file = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)?;
    let mut written = 0usize;
    for (sequence, entry) in entries.iter().enumerate() {
        let last = entry
            .events
            .last()
            .ok_or("round timing entry has no events")?;
        last.synchronize()?;
        let mut rounds = Vec::with_capacity(3);
        for pair in entry.events.windows(2).take(entry.events.len() - 2) {
            rounds.push(elapsed_time(&pair[0], &pair[1])?);
        }
        let total = elapsed_time(&entry.events[0], last)?;
        if !(total.is_finite() && rounds.iter().all(|v| v.is_finite())) {
            return Err(format!(
                "non-finite round timing data at sequence {sequence} layer {}",
                entry.layer_idx
            )
            .into());
        }
        let rounds_json = rounds
            .iter()
            .map(|v| v.to_string())
            .collect::<Vec<_>>()
            .join(",");
        writeln!(
            file,
            "{{\"sequence\":{},\"kind\":{:?},\"thread\":{:?},\"layer_idx\":{},\"folding_steps\":{},\"round_ms\":[{}],\"total_ms\":{}}}",
            sequence, entry.kind, entry.thread, entry.layer_idx, entry.folding_steps, rounds_json, total
        )?;
        written += 1;
    }
    Ok(written)
}
