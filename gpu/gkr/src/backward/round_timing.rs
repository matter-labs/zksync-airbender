//! Opt-in CUDA-event recorder for backward sumcheck rounds. Inert unless
//! `GKR_BWD_FIRST3_TIMING_OUT` is set.
//!
//! Event records are enqueue-only on the exec stream (contract-safe).
//! `dump_first3_timing` must run only after the enclosing proof has
//! synchronized; it synchronizes each terminal event before reading.
//!
//! Per layer: a start event, one event per recorded segment (the first three
//! round tails, plus the windowed arm's named prologue segments), and one
//! event after the final round's tail. This yields the per-segment times and
//! the layer's total backward time, tagged with the arm that ran.

use std::io::Write;
use std::sync::{Mutex, OnceLock};

use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;

pub struct RoundTimingEntry {
    pub kind: &'static str,
    pub arm: &'static str,
    pub thread: String,
    pub layer_idx: usize,
    pub folding_steps: usize,
    pub start: CudaEvent,
    pub marks: Vec<(String, CudaEvent)>,
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
        arm: &'static str,
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
                arm,
                thread: format!("{:?}", std::thread::current().id()),
                layer_idx,
                folding_steps,
                start,
                marks: Vec::new(),
            },
            round_marks: 0,
        }))
    }

    /// Records a named segment boundary; call right after the segment's last
    /// launch is scheduled. Uncapped — used for the windowed prologue.
    pub fn mark(&mut self, label: impl Into<String>, stream: &CudaStream) -> CudaResult<()> {
        let event = CudaEvent::create()?;
        event.record(stream)?;
        self.entry.marks.push((label.into(), event));
        Ok(())
    }

    /// Records a round-boundary event; call right after the fused tail of each
    /// round. Only the first three marked rounds are recorded.
    pub fn mark_round_end(&mut self, step: usize, stream: &CudaStream) -> CudaResult<()> {
        if self.round_marks >= 3 {
            return Ok(());
        }
        self.round_marks += 1;
        self.mark(format!("round{step}"), stream)
    }

    /// Records the layer-end event; call right after the final round's tail.
    pub fn finish(mut self, stream: &CudaStream) -> CudaResult<()> {
        let event = CudaEvent::create()?;
        event.record(stream)?;
        self.entry.marks.push(("layer".to_string(), event));
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
        let (_, last) = entry
            .marks
            .last()
            .ok_or("round timing entry has no segments")?;
        last.synchronize()?;
        let mut segments = Vec::with_capacity(entry.marks.len());
        let mut previous = &entry.start;
        for (label, event) in &entry.marks {
            segments.push((label.as_str(), elapsed_time(previous, event)?));
            previous = event;
        }
        let total = elapsed_time(&entry.start, last)?;
        if !(total.is_finite() && segments.iter().all(|(_, v)| v.is_finite())) {
            return Err(format!(
                "non-finite round timing data at sequence {sequence} layer {}",
                entry.layer_idx
            )
            .into());
        }
        let segments_json = segments
            .iter()
            .map(|(label, ms)| format!("{{\"label\":{label:?},\"ms\":{ms}}}"))
            .collect::<Vec<_>>()
            .join(",");
        writeln!(
            file,
            "{{\"sequence\":{},\"kind\":{:?},\"arm\":{:?},\"thread\":{:?},\"layer_idx\":{},\"folding_steps\":{},\"segments\":[{}],\"total_ms\":{}}}",
            sequence,
            entry.kind,
            entry.arm,
            entry.thread,
            entry.layer_idx,
            entry.folding_steps,
            segments_json,
            total
        )?;
        written += 1;
    }
    Ok(written)
}
