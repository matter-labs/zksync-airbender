//! Opt-in CUDA-event recorder for the first three backward main-layer
//! sumcheck rounds. Inert unless `GKR_BWD_FIRST3_TIMING_OUT` is set.
//!
//! Event records are enqueue-only on the exec stream (contract-safe).
//! `dump_first3_timing` must run only after the enclosing proof has
//! synchronized; it synchronizes each terminal event before reading.

use std::io::Write;
use std::sync::{Mutex, OnceLock};

use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;

pub struct First3Entry {
    pub thread: String,
    pub layer_idx: usize,
    pub folding_steps: usize,
    pub events: [CudaEvent; 4],
}

// SAFETY: CUDA event handles are process-global and valid on any host thread.
unsafe impl Send for First3Entry {}

static OUT_PATH: OnceLock<Option<String>> = OnceLock::new();
static SINK: Mutex<Vec<First3Entry>> = Mutex::new(Vec::new());

pub fn first3_timing_out() -> Option<&'static str> {
    OUT_PATH
        .get_or_init(|| std::env::var("GKR_BWD_FIRST3_TIMING_OUT").ok())
        .as_deref()
}

pub struct First3Recorder {
    thread: String,
    layer_idx: usize,
    folding_steps: usize,
    events: Vec<CudaEvent>,
}

impl First3Recorder {
    /// Records the interval-start event immediately; call right before the
    /// round-0 VM is scheduled. Returns `None` when the recorder is disabled.
    pub fn begin(
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
            thread: format!("{:?}", std::thread::current().id()),
            layer_idx,
            folding_steps,
            events: vec![start],
        }))
    }

    /// Records the round-boundary event; call right after the fused tail of
    /// rounds 0, 1, and 2 is scheduled.
    pub fn mark_round_end(&mut self, stream: &CudaStream) -> CudaResult<()> {
        if self.events.len() >= 4 {
            return Ok(());
        }
        let event = CudaEvent::create()?;
        event.record(stream)?;
        self.events.push(event);
        Ok(())
    }

    pub fn finish(self) {
        let events: [CudaEvent; 4] = match self.events.try_into() {
            Ok(events) => events,
            Err(_) => return,
        };
        SINK.lock().unwrap().push(First3Entry {
            thread: self.thread,
            layer_idx: self.layer_idx,
            folding_steps: self.folding_steps,
            events,
        });
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
        entry.events[3].synchronize()?;
        let r0 = elapsed_time(&entry.events[0], &entry.events[1])?;
        let r1 = elapsed_time(&entry.events[1], &entry.events[2])?;
        let r2 = elapsed_time(&entry.events[2], &entry.events[3])?;
        let total = elapsed_time(&entry.events[0], &entry.events[3])?;
        if !(r0.is_finite() && r1.is_finite() && r2.is_finite() && total.is_finite()) {
            return Err(format!(
                "non-finite first3 event data at sequence {sequence} layer {}",
                entry.layer_idx
            )
            .into());
        }
        writeln!(
            file,
            "{{\"sequence\":{},\"thread\":{:?},\"layer_idx\":{},\"folding_steps\":{},\"r0_ms\":{},\"r1_ms\":{},\"r2_ms\":{},\"total_ms\":{}}}",
            sequence, entry.thread, entry.layer_idx, entry.folding_steps, r0, r1, r2, total
        )?;
        written += 1;
    }
    Ok(written)
}
