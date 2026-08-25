//! Opt-in CUDA-event recorder for backward sumcheck rounds. The production
//! worker configures it once from the complete exact-memory identity; it is
//! otherwise inert and never reads the environment itself.
//!
//! Event records are enqueue-only on the exec stream (contract-safe).
//! `dump_first3_timing` must run only after the enclosing proof has
//! synchronized; it synchronizes each terminal event before reading.
//!
//! Per layer: a start event, one event per recorded segment (the first three
//! round tails, plus the windowed arm's named prologue and continuation-window
//! kernel/tail segments), and one
//! event after the final round's tail. This yields the per-segment times and
//! the layer's total backward time, tagged with the arm that ran.

use std::io::Write;
use std::path::Path;
use std::sync::{Mutex, OnceLock};

use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;

pub struct RoundTimingEntry {
    pub proof: RoundTimingProofIdentity,
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
static ACTIVE_PROOF: Mutex<Option<RoundTimingProofIdentity>> = Mutex::new(None);

/// Immutable source identity shared by the per-proof memory row and every
/// timing row scheduled while that proof is active.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoundTimingProofIdentity {
    pub batch_id: u64,
    pub circuit_type: String,
    pub sequence_id: usize,
    pub device_id: i32,
}

impl RoundTimingProofIdentity {
    pub fn key(&self) -> String {
        format!(
            "batch:{}:circuit:{}:sequence:{}:device:{}",
            self.batch_id, self.circuit_type, self.sequence_id, self.device_id
        )
    }

    pub fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "key": self.key(),
            "batch_id": self.batch_id,
            "circuit_type": self.circuit_type,
            "sequence_id": self.sequence_id,
            "device_id": self.device_id,
        })
    }
}

/// Configure the recorder once from the worker's already-resolved immutable
/// measurement configuration. The recorder never rereads the environment.
pub fn configure_first3_timing(path: Option<&Path>) -> Result<(), String> {
    let path = path.map(|path| path.to_string_lossy().into_owned());
    if OUT_PATH.set(path.clone()).is_ok() || OUT_PATH.get() == Some(&path) {
        Ok(())
    } else {
        Err(format!(
            "round timing output was already configured as {:?}, cannot change it to {path:?}",
            OUT_PATH.get()
        ))
    }
}

/// Keeps one measured proof's source identity active while its GPU work is
/// scheduled. Measurement topology is serialized, so overlap is a defect.
pub struct RoundTimingProofScope {
    identity: Option<RoundTimingProofIdentity>,
}

pub fn begin_proof(identity: RoundTimingProofIdentity) -> Result<RoundTimingProofScope, String> {
    if first3_timing_out().is_none() {
        return Ok(RoundTimingProofScope { identity: None });
    }
    let mut active = ACTIVE_PROOF.lock().unwrap();
    if let Some(existing) = active.as_ref() {
        return Err(format!(
            "round timing proof identity overlaps: active={} requested={}",
            existing.key(),
            identity.key()
        ));
    }
    *active = Some(identity.clone());
    Ok(RoundTimingProofScope {
        identity: Some(identity),
    })
}

impl Drop for RoundTimingProofScope {
    fn drop(&mut self) {
        let Some(expected) = self.identity.take() else {
            return;
        };
        let mut active = ACTIVE_PROOF.lock().unwrap();
        debug_assert_eq!(active.as_ref(), Some(&expected));
        *active = None;
    }
}

pub fn first3_timing_out() -> Option<&'static str> {
    OUT_PATH.get().and_then(Option::as_deref)
}

/// Exact segment sequence expected from one real dimension-reducing layer.
/// The complete arm's continuation count comes from its admitted entry round;
/// the legacy arm records at most the first three non-final rounds.
pub fn expected_dim_reducing_segments(
    folding_steps: usize,
    entry_round: Option<usize>,
) -> Vec<String> {
    let mut labels = Vec::new();
    if let Some(entry_round) = entry_round {
        assert!(entry_round >= 3 && entry_round % 3 == 0);
        labels.push("window_r0".to_owned());
        for index in 0..((entry_round - 3) / 3) {
            labels.push(format!("window_continuation_{index}"));
        }
        labels.push("megakernel".to_owned());
    } else {
        for step in 0..folding_steps.saturating_sub(1).min(3) {
            labels.push(format!("round{step}"));
        }
    }
    labels.push("layer".to_owned());
    labels
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
        let proof = ACTIVE_PROOF
            .lock()
            .unwrap()
            .clone()
            .expect("enabled round timing requires an active measured proof identity");
        let start = CudaEvent::create()?;
        start.record(stream)?;
        Ok(Some(Self {
            entry: RoundTimingEntry {
                proof,
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
        let row = serde_json::json!({
            "sequence": sequence,
            "proof": entry.proof.to_json(),
            "kind": entry.kind,
            "arm": entry.arm,
            "thread": entry.thread,
            "layer_idx": entry.layer_idx,
            "folding_steps": entry.folding_steps,
            "segments": segments
                .iter()
                .map(|(label, ms)| serde_json::json!({"label": label, "ms": ms}))
                .collect::<Vec<_>>(),
            "total_ms": total,
        });
        serde_json::to_writer(&mut file, &row)?;
        writeln!(file)?;
        written += 1;
    }
    Ok(written)
}

#[cfg(test)]
mod tests {
    use super::{expected_dim_reducing_segments, RoundTimingProofIdentity};

    #[test]
    fn cpu_round_timing_identity_and_exact_dr_paths_are_stable() {
        let identity = RoundTimingProofIdentity {
            batch_id: 17,
            circuit_type: "MainVM".to_owned(),
            sequence_id: 23,
            device_id: 0,
        };
        assert_eq!(
            identity.key(),
            "batch:17:circuit:MainVM:sequence:23:device:0"
        );
        assert_eq!(identity.to_json()["key"], identity.key());

        assert_eq!(
            expected_dim_reducing_segments(24, Some(3)),
            ["window_r0", "megakernel", "layer"]
        );
        assert_eq!(
            expected_dim_reducing_segments(24, Some(9)),
            [
                "window_r0",
                "window_continuation_0",
                "window_continuation_1",
                "megakernel",
                "layer",
            ]
        );
        assert_eq!(
            expected_dim_reducing_segments(24, None),
            ["round0", "round1", "round2", "layer"]
        );
        assert_eq!(expected_dim_reducing_segments(2, None), ["round0", "layer"]);
    }
}
