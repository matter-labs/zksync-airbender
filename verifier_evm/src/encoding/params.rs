//! The F1 profile parameters shared by the encoder, the decoder and the generated verifiers.

use prover::gkr::prover_config::ProverConfig;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FormatParams {
    pub trace_log2: usize,
    pub explicit_output_log2: usize,
    pub pack_log2: usize,
    pub cap_log2: usize,
    pub folds: Vec<usize>,
    pub queries: Vec<usize>,
    /// Wire bytes per Merkle digest: 25 (truncated commitment) or 32 (legacy).
    pub digest_bytes: usize,
    /// Setup-tree level the verifier holds as deployment data (the setup frontier); setup paths
    /// stop there. `cap_log2` = no frontier, full paths to the cap.
    pub setup_frontier_level: usize,
}

impl FormatParams {
    pub fn from_config(config: &ProverConfig, pack_log2: usize, digest_bytes: usize) -> Self {
        assert!(
            matches!(digest_bytes, 25 | 32),
            "digest_bytes must be 25 or 32"
        );
        let ws = &config.whir_schedule;
        assert!(
            ws.cap_size.is_power_of_two(),
            "cap size must be a power of two"
        );
        assert_eq!(
            ws.whir_steps_schedule.len(),
            ws.whir_queries_schedule.len(),
            "WHIR folds/queries schedule length mismatch"
        );
        Self {
            trace_log2: config.trace_len_log2,
            explicit_output_log2: config.sumcheck_explicit_output_size_log_2,
            pack_log2,
            cap_log2: ws.cap_size.trailing_zeros() as usize,
            folds: ws.whir_steps_schedule.clone(),
            queries: ws.whir_queries_schedule.clone(),
            digest_bytes,
            setup_frontier_level: ws.cap_size.trailing_zeros() as usize,
        }
    }

    /// The profile with the setup frontier at `level` (at or below the cap level).
    pub fn with_setup_frontier(mut self, level: usize) -> Self {
        assert!(
            level >= self.cap_log2,
            "the setup frontier lies at or below the cap"
        );
        self.setup_frontier_level = level;
        self
    }

    /// Setup-path siblings the frontier replaces.
    pub fn setup_frontier_skip(&self) -> usize {
        self.setup_frontier_level - self.cap_log2
    }

    pub fn cap(&self) -> usize {
        1 << self.cap_log2
    }
}
