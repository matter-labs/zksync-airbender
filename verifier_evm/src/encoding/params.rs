//! The F1 profile parameters shared by the encoder, the decoder and the generated verifiers.

use prover::gkr::prover_config::ProverConfig;

/// Independent wire/deployment choices. Protocol geometry comes from ProverConfig.
#[derive(Clone, Debug)]
pub struct FormatParams {
    pub digest_bytes: usize,
    pub setup_frontier_level: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Geometry {
    pub trace_log2: usize,
    pub explicit_output_log2: usize,
    pub pack_log2: usize,
    pub cap_log2: usize,
    pub folds: Vec<usize>,
    pub queries: Vec<usize>,
    /// Wire bytes per Merkle digest: 25 (the truncated L1 commitment).
    pub digest_bytes: usize,
    /// Setup-tree level the verifier holds as deployment data (the setup frontier); setup paths
    /// stop there. The frontier lies strictly below the cap.
    pub setup_frontier_level: usize,
}

impl Geometry {
    pub fn from_config(config: &ProverConfig, wire: &FormatParams) -> Self {
        let FormatParams {
            digest_bytes,
            setup_frontier_level,
        } = *wire;
        assert!(
            digest_bytes == 25,
            "the L1 wrap commitment uses 25-byte digests"
        );
        let ws = &config.whir_schedule;
        assert!(
            ws.cap_size.is_power_of_two(),
            "cap size must be a power of two"
        );
        assert_eq!(
            ws.fold_steps().len(),
            ws.queries_per_round().len(),
            "WHIR folds/queries schedule length mismatch"
        );
        assert!(
            setup_frontier_level > ws.cap_size.trailing_zeros() as usize,
            "the setup frontier must be below the cap"
        );
        Self {
            trace_log2: config.trace_len_log2,
            explicit_output_log2: config.sumcheck_explicit_output_size_log_2,
            pack_log2: config.pack_log2(),
            cap_log2: ws.cap_size.trailing_zeros() as usize,
            folds: ws.fold_steps().clone(),
            queries: ws.queries_per_round().clone(),
            digest_bytes,
            setup_frontier_level,
        }
    }

    /// Setup-path siblings the frontier replaces.
    pub fn setup_frontier_skip(&self) -> usize {
        self.setup_frontier_level - self.cap_log2
    }

    pub fn cap(&self) -> usize {
        1 << self.cap_log2
    }
}
