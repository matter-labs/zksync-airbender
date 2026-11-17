//! The compressed-calldata profile parameters shared by the encoder, the decoder and the
//! generated verifiers.

use prover::gkr::prover_config::ProverConfig;

/// Setup deployment choices. Protocol geometry comes from ProverConfig.
#[derive(Clone, Debug)]
pub struct FormatParams {
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
    pub folding_pow_bits: Vec<u32>,
    /// OOD point difficulty of the next oracle, indexed by the committing round.
    pub ood_pow_bits: Vec<u32>,
    /// Setup-tree level the verifier holds as deployment data (the setup frontier); setup paths
    /// stop there. The frontier lies strictly below the cap.
    pub setup_frontier_level: usize,
}

impl Geometry {
    pub fn from_config(config: &ProverConfig, wire: &FormatParams) -> Self {
        let FormatParams {
            setup_frontier_level,
        } = *wire;
        let ws = &config.whir_schedule;
        assert!(
            ws.internal_rounds.iter().all(|r| r.num_ood_samples == 1),
            "the compressed calldata encodes exactly one OOD sample"
        );
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
            folding_pow_bits: core::iter::once(ws.base_round.folding_pow_bits)
                .chain(ws.internal_rounds.iter().map(|r| r.folding_pow_bits))
                .collect(),
            ood_pow_bits: ws.internal_rounds.iter().map(|r| r.ood_pow_bits).collect(),
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
