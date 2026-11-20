//! The compressed-calldata profile parameters shared by the encoder, the decoder and the
//! generated verifiers.

use prover::gkr::prover_config::ProverConfig;

/// Setup deployment choices. Protocol geometry comes from ProverConfig.
#[derive(Clone, Debug)]
pub struct FormatParams {
    pub setup_frontier_level: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct OracleGeometry {
    pub domain_log2: usize,
    pub lde_log2: usize,
    pub query_index_bits: usize,
}

pub(crate) fn oracle_geometry(config: &ProverConfig) -> Vec<OracleGeometry> {
    let schedule = &config.whir_schedule;
    let mut message_log2 = config.whir_message_size_log2();
    let rates = core::iter::once(schedule.base_lde_factor_log2()).chain(
        schedule
            .internal_rounds
            .iter()
            .map(|round| round.lde_factor_log2),
    );
    schedule
        .fold_steps()
        .into_iter()
        .zip(rates)
        .map(|(fold, lde_log2)| {
            let domain_log2 = message_log2 + lde_log2;
            message_log2 = message_log2
                .checked_sub(fold)
                .expect("WHIR fold exceeds message size");
            let query_index_bits = message_log2 + lde_log2;
            OracleGeometry {
                domain_log2,
                lde_log2,
                query_index_bits,
            }
        })
        .collect()
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Geometry {
    pub trace_log2: usize,
    pub explicit_output_log2: usize,
    pub pack_log2: usize,
    pub cap_log2: usize,
    pub oracles: Vec<OracleGeometry>,
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
        let cap_log2 = ws.cap_size.trailing_zeros() as usize;
        assert!(
            setup_frontier_level > cap_log2,
            "the setup frontier must be below the cap"
        );
        let oracles = oracle_geometry(config);
        assert!(
            oracles
                .iter()
                .all(|oracle| (cap_log2..=u32::BITS as usize).contains(&oracle.query_index_bits)),
            "WHIR query index bits must accommodate the cap and fit in 32 bits"
        );
        assert!(
            setup_frontier_level <= oracles[0].query_index_bits,
            "profile setup frontier lies below the setup leaves"
        );
        Self {
            oracles,
            trace_log2: config.trace_len_log2,
            explicit_output_log2: config.sumcheck_explicit_output_size_log_2,
            pack_log2: config.pack_log2(),
            cap_log2,
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
