use crate::upstream::{
    BaseFieldQuery, ExtensionFieldQuery, Keccak256MerkleTreeWithCap, MerkleTreeCapVarLength,
    WhirBaseLayerCommitmentAndQueries, WhirCommitment, WhirIntermediateCommitmentAndQueries,
    WhirPolyCommitProof, WhirSchedule,
};
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::PR;
use gpu_gkr::proth120::proof_layout::{
    ProofLayoutPr, ProofSlabSlicePr, WhirBaseOpeningsFieldsPr, WhirProofTargetPr,
};
use gpu_hash::keccak256::Digest;
use std::marker::PhantomData;
use std::sync::Arc;

pub(crate) struct BaseOpeningsDevice {
    pub(crate) leaves: ProofSlabSlicePr<PR>,
    pub(crate) paths: ProofSlabSlicePr<Digest>,
    pub(crate) tree_indexes: ProofSlabSlicePr<u32>,
}

pub(crate) struct IntermediateProofDevice {
    pub(crate) cap: ProofSlabSlicePr<Digest>,
    pub(crate) leaves: ProofSlabSlicePr<PR>,
    pub(crate) paths: ProofSlabSlicePr<Digest>,
    pub(crate) tree_indexes: ProofSlabSlicePr<u32>,
}

pub(crate) struct L1WhirProofDevice {
    pub(crate) memory: BaseOpeningsDevice,
    pub(crate) setup: BaseOpeningsDevice,
    pub(crate) intermediate: Vec<IntermediateProofDevice>,
    pub(crate) memory_cap: ProofSlabSlicePr<Digest>,
    pub(crate) ood_samples: ProofSlabSlicePr<PR>,
    pub(crate) sumcheck_polys: ProofSlabSlicePr<PR>,
    pub(crate) pow_nonces: ProofSlabSlicePr<u64>,
    pub(crate) final_monomials: ProofSlabSlicePr<PR>,
    pub(crate) batched_opening: ProofSlabSlicePr<PR>,
}

impl BaseOpeningsDevice {
    fn new(
        target: &WhirProofTargetPr,
        layout: &gpu_gkr::proth120::proof_layout::WhirBaseOpeningsLayoutPr,
    ) -> Self {
        Self {
            leaves: ProofSlabSlicePr::new(Arc::clone(&target.backing), layout.leaves.clone()),
            paths: ProofSlabSlicePr::new(Arc::clone(&target.backing), layout.paths.clone()),
            tree_indexes: ProofSlabSlicePr::new(
                Arc::clone(&target.backing),
                layout.tree_indexes.clone(),
            ),
        }
    }
}
impl L1WhirProofDevice {
    pub(crate) fn new(target: &WhirProofTargetPr) -> Self {
        let layout = &target.layout.whir;
        Self {
            memory: BaseOpeningsDevice::new(target, &layout.memory),
            setup: BaseOpeningsDevice::new(target, &layout.setup),
            intermediate: layout
                .intermediate
                .iter()
                .map(|o| IntermediateProofDevice {
                    cap: ProofSlabSlicePr::new(Arc::clone(&target.backing), o.cap.clone()),
                    leaves: ProofSlabSlicePr::new(
                        Arc::clone(&target.backing),
                        o.openings.leaves.clone(),
                    ),
                    paths: ProofSlabSlicePr::new(
                        Arc::clone(&target.backing),
                        o.openings.paths.clone(),
                    ),
                    tree_indexes: ProofSlabSlicePr::new(
                        Arc::clone(&target.backing),
                        o.openings.tree_indexes.clone(),
                    ),
                })
                .collect(),
            memory_cap: ProofSlabSlicePr::new(
                Arc::clone(&target.backing),
                layout.memory_cap.clone(),
            ),
            ood_samples: ProofSlabSlicePr::new(
                Arc::clone(&target.backing),
                layout.ood_samples.clone(),
            ),
            sumcheck_polys: ProofSlabSlicePr::new(
                Arc::clone(&target.backing),
                layout.sumcheck_polys.clone(),
            ),
            pow_nonces: ProofSlabSlicePr::new(
                Arc::clone(&target.backing),
                layout.pow_nonces.clone(),
            ),
            final_monomials: ProofSlabSlicePr::new(
                Arc::clone(&target.backing),
                layout.final_monomials.clone(),
            ),
            batched_opening: ProofSlabSlicePr::new(
                Arc::clone(&target.backing),
                layout.batched_opening.clone(),
            ),
        }
    }
}

pub type L1WhirProof = WhirPolyCommitProof<PR, PR, Keccak256MerkleTreeWithCap>;

/// Enqueued WHIR work; the caller copies its proof slab and assembles in one callback.
/// All device output views retire at schedule-end, while the caller still owns the slab.
pub struct L1WhirPendingReadback {
    pub(crate) layout: Arc<ProofLayoutPr>,
    pub(crate) schedule: WhirSchedule,
    pub(crate) setup_cap: Vec<Digest>,
    pub(crate) tracing_ranges: Vec<(String, Range)>,
}
impl L1WhirPendingReadback {
    pub fn readback(&self) -> L1WhirReadback {
        L1WhirReadback::new(
            Arc::clone(&self.layout),
            self.schedule.clone(),
            self.setup_cap.clone(),
        )
    }
    pub fn into_keepalive(self) -> L1WhirKeepalive {
        L1WhirKeepalive {
            _tracing_ranges: self.tracing_ranges,
        }
    }
}

/// Phase ranges retained until completion; WHIR owns no readback mirrors.
pub struct L1WhirKeepalive {
    _tracing_ranges: Vec<(String, Range)>,
}

fn assemble_base_queries(
    host: &WhirBaseOpeningsFieldsPr<'_>,
) -> Vec<BaseFieldQuery<PR, Keccak256MerkleTreeWithCap>> {
    let indexes = host.tree_indexes;
    let leaves = host.leaves;
    let paths = host.paths;
    let leaf_width = leaves.len() / indexes.len();
    let depth = paths.len() / indexes.len();
    indexes
        .iter()
        .enumerate()
        .map(|(q, &index)| BaseFieldQuery {
            index: index as usize,
            leaf_values_concatenated: leaves[q * leaf_width..(q + 1) * leaf_width].to_vec(),
            path: paths[q * depth..(q + 1) * depth].to_vec(),
            _marker: PhantomData,
        })
        .collect()
}

pub struct L1WhirReadback {
    layout: Arc<ProofLayoutPr>,
    schedule: WhirSchedule,
    memory_columns: usize,
    setup_columns: usize,
    setup_cap: Vec<Digest>,
}

impl L1WhirReadback {
    pub fn new(layout: Arc<ProofLayoutPr>, schedule: WhirSchedule, setup_cap: Vec<Digest>) -> Self {
        let memory_columns = layout.memory_claims.len() / size_of::<PR>();
        let setup_columns = layout.setup_claims.len() / size_of::<PR>();
        Self {
            layout,
            schedule,
            memory_columns,
            setup_columns,
            setup_cap,
        }
    }

    /// Assembles the WHIR proof with the GKR claims consumed by the fold and
    /// the batching PoW nonce produced before the WHIR handoff.
    ///
    /// `bytes` is the completed, aligned proof-slab readback. The caller owns
    /// its mirror until the assembly callback has run.
    pub fn assemble(
        &self,
        bytes: &[u8],
        memory_claims: &[PR],
        setup_claims: &[PR],
        batching_challenge_pow_nonce: u64,
    ) -> L1WhirProof {
        let host = self.layout.parse_whir_fields(bytes);
        assert_eq!(
            memory_claims.len(),
            self.memory_columns,
            "Proth120 WHIR: memory claims length differs from the packed columns"
        );
        assert_eq!(
            setup_claims.len(),
            self.setup_columns,
            "Proth120 WHIR: setup claims length differs from the packed columns"
        );
        let mut intermediate_whir_oracles: Vec<_> = host
            .intermediate
            .iter()
            .map(|oracle| {
                let indexes = oracle.openings.tree_indexes;
                let leaves = oracle.openings.leaves;
                let paths = oracle.openings.paths;
                let width = leaves.len() / indexes.len();
                let depth = paths.len() / indexes.len();
                let mut result =
                    WhirIntermediateCommitmentAndQueries::with_commitment(MerkleTreeCapVarLength {
                        cap: oracle.cap.to_vec(),
                    });
                result.queries = indexes
                    .iter()
                    .enumerate()
                    .map(|(q, &index)| ExtensionFieldQuery {
                        index: index as usize,
                        leaf_values_concatenated: leaves[q * width..(q + 1) * width].to_vec(),
                        path: paths[q * depth..(q + 1) * depth].to_vec(),
                        _marker: PhantomData,
                    })
                    .collect();
                result
            })
            .collect();
        let fold_steps = self.schedule.fold_steps();
        let sumcheck_polys = host.sumcheck_polys.as_chunks::<3>().0;
        let ood_samples = host.ood_samples;
        let pow_nonces = host.pow_nonces;
        assert_eq!(fold_steps.len(), intermediate_whir_oracles.len() + 1);
        assert_eq!(ood_samples.len(), intermediate_whir_oracles.len());
        assert_eq!(pow_nonces.len(), fold_steps.len());
        assert_eq!(sumcheck_polys.len(), fold_steps.iter().sum::<usize>());
        let mut polys = sumcheck_polys.iter().copied();
        let base_sumcheck_polys = polys.by_ref().take(fold_steps[0]).collect();
        for (i, oracle) in intermediate_whir_oracles.iter_mut().enumerate() {
            oracle.ood_samples = vec![ood_samples[i]];
            oracle.sumcheck_polys = polys.by_ref().take(fold_steps[i + 1]).collect();
            oracle.queries_pow_nonce = pow_nonces[i + 1];
        }
        WhirPolyCommitProof {
            setup_commitment: WhirBaseLayerCommitmentAndQueries {
                commitment: WhirCommitment {
                    cap: MerkleTreeCapVarLength {
                        cap: self.setup_cap.clone(),
                    },
                    _marker: PhantomData,
                },
                num_columns: self.setup_columns,
                evals: setup_claims.to_vec(),
                queries: assemble_base_queries(&host.setup),
            },
            memory_commitment: WhirBaseLayerCommitmentAndQueries {
                commitment: WhirCommitment {
                    cap: MerkleTreeCapVarLength {
                        cap: host.memory_cap.to_vec(),
                    },
                    _marker: PhantomData,
                },
                num_columns: self.memory_columns,
                evals: memory_claims.to_vec(),
                queries: assemble_base_queries(&host.memory),
            },
            witness_commitment: WhirBaseLayerCommitmentAndQueries {
                commitment: Default::default(),
                num_columns: 0,
                evals: vec![],
                queries: vec![],
            },
            intermediate_whir_oracles,
            batching_challenge_pow_nonce,
            base_sumcheck_polys,
            base_folding_pow_nonces: vec![],
            base_queries_pow_nonce: pow_nonces[0],
            final_monomials: host.final_monomials.to_vec(),
            whir_schedule: self.schedule.clone(),
        }
    }
}
