//! GPU setup caps for trusted records, without a proving backend.

use crate::upstream::{BaseColumns, BaseCommitmentGeometry, ProverConfig};
use gpu_gkr::setup::GpuGKRSetupHost;
use gpu_prover_context::{ProverContext, ProverContextConfig};
use prover::field::baby_bear::base::BabyBearField;
use prover::gkr::prover::setup::GKRSetup;
use prover::merkle_trees::MerkleTreeCapVarLength;

pub struct TrustedSetupCommitter {
    context: ProverContext,
}

impl Default for TrustedSetupCommitter {
    fn default() -> Self {
        Self::new()
    }
}

impl TrustedSetupCommitter {
    pub fn new() -> Self {
        Self {
            context: ProverContext::new_with_auto_arena_size(
                &ProverContextConfig::default(),
                crate::memory_policy::select_arena_bytes,
            )
            .expect("trusted setup context"),
        }
    }

    pub fn reset_peak(&self) {
        self.context.reset_used_mem_peak();
    }
    pub fn peak(&self) -> usize {
        self.context.get_used_mem_peak()
    }

    pub fn commit(
        &self,
        config: &ProverConfig,
        setup: &GKRSetup<BabyBearField>,
    ) -> MerkleTreeCapVarLength {
        assert!(
            !setup.hypercube_evals.is_empty(),
            "trusted setup must not be empty"
        );
        let geometry = BaseCommitmentGeometry::from_config(
            config,
            BaseColumns {
                setup: setup.hypercube_evals.len(),
                memory: 0,
                witness: 0,
            },
        );
        let host = GpuGKRSetupHost::precompute_for_geometry(setup, geometry, &self.context)
            .expect("trusted GPU setup commitment");
        MerkleTreeCapVarLength {
            cap: host.unified_tree_cap().to_vec(),
        }
    }
}
