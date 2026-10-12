use std::sync::{Arc, OnceLock};

use era_cudart::result::CudaResult;
use gpu_gkr::setup::L1WrapSetupHost;
use gpu_prover_context::ProverContext;
use gpu_trace::trace::packed::PackedCommitConfig;

use crate::upstream::{
    L1WrapSetup, MerkleTreeCapVarLength, ProofProfile, SecurityLevel, EVM_PRODUCTION_PACK_LOG2,
};

pub struct L1WrapPrecomputed {
    pub setup: L1WrapSetup,
    host: OnceLock<Arc<L1WrapSetupHost>>,
}

impl L1WrapPrecomputed {
    pub fn new(setup: L1WrapSetup) -> Self {
        Self {
            setup,
            host: OnceLock::new(),
        }
    }

    pub fn initialize(&self, security: SecurityLevel, context: &ProverContext) -> CudaResult<()> {
        self.host
            .get_or_try_init(|| {
                let config = ProofProfile::L1Wrap.prover_config(22, security);
                let log_packed = config
                    .trace_len_log2
                    .checked_add(EVM_PRODUCTION_PACK_LOG2)
                    .expect("L1WrapPrecomputed: packed domain log overflow");
                let cfg = PackedCommitConfig::from_prover_config(
                    &config,
                    u32::try_from(log_packed)
                        .expect("L1WrapPrecomputed: packed domain log exceeds u32"),
                );
                let pack_log2 = u32::try_from(EVM_PRODUCTION_PACK_LOG2)
                    .expect("L1WrapPrecomputed: pack_log2 exceeds u32");
                L1WrapSetupHost::precompute(&self.setup.setup, pack_log2, cfg, context)
                    .map(Arc::new)
            })
            .map(|_| ())
    }

    pub fn host(&self) -> Arc<L1WrapSetupHost> {
        Arc::clone(
            self.host
                .get()
                .expect("L1Wrap setup initialization must run before proving"),
        )
    }

    pub fn setup_cap(&self) -> MerkleTreeCapVarLength {
        self.host().cap()
    }
}

#[cfg(test)]
mod cpu_tests {
    use super::*;

    #[test]
    #[should_panic(expected = "L1Wrap setup initialization must run before proving")]
    fn host_before_initialize_panics() {
        let circuit = serde_json::from_str(include_str!(
            "../../../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json"
        ))
        .expect("committed Proth120 layout");
        let setup = L1WrapSetup {
            circuit,
            table_driver: cs::tables::TableDriver::new(),
            decoder_table: Vec::new(),
            setup: prover::gkr::prover::setup::GKRSetup {
                hypercube_evals: Vec::new(),
            },
            trace_len: 1 << 22,
        };
        L1WrapPrecomputed::new(setup).host();
    }
}
