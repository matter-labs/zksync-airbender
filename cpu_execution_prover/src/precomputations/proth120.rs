use super::{CpuCircuitPrecomputations, CpuPrecomputed};
use crate::upstream::{
    ColumnMajorBaseOracleForLDE, CosetByCosetBaseCommitment, CpuGKRSetup,
    Keccak256MerkleTreeWithCap, L1WrapSetup, Proth120, ProverConfig, SetupCommitment, Twiddles,
};
use execution_prover::config::SoundnessMode;
use execution_prover::ProofProfile;
use execution_prover_model::circuit_type::CircuitType;
use std::alloc::Global;
use std::sync::OnceLock;
use worker::Worker;

pub(crate) struct L1WrapPrecomputed {
    pub(crate) setup: L1WrapSetup,
    config: ProverConfig,
    committed: OnceLock<L1WrapCommittedSetup>,
}

pub(crate) struct L1WrapCommittedSetup {
    pub(crate) commitment: SetupCommitment<Proth120, Keccak256MerkleTreeWithCap>,
    pub(crate) twiddles: Twiddles<Proth120, Global>,
    pub(crate) config: ProverConfig,
}

impl L1WrapPrecomputed {
    pub(super) fn new(
        circuit_type: CircuitType,
        setup: L1WrapSetup,
        soundness_mode: SoundnessMode,
    ) -> Self {
        let config = ProofProfile::L1Wrap
            .prover_config(circuit_type.get_domain_size_log2() as usize, soundness_mode);
        Self::with_config(circuit_type, setup, config)
    }

    pub(crate) fn with_config(
        circuit_type: CircuitType,
        setup: L1WrapSetup,
        config: ProverConfig,
    ) -> Self {
        assert!(
            circuit_type.is_l1_wrap(),
            "an L1 wrap setup needs an L1 wrap circuit, got {circuit_type:?}"
        );
        assert!(
            setup.trace_len == circuit_type.get_domain_size() && setup.rom == circuit_type.rom(),
            "L1 wrap setup (trace {}, {:?}) disagrees with {circuit_type:?}",
            setup.trace_len,
            setup.rom
        );
        Self {
            config,
            setup,
            committed: OnceLock::new(),
        }
    }

    pub(crate) fn initialize_setup(&self, worker: &Worker) {
        self.committed.get_or_init(|| {
            L1WrapCommittedSetup::new(&self.setup.setup, self.config.clone(), worker)
        });
    }

    pub(crate) fn committed(&self) -> &L1WrapCommittedSetup {
        self.committed
            .get()
            .expect("L1Wrap setup initialization must run before proving")
    }
}

impl L1WrapCommittedSetup {
    fn new(setup: &CpuGKRSetup<Proth120>, config: ProverConfig, worker: &Worker) -> Self {
        let pack_log2 = config.pack_log2();
        let twiddles = Twiddles::new(1 << config.whir_message_size_log2(), worker);
        let inputs: Vec<&[Proth120]> = setup
            .hypercube_evals
            .iter()
            .map(|column| &column[..])
            .collect();
        let oracle =
            ColumnMajorBaseOracleForLDE::CosetRecompute(CosetByCosetBaseCommitment::commit_packed(
                &inputs,
                &twiddles,
                config.lde_factor(),
                config.base_oracles_values_per_leaf().trailing_zeros() as usize,
                config.cap_size,
                config.trace_len_log2,
                pack_log2,
                worker,
            ));
        Self {
            commitment: SetupCommitment::InMemory(oracle),
            twiddles,
            config,
        }
    }
}

impl CpuCircuitPrecomputations {
    pub(crate) fn l1_wrap(&self) -> &L1WrapPrecomputed {
        match &*self.0 {
            CpuPrecomputed::L1Wrap(precomputed) => precomputed,
            CpuPrecomputed::BabyBear(_) => panic!("L1Wrap requires Proth precomputations"),
        }
    }
}
