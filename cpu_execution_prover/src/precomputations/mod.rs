mod baby_bear;
mod proth120;

use baby_bear::Precomputed;
use execution_prover::config::SoundnessMode;
use execution_prover::setup::CanonicalCircuitSetup;
use execution_prover::ProofProfile;
use execution_prover_model::circuit_type::CircuitType;
use proth120::L1WrapPrecomputed;
use std::sync::Arc;

#[derive(Clone)]
pub struct CpuCircuitPrecomputations(Arc<CpuPrecomputed>);

enum CpuPrecomputed {
    BabyBear(Box<Precomputed>),
    L1Wrap(Box<L1WrapPrecomputed>),
}

impl CpuCircuitPrecomputations {
    pub(crate) fn from_canonical(
        circuit_type: CircuitType,
        setup: CanonicalCircuitSetup,
        soundness_mode: SoundnessMode,
        profiles: &[ProofProfile],
    ) -> Self {
        let precomputed = match setup {
            CanonicalCircuitSetup::L1Wrap(setup) => CpuPrecomputed::L1Wrap(Box::new(
                L1WrapPrecomputed::new(circuit_type, setup, soundness_mode),
            )),
            setup => CpuPrecomputed::BabyBear(Box::new(Precomputed::new(
                circuit_type,
                setup,
                soundness_mode,
                profiles,
            ))),
        };
        Self(Arc::new(precomputed))
    }
}
