//! BabyBear circuit setups: the binary-independent delegation and
//! inits-and-teardowns circuits, and each binary's RISC-V family circuits.

use super::*;
use crate::config::SoundnessMode;
use crate::setup::{
    build_common_setups, build_unrolled_setup_with_preprocessing, preprocess_binary,
    BinaryPreprocessing,
};
use crate::upstream::GKRCircuitArtifact;
use std::time::Duration;

/// Build and prepare the binary-independent circuits, all at
/// `ProofProfile::Standard`.
pub(in crate::prover) fn prepare_common_circuits<B: ExecutionBackend>(
    backend: &B,
    worker: &Worker,
    soundness_mode: SoundnessMode,
) -> BTreeMap<CircuitType, B::Precomputations> {
    build_common_setups(worker)
        .into_iter()
        .map(|(circuit_type, setup)| {
            (
                circuit_type,
                backend.prepare(
                    circuit_type,
                    setup,
                    soundness_mode,
                    &[ProofProfile::Standard],
                ),
            )
        })
        .collect()
}

/// Decode the binary once for each machine its BabyBear variants run on.
pub(in crate::prover) fn preprocess_machines(
    variants: &[(ExecutionKind, MachineType, Vec<ProofProfile>)],
    text_section: &[u32],
) -> Vec<(MachineType, BinaryPreprocessing, Arc<SimpleTape>)> {
    let mut machines = Vec::new();
    for &(kind, machine, _) in variants {
        if kind.is_l1_wrap() || machines.iter().any(|(m, _, _)| *m == machine) {
            continue;
        }
        let kinds: Vec<_> = variants
            .iter()
            .filter_map(|(k, m, _)| (*m == machine && !k.is_l1_wrap()).then_some(*k))
            .collect();
        let preprocessing = preprocess_binary(machine, &kinds, text_section);
        let tape = Arc::new(SimpleTape::new(&preprocessing.execution_instructions));
        machines.push((machine, preprocessing, tape));
    }
    machines
}

impl<B: ExecutionBackend> ExecutionProver<B> {
    /// Build and prepare the RISC-V family circuits of one BabyBear variant.
    /// Also returns the time spent constructing their setups and the time
    /// spent preparing them in the backend.
    pub(in crate::prover) fn prepare_riscv_families(
        &self,
        key: usize,
        execution_kind: ExecutionKind,
        machine_type: MachineType,
        padded_binary_image: &[u32],
        preprocessing: &BinaryPreprocessing,
        profiles: &[ProofProfile],
    ) -> (
        HashMap<UnrolledCircuitType, B::Precomputations>,
        (Duration, Duration),
    ) {
        let circuit_types = crate::setup::circuit_types_for_variant(
            execution_kind,
            machine_type,
            self.configuration.soundness_mode,
        );
        let mut setup_time = Duration::ZERO;
        let mut preparation_time = Duration::ZERO;
        let precomputations = circuit_types
            .into_iter()
            .map(|circuit_type| {
                debug!(
                    "PROVER producing precomputations for circuit {circuit_type:?} and binary with key {key:?}"
                );
                let start = Instant::now();
                let setup = build_unrolled_setup_with_preprocessing(
                    circuit_type,
                    padded_binary_image,
                    preprocessing,
                    &self.worker,
                );
                setup_time += start.elapsed();
                let start = Instant::now();
                let precomp = self.backend.prepare(
                    CircuitType::Unrolled(circuit_type),
                    setup,
                    self.configuration.soundness_mode,
                    profiles,
                );
                preparation_time += start.elapsed();
                (circuit_type, precomp)
            })
            .collect();
        (precomputations, (setup_time, preparation_time))
    }
}

impl<B: ExecutionBackend> BinaryHolder<B> {
    /// The compiled columns of this binary's RISC-V family `circuit`.
    pub(super) fn compiled_circuit(&self, circuit: CircuitType) -> &GKRCircuitArtifact<BF> {
        let CircuitType::Unrolled(family) = circuit else {
            panic!("{circuit:?} is not a RISC-V family of this binary")
        };
        self.precomputations[&family].compiled_circuit()
    }
}
