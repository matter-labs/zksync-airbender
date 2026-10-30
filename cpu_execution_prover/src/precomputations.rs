use crate::upstream::{
    CircuitSetup, CpuGKRSetup, DefaultTreeConstructor, GKRCircuitArtifact, MerkleTreeCapVarLength,
    ProverConfig, SetupCommitment, TableDriver, TwiddleSetOps, UnrolledCircuitWitnessEvalFn, BF,
};
use execution_prover::backend::CircuitPrecomputation;
use execution_prover::config::{ProvingSelection, SelectionError};
use execution_prover::setup::CanonicalCircuitSetup;
use execution_prover_model::circuit_type::CircuitType;
use std::alloc::Global;
use std::ops::Deref;
use std::sync::{Arc, OnceLock};
use worker::Worker;

#[derive(Clone)]
pub struct CpuCircuitPrecomputations(Arc<Precomputed>);

pub struct Precomputed {
    circuit_type: CircuitType,
    selection: ProvingSelection,
    config: ProverConfig,
    pub(crate) compiled_circuit: Arc<GKRCircuitArtifact<BF>>,
    pub(crate) setup: CpuGKRSetup<BF>,
    pub(crate) table_driver: TableDriver<BF>,
    /// `None` for delegation circuits and standalone inits-and-teardowns.
    pub(crate) witness_eval_fn: Option<UnrolledCircuitWitnessEvalFn<Global>>,
    pub(crate) trace_len: usize,
    pub(crate) setup_commitment: OnceLock<SetupCommitment<BF, DefaultTreeConstructor>>,
}

impl Deref for CpuCircuitPrecomputations {
    type Target = Precomputed;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl CpuCircuitPrecomputations {
    pub(crate) fn from_canonical(
        circuit_type: CircuitType,
        setup: CanonicalCircuitSetup,
        selection: ProvingSelection,
    ) -> Result<Self, SelectionError> {
        let compiled = match &setup {
            CanonicalCircuitSetup::Riscv(setup) => &setup.compiled_circuit,
            CanonicalCircuitSetup::Delegation(setup) => &setup.compiled_circuit,
        };
        let config = circuit_type.try_prover_config_in_mode(compiled, selection)?;
        let precomputed = match setup {
            CanonicalCircuitSetup::Riscv(CircuitSetup {
                family_idx: _,
                geometry: _,
                trace_len,
                compiled_circuit,
                table_driver,
                setup,
                witness_eval_fn,
                prover_configs: _,
            }) => Precomputed {
                circuit_type,
                selection,
                config,
                compiled_circuit: Arc::new(compiled_circuit),
                setup,
                table_driver,
                witness_eval_fn,
                trace_len,
                setup_commitment: OnceLock::new(),
            },
            CanonicalCircuitSetup::Delegation(setup) => Precomputed {
                circuit_type,
                selection,
                config,
                compiled_circuit: Arc::new(setup.compiled_circuit),
                setup: setup.setup,
                table_driver: setup.table_driver,
                witness_eval_fn: None,
                trace_len: setup.trace_len,
                setup_commitment: OnceLock::new(),
            },
        };
        assert_eq!(
            precomputed.trace_len,
            circuit_type.get_domain_size(),
            "setup trace length disagrees with CircuitType geometry for {circuit_type:?}"
        );
        Ok(Self(Arc::new(precomputed)))
    }

    pub(crate) fn config_for_request(
        &self,
        circuit_type: CircuitType,
        selection: ProvingSelection,
    ) -> Result<&ProverConfig, SelectionError> {
        if self.circuit_type != circuit_type {
            return Err(SelectionError::PreparedCircuitMismatch {
                prepared: self.circuit_type,
                requested: circuit_type,
            });
        }
        if self.selection != selection {
            return Err(SelectionError::PreparedSelectionMismatch {
                prepared: self.selection,
                requested: selection,
            });
        }
        Ok(&self.config)
    }

    pub(crate) fn initialize_setup<T: TwiddleSetOps<BF>>(
        &self,
        twiddles: &T,
        worker: &Worker,
    ) -> &SetupCommitment<BF, DefaultTreeConstructor> {
        self.setup_commitment.get_or_init(|| {
            self.setup.commit_for_config::<DefaultTreeConstructor>(
                twiddles.plain(),
                &self.config,
                worker,
            )
        })
    }
}

impl Precomputed {
    pub(crate) fn trace_len_log2(&self) -> usize {
        self.trace_len.trailing_zeros() as usize
    }
}

impl CircuitPrecomputation for CpuCircuitPrecomputations {
    fn compiled_circuit(&self) -> &Arc<GKRCircuitArtifact<BF>> {
        &self.0.compiled_circuit
    }

    fn setup_cap(&self) -> Option<MerkleTreeCapVarLength> {
        if self.setup.hypercube_evals.is_empty() {
            return None;
        }
        let commitment = self
            .setup_commitment
            .get()
            .expect("setup initialization must run before a setup cap is read");
        Some(commitment.get_cap())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use execution_prover::config::SoundnessMode;
    use execution_prover::setup::build_delegation_setup;
    use execution_prover_model::circuit_type::DelegationCircuitType;

    #[test]
    fn prepared_selection_mismatch_is_rejected() {
        let worker = Worker::new_with_num_threads(1);
        let delegation = DelegationCircuitType::Blake2GFunction;
        let circuit = CircuitType::Delegation(delegation);
        for &mode in SoundnessMode::ALL {
            let selection = ProvingSelection {
                soundness_mode: mode,
                ..ProvingSelection::default()
            };
            let prepared = CpuCircuitPrecomputations::from_canonical(
                circuit,
                build_delegation_setup(delegation, &worker),
                selection,
            )
            .unwrap();
            let config = prepared.config_for_request(circuit, selection).unwrap();
            assert_eq!(
                config,
                &circuit
                    .try_prover_config_in_mode(prepared.compiled_circuit(), selection)
                    .unwrap()
            );
            let clone = prepared.clone();
            assert!(core::ptr::eq(
                config,
                clone.config_for_request(circuit, selection).unwrap()
            ));
            assert!(prepared.setup_commitment.get().is_none());
            let other_mode = if mode == SoundnessMode::PessimisticConjecture {
                SoundnessMode::EthproofsSoundnessCalc
            } else {
                SoundnessMode::PessimisticConjecture
            };
            let requested = ProvingSelection {
                soundness_mode: other_mode,
                ..selection
            };
            assert!(matches!(
                prepared.config_for_request(circuit, requested),
                Err(SelectionError::PreparedSelectionMismatch { .. })
            ));
            assert!(matches!(
                prepared.config_for_request(
                    CircuitType::Delegation(DelegationCircuitType::BigIntWithControl),
                    selection
                ),
                Err(SelectionError::PreparedCircuitMismatch { .. })
            ));
            assert!(prepared.setup_commitment.get().is_none());
        }
    }
}
