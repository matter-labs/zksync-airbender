use crate::baby_bear::precomputations::setup_host::BabyBearPrecomputations;
use crate::proth120::precomputations::L1WrapPrecomputed;
use crate::upstream::{ProofProfile, UnrolledCircuitWitnessEvalFn};
use era_cudart::result::CudaResult;
use execution_prover::config::{assert_profiles_for_circuit, SoundnessMode};
use execution_prover::setup::CanonicalCircuitSetup;
use gpu_core::primitives::static_host::{alloc_static_pinned_box_uninit, StaticPinnedBox};
use gpu_trace::witness::circuit_type::CircuitType;
use gpu_trace::witness::trace_unrolled::ExecutorFamilyDecoderData;
use std::sync::Arc;

pub(crate) fn decoder_host<D: Copy + Default + Into<ExecutorFamilyDecoderData>>(
    rows: &[Option<D>],
) -> CudaResult<Option<Arc<StaticPinnedBox<ExecutorFamilyDecoderData>>>> {
    if rows.is_empty() {
        return Ok(None);
    }
    let mut buf = alloc_static_pinned_box_uninit::<ExecutorFamilyDecoderData>(rows.len())?;
    for (slot, src) in buf.iter_mut().zip(rows.iter().copied()) {
        *slot = src.unwrap_or_default().into();
    }
    Ok(Some(Arc::new(buf)))
}

#[derive(Clone)]
pub enum CircuitPrecomputations {
    BabyBear(BabyBearPrecomputations),
    L1Wrap(Arc<L1WrapPrecomputed>),
}

impl CircuitPrecomputations {
    pub fn baby_bear(&self) -> &BabyBearPrecomputations {
        match self {
            Self::BabyBear(precomputations) => precomputations,
            Self::L1Wrap(_) => panic!("BabyBear precomputations are not defined for L1Wrap"),
        }
    }

    pub fn l1_wrap(&self) -> &Arc<L1WrapPrecomputed> {
        match self {
            Self::L1Wrap(precomputed) => precomputed,
            Self::BabyBear(_) => panic!("L1Wrap requires Proth precomputations"),
        }
    }

    pub fn from_canonical(
        circuit_type: CircuitType,
        setup: CanonicalCircuitSetup,
        soundness_mode: SoundnessMode,
        profiles: &[ProofProfile],
    ) -> Self {
        assert_profiles_for_circuit(circuit_type, profiles);
        assert_eq!(
            matches!(setup, CanonicalCircuitSetup::L1Wrap(_)),
            circuit_type == CircuitType::L1Wrap,
            "canonical setup variant disagrees with {circuit_type:?}"
        );
        let (compiled_circuit, cpu_setup, decoder_table) = match setup {
            CanonicalCircuitSetup::L1Wrap(setup) => {
                return Self::L1Wrap(Arc::new(
                    L1WrapPrecomputed::new(circuit_type, setup, soundness_mode)
                        .expect("L1 wrap precomputation allocation failed"),
                ));
            }
            CanonicalCircuitSetup::Riscv(setup) => {
                let decoder_table = setup.witness_eval_fn.map(|evaluator| match evaluator {
                    UnrolledCircuitWitnessEvalFn::NonMemory { decoder_table, .. }
                    | UnrolledCircuitWitnessEvalFn::Memory { decoder_table, .. }
                    | UnrolledCircuitWitnessEvalFn::Unified { decoder_table, .. } => decoder_table,
                });
                (setup.compiled_circuit, setup.setup, decoder_table)
            }
            CanonicalCircuitSetup::Delegation(setup) => (setup.compiled_circuit, setup.setup, None),
        };
        Self::BabyBear(BabyBearPrecomputations::from_setup(
            circuit_type,
            compiled_circuit,
            cpu_setup,
            decoder_table,
            soundness_mode,
            profiles,
        ))
    }
}
