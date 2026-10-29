use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_prover_context::ProverContext;

use super::desc::{ARG_DERIVED_E4_CAP, CONST_DERIVED_E4_CAP};
use crate::proth120::backward::scheduled_execution::{note_device, ResourceEventPr};
use crate::proth120::packed_challenges::PackedChallenges;
use crate::upstream::{
    ChallengeKey, ChallengePower, ChallengeRef, GKRCircuitArtifact, PermutationSlot, TableType, PR,
};

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub(crate) struct ChallengePowerSlot {
    pub source: u32,
    pub power: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct ForwardChallengeDesc {
    pub slots: [ChallengePowerSlot; ARG_DERIVED_E4_CAP],
    pub arg_count: u32,
    pub lookup_slot: u32,
    pub decoder_slot: u32,
    pub table_width: u32,
    pub decoder_table_id: u32,
}

const _: () = {
    assert!(size_of::<ChallengePowerSlot>() == 8);
    assert!(size_of::<ForwardChallengeDesc>() == 116);
    assert!(align_of::<ForwardChallengeDesc>() == 4);
};

pub struct ForwardChallengePlan {
    pub(crate) desc: ForwardChallengeDesc,
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) arg_refs: Vec<ChallengeRef>,
    pub(crate) lookup_additive_slot: Option<usize>,
    pub(crate) decoder_fill_slot: Option<usize>,
}

fn challenge_source(key: ChallengeKey) -> u32 {
    match key {
        ChallengeKey::PermutationAdditive => 6,
        ChallengeKey::PermutationLinearization(slot) => match slot {
            PermutationSlot::AddressLow => 0,
            PermutationSlot::AddressHigh => 1,
            PermutationSlot::TimestampLow => 2,
            PermutationSlot::TimestampHigh => 3,
            PermutationSlot::ValueLow => 4,
            PermutationSlot::ValueHigh => 5,
        },
        ChallengeKey::LookupAdditive => 8,
        ChallengeKey::LookupMultiplicative => 7,
        ChallengeKey::ClaimBatching => panic!("Proth120 forward cannot use ClaimBatching"),
    }
}

impl ForwardChallengePlan {
    pub(crate) fn new(
        dag: &gkr_eval_ir::DagCircuit,
        forward: &gpu_gkr_compiler::ForwardProgramBundle,
        circuit: &GKRCircuitArtifact<PR>,
    ) -> Self {
        let arg_refs: Vec<_> = forward
            .layers
            .iter()
            .flat_map(|layer| layer.derived_e4.arg_refs().iter().copied())
            .collect();
        assert!(
            arg_refs.len() <= ARG_DERIVED_E4_CAP,
            "Proth120 forward argument bank overflow"
        );
        let lookup_additive_slot = forward
            .layers
            .iter()
            .any(|layer| layer.derived_e4.uses_lookup_additive())
            .then_some(0);
        let decoder_fill_slot = forward
            .layers
            .iter()
            .any(|layer| {
                layer.specials.iter().any(|s| {
                    matches!(
                        s,
                        gpu_gkr_compiler::ForwardSpecialStrategy::PeekDecoder { .. }
                    )
                })
            })
            .then_some(usize::from(lookup_additive_slot.is_some()));
        let mut slots = [ChallengePowerSlot::default(); ARG_DERIVED_E4_CAP];
        for (slot, reference) in slots.iter_mut().zip(&arg_refs) {
            assert!(dag.layers.iter().any(|layer| layer.sources.iter().any(|source| matches!(source, gkr_eval_ir::SourceKind::Challenge { reference: r } if r == reference))), "Proth120 forward challenge is absent from the DAG");
            *slot = ChallengePowerSlot {
                source: challenge_source(reference.key),
                power: match reference.power {
                    ChallengePower::One => 1,
                    ChallengePower::Static(p) => p,
                },
            };
        }
        assert!(
            circuit.generic_lookup_tables_width <= 11,
            "Proth120 setup lookup width exceeds 11"
        );
        let desc = ForwardChallengeDesc {
            slots,
            arg_count: arg_refs.len() as u32,
            lookup_slot: lookup_additive_slot.map_or(u32::MAX, |s| s as u32),
            decoder_slot: decoder_fill_slot.map_or(u32::MAX, |s| s as u32),
            table_width: circuit.generic_lookup_tables_width as u32,
            decoder_table_id: if circuit.tables_ids_in_generic_lookups {
                TableType::Decoder as u32
            } else {
                0
            },
        };
        Self {
            desc,
            arg_refs,
            lookup_additive_slot,
            decoder_fill_slot,
        }
    }
}

pub struct ForwardChallengeBanks {
    pub arg_derived: DeviceAllocation<PR>,
    pub const_derived: DeviceAllocation<PR>,
    pub lookup_alpha_powers: DeviceAllocation<PR>,
}

impl ForwardChallengeBanks {
    pub(crate) fn note_resources(
        &self,
        context: &ProverContext,
        stage: &'static str,
        event: ResourceEventPr,
    ) {
        for (owner, bank) in [
            ("forward.banks.arg_derived", &self.arg_derived),
            ("forward.banks.const_derived", &self.const_derived),
            (
                "forward.banks.lookup_alpha_powers",
                &self.lookup_alpha_powers,
            ),
        ] {
            note_device(context, stage, None, event, owner, bank);
        }
    }
}

cuda_kernel_signature_arguments_and_function!(
    pub(crate) ForwardChallengeBanksKernel,
    challenges: *const PR,
    arg_derived: *mut PR,
    const_derived: *mut PR,
    lookup_alpha_powers: *mut PR,
    plan: ForwardChallengeDesc,
);
cuda_kernel_declaration!(pub(crate) ab_pr_gkr_forward_challenge_banks_kernel(
    challenges: *const PR, arg_derived: *mut PR, const_derived: *mut PR,
    lookup_alpha_powers: *mut PR, plan: ForwardChallengeDesc
));

pub fn schedule_forward_challenge_banks(
    challenges: &PackedChallenges,
    plan: &ForwardChallengePlan,
    context: &ProverContext,
) -> CudaResult<ForwardChallengeBanks> {
    schedule_from_device_challenges(challenges.challenges(), plan, context)
}

pub(crate) fn schedule_from_device_challenges(
    challenges: &era_cudart::slice::DeviceSlice<PR>,
    plan: &ForwardChallengePlan,
    context: &ProverContext,
) -> CudaResult<ForwardChallengeBanks> {
    assert_eq!(
        challenges.len(),
        9,
        "Proth120 forward challenges must contain nine fields"
    );
    let mut banks = ForwardChallengeBanks {
        arg_derived: context.alloc(ARG_DERIVED_E4_CAP, AllocationPlacement::BestFit)?,
        const_derived: context.alloc(CONST_DERIVED_E4_CAP, AllocationPlacement::BestFit)?,
        lookup_alpha_powers: context.alloc(11, AllocationPlacement::BestFit)?,
    };
    banks.note_resources(context, "forward", ResourceEventPr::Allocated);
    let args = ForwardChallengeBanksKernelArguments::new(
        challenges.as_ptr(),
        banks.arg_derived.as_mut_ptr(),
        banks.const_derived.as_mut_ptr(),
        banks.lookup_alpha_powers.as_mut_ptr(),
        plan.desc,
    );
    let config = CudaLaunchConfig::basic(1, 128, context.get_exec_stream());
    ForwardChallengeBanksKernelFunction(ab_pr_gkr_forward_challenge_banks_kernel)
        .launch(&config, &args)?;
    Ok(banks)
}
