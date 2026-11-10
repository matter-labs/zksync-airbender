use std::collections::{BTreeMap, BTreeSet};

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_prover_context::ProverContext;

use crate::proth120::programs::GkrProgramsPr;
use crate::proth120::proof_layout::ProofLayoutPr;
use crate::transform::logical_protocol_address;
use crate::upstream::{GKRAddress, PR};

const BASE_CLAIM_COUNT: usize = 106;

#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct DenseClaimIndicesPr {
    indices: [u32; BASE_CLAIM_COUNT],
}

cuda_kernel_signature_arguments_and_function!(pub(crate) PrGatherBaseClaims, claims: *const PR, indices: DenseClaimIndicesPr, out: *mut PR, count: u32);
cuda_kernel_declaration!(pub(crate) ab_pr_gkr_gather_base_claims_kernel(claims: *const PR, indices: DenseClaimIndicesPr, out: *mut PR, count: u32));

#[repr(C)]
struct GatherArgumentsLayout {
    claims: *const PR,
    indices: DenseClaimIndicesPr,
    out: *mut PR,
    count: u32,
}
#[allow(dead_code)]
pub(crate) const PR_GATHER_ARGUMENT_BYTES: usize = size_of::<GatherArgumentsLayout>();
const _: () = {
    assert!(size_of::<DenseClaimIndicesPr>() == 424);
    assert!(size_of::<GatherArgumentsLayout>() == 448);
    assert!(size_of::<GatherArgumentsLayout>() <= 32764);
    assert!(std::mem::offset_of!(GatherArgumentsLayout, count) == 440);
};

pub(crate) struct GatheredBaseClaimsPr {
    pub(crate) values: DeviceAllocation<PR>,
    pub(crate) memory_witness_count: usize,
    pub(crate) setup_count: usize,
}

pub(crate) fn dense_claim_indices(
    claim_addresses: &[GKRAddress],
    memory_columns: usize,
    witness_columns: usize,
    setup_columns: usize,
) -> Vec<u32> {
    let mut indices = BTreeMap::new();
    for (index, address) in claim_addresses.iter().copied().enumerate() {
        assert!(
            indices
                .insert(
                    address,
                    u32::try_from(index).expect("Proth120 claim map exceeds u32")
                )
                .is_none(),
            "Proth120 claim map has duplicate addresses"
        );
    }
    let addresses = (0..memory_columns)
        .map(GKRAddress::BaseLayerMemory)
        .chain((0..witness_columns).map(GKRAddress::BaseLayerWitness))
        .chain((0..setup_columns).map(GKRAddress::Setup));
    addresses
        .map(|address| {
            *indices
                .get(&address)
                .unwrap_or_else(|| panic!("Proth120 base claim is missing: {address:?}"))
        })
        .collect()
}

/// The claim addresses the last backward layer (layer 0) hands to the base
/// claims: its folding sources in address order, then its extra evaluations.
pub(crate) fn final_claim_addresses_pr(
    programs: &GkrProgramsPr,
    layout: &ProofLayoutPr,
) -> Vec<GKRAddress> {
    let mapping = &programs.runtime_circuit.scratch_space_mapping_rev;
    let sources: BTreeSet<GKRAddress> = programs.backward_layers[0]
        .inputs
        .iter()
        .copied()
        .filter(|address| *address != GKRAddress::placeholder())
        .map(|address| logical_protocol_address(address, mapping))
        .collect();
    let extras = &layout
        .backward_layers
        .iter()
        .find(|layer| layer.layer_idx == 0)
        .expect("Proth120 layer-0 layout is missing")
        .extra_evaluations_addresses;
    sources.into_iter().chain(extras.iter().copied()).collect()
}

/// Construction-built gather layout for the unified Proth120 circuit.
#[derive(Clone, Copy)]
pub struct BaseClaimGatherPr {
    indices: DenseClaimIndicesPr,
    claim_count: usize,
    pub(crate) memory_witness_count: usize,
    setup_count: usize,
}

impl BaseClaimGatherPr {
    pub fn new(
        programs: &GkrProgramsPr,
        layout: &ProofLayoutPr,
        memory_columns: usize,
        witness_columns: usize,
        setup_columns: usize,
    ) -> Self {
        assert_eq!(
            (memory_columns, witness_columns, setup_columns),
            (38, 58, 10),
            "Proth120 unified gather requires 38 memory, 58 witness and 10 setup columns ({BASE_CLAIM_COUNT} total)"
        );
        let addresses = final_claim_addresses_pr(programs, layout);
        let indices =
            dense_claim_indices(&addresses, memory_columns, witness_columns, setup_columns);
        Self {
            indices: DenseClaimIndicesPr {
                indices: indices
                    .try_into()
                    .expect("Proth120 unified base claim count"),
            },
            claim_count: addresses.len(),
            memory_witness_count: memory_columns + witness_columns,
            setup_count: setup_columns,
        }
    }
}

pub(crate) fn schedule_gather_base_claims_pr(
    claims: &DeviceSlice<PR>,
    gather: BaseClaimGatherPr,
    context: &ProverContext,
) -> CudaResult<GatheredBaseClaimsPr> {
    assert_eq!(
        claims.len(),
        gather.claim_count,
        "Proth120 claim map length mismatch"
    );
    let count = BASE_CLAIM_COUNT as u32;
    let mut values = context.alloc(BASE_CLAIM_COUNT, AllocationPlacement::BestFit)?;
    PrGatherBaseClaimsFunction(ab_pr_gkr_gather_base_claims_kernel).launch(
        &CudaLaunchConfig::basic(count.div_ceil(128), 128, context.get_exec_stream()),
        &PrGatherBaseClaimsArguments::new(
            claims.as_ptr(),
            gather.indices,
            values.as_mut_ptr(),
            count,
        ),
    )?;
    Ok(GatheredBaseClaimsPr {
        values,
        memory_witness_count: gather.memory_witness_count,
        setup_count: gather.setup_count,
    })
}
