use std::collections::BTreeMap;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::static_host::{alloc_static_pinned_box_from_slice, StaticPinnedBox};
use gpu_prover_context::ProverContext;

use crate::proth120::backward::scheduled_execution::{
    note_device, note_resource, resource_ledger_active, ResourceEventPr, ResourceIdPr,
};
use crate::upstream::{GKRAddress, PR};

cuda_kernel_signature_arguments_and_function!(pub(crate) PrGatherBaseClaims, claims: *const PR, indices: *const u32, out: *mut PR, count: u32);
cuda_kernel_declaration!(pub(crate) ab_pr_gkr_gather_base_claims_kernel(claims: *const PR, indices: *const u32, out: *mut PR, count: u32));

#[repr(C)]
struct GatherArgumentsLayout {
    claims: *const PR,
    indices: *const u32,
    out: *mut PR,
    count: u32,
}
#[allow(dead_code)]
pub(crate) const PR_GATHER_ARGUMENT_BYTES: usize = size_of::<GatherArgumentsLayout>();
const _: () = {
    assert!(size_of::<GatherArgumentsLayout>() == 32);
    assert!(std::mem::offset_of!(GatherArgumentsLayout, count) == 24);
};

pub(crate) struct GatheredBaseClaimsPr {
    pub(crate) values: DeviceAllocation<PR>,
    _indices: DeviceAllocation<u32>,
    _indices_host: StaticPinnedBox<u32>,
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

pub(crate) fn schedule_gather_base_claims_pr(
    claims: &DeviceSlice<PR>,
    claim_addresses: &[GKRAddress],
    memory_columns: usize,
    witness_columns: usize,
    setup_columns: usize,
    context: &ProverContext,
) -> CudaResult<GatheredBaseClaimsPr> {
    assert_eq!(
        claims.len(),
        claim_addresses.len(),
        "Proth120 claim map length mismatch"
    );
    let indices = dense_claim_indices(
        claim_addresses,
        memory_columns,
        witness_columns,
        setup_columns,
    );
    assert!(!indices.is_empty(), "Proth120 dense base claims are empty");
    let count = u32::try_from(indices.len()).expect("Proth120 base claim count exceeds u32");
    let indices_host = alloc_static_pinned_box_from_slice(&indices)?;
    let mut device_indices = context.alloc(indices.len(), AllocationPlacement::BestFit)?;
    let mut values = context.alloc(indices.len(), AllocationPlacement::BestFit)?;
    note_device(
        context,
        "claims",
        None,
        ResourceEventPr::Allocated,
        "claims.gathered.indices",
        &device_indices,
    );
    note_device(
        context,
        "claims",
        None,
        ResourceEventPr::Allocated,
        "claims.gathered.values",
        &values,
    );
    if resource_ledger_active() {
        note_resource(
            context,
            "claims",
            None,
            ResourceEventPr::HostKeepalive,
            "claims.gathered.indices_source",
            ResourceIdPr::host(&indices_host[..]),
            None,
        );
    }
    memory_copy_async(
        &mut device_indices,
        &*indices_host,
        context.get_exec_stream(),
    )?;
    PrGatherBaseClaimsFunction(ab_pr_gkr_gather_base_claims_kernel).launch(
        &CudaLaunchConfig::basic(count.div_ceil(128), 128, context.get_exec_stream()),
        &PrGatherBaseClaimsArguments::new(
            claims.as_ptr(),
            device_indices.as_ptr(),
            values.as_mut_ptr(),
            count,
        ),
    )?;
    Ok(GatheredBaseClaimsPr {
        values,
        _indices: device_indices,
        _indices_host: indices_host,
        memory_witness_count: memory_columns
            .checked_add(witness_columns)
            .expect("Proth120 raw claim count overflow"),
        setup_count: setup_columns,
    })
}
