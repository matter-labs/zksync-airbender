use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::static_host::{alloc_static_pinned_box_from_slice, StaticPinnedBox};
use gpu_prover_context::transfer::Transfer;
use gpu_prover_context::ProverContext;

use crate::proth120::backward::scheduled_execution::{
    note_device, note_resource, resource_ledger_active, ResourceEventPr, ResourceIdPr,
};
use crate::proth120::programs::GkrProgramsPr;
use crate::proth120::proof_layout::ProofLayoutPr;
use crate::transform::logical_protocol_address;
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
    _indices_host: Arc<StaticPinnedBox<u32>>,
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

/// A circuit's dense base-claim gather indices, built once from its programs and
/// proof layout; the pinned buffer is the H2D source of every proof's copy.
pub struct BaseClaimIndicesHostPr {
    indices: Arc<StaticPinnedBox<u32>>,
}

impl BaseClaimIndicesHostPr {
    pub fn new(
        programs: &GkrProgramsPr,
        layout: &ProofLayoutPr,
        memory_columns: usize,
        witness_columns: usize,
        setup_columns: usize,
    ) -> CudaResult<Self> {
        let indices = dense_claim_indices(
            &final_claim_addresses_pr(programs, layout),
            memory_columns,
            witness_columns,
            setup_columns,
        );
        Ok(Self {
            indices: Arc::new(alloc_static_pinned_box_from_slice(&indices)?),
        })
    }
}

/// A proof's device copy of [`BaseClaimIndicesHostPr`], uploaded with its inputs.
pub struct BaseClaimIndicesPr {
    host: Arc<StaticPinnedBox<u32>>,
    device: DeviceAllocation<u32>,
}

impl BaseClaimIndicesPr {
    pub fn allocate(host: &BaseClaimIndicesHostPr, context: &ProverContext) -> CudaResult<Self> {
        Ok(Self {
            host: Arc::clone(&host.indices),
            device: context.alloc(host.indices.len(), AllocationPlacement::BestFit)?,
        })
    }

    pub fn schedule_transfer<'a>(
        &mut self,
        transfer: &mut Transfer<'a>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        transfer.schedule(Arc::clone(&self.host), &mut self.device, context)
    }
}

/// Gathers the dense base claims; `uploaded` indices must equal the ones derived
/// from `claim_addresses`, which are otherwise copied in on `exec_stream`.
pub(crate) fn schedule_gather_base_claims_pr(
    claims: &DeviceSlice<PR>,
    claim_addresses: &[GKRAddress],
    memory_columns: usize,
    witness_columns: usize,
    setup_columns: usize,
    uploaded: Option<BaseClaimIndicesPr>,
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
    let (indices_host, device_indices) = match uploaded {
        Some(BaseClaimIndicesPr { host, device }) => {
            assert_eq!(
                host[..],
                indices[..],
                "Proth120 uploaded base-claim indices differ from the final claim layout"
            );
            (host, device)
        }
        None => {
            let host = Arc::new(alloc_static_pinned_box_from_slice(&indices)?);
            let mut device = context.alloc(indices.len(), AllocationPlacement::BestFit)?;
            memory_copy_async(&mut device, &host[..], context.get_exec_stream())?;
            (host, device)
        }
    };
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
