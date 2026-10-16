use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_hash::keccak256::{keccak256_pow, transcript_draw_fields};
use gpu_prover_context::ProverContext;
use gpu_trace::trace::packed::PackedCosetRecomputeOracle;

use crate::proth120::backward::scheduled_execution::{note_device, ResourceEventPr};
use crate::proth120::backward::GpuGKRBackwardScheduledExecutionPr;
use crate::proth120::base_layer_claims::{schedule_gather_base_claims_pr, GatheredBaseClaimsPr};
use crate::proth120::proof_layout::ProofSlabPr;
use crate::setup::PackedSetupSource;
use crate::upstream::PR;

cuda_kernel_signature_arguments_and_function!(pub(crate) PrMergeClaims, claims: *const PR, count: u32, extra: *const PR, pack_log2: u32, merged: *mut PR);
cuda_kernel_declaration!(pub(crate) ab_pr_gkr_merge_claims_kernel(claims: *const PR, count: u32, extra: *const PR, pack_log2: u32, merged: *mut PR));

#[repr(C)]
struct MergeArgumentsLayout {
    claims: *const PR,
    count: u32,
    extra: *const PR,
    pack_log2: u32,
    merged: *mut PR,
}
#[allow(dead_code)]
pub(crate) const PR_MERGE_ARGUMENT_BYTES: usize = size_of::<MergeArgumentsLayout>();
const _: () = {
    assert!(size_of::<MergeArgumentsLayout>() == 40);
    assert!(std::mem::offset_of!(MergeArgumentsLayout, extra) == 16);
    assert!(std::mem::offset_of!(MergeArgumentsLayout, merged) == 32);
};

pub struct GkrOutputPr {
    claims: DeviceAllocation<PR>,
    memory_claim_count: usize,
    point: DeviceAllocation<PR>,
    batching: DeviceAllocation<PR>,
    seed: DeviceAllocation<u8>,
    _extra: DeviceAllocation<PR>,
    _gathered: GatheredBaseClaimsPr,
    _coefficient_upload_callbacks: Option<Callbacks<'static>>,
    pub(crate) backward: Option<GpuGKRBackwardScheduledExecutionPr>,
}

#[allow(clippy::too_many_arguments)]
pub fn schedule_base_layer_claims_and_packed_merge_pr(
    backward: &mut GpuGKRBackwardScheduledExecutionPr,
    base: &PackedCosetRecomputeOracle<PR>,
    setup: &PackedSetupSource<'_>,
    pack_log2: u32,
    batching_pow_bits: u32,
    proof: &mut ProofSlabPr,
    context: &ProverContext,
) -> CudaResult<GkrOutputPr> {
    assert_eq!(
        pack_log2,
        base.pack_log2(),
        "Proth120 base packing mismatch"
    );
    assert_eq!(
        pack_log2, setup.host.pack_log2,
        "Proth120 setup packing mismatch"
    );
    let addresses = backward.final_claim_addresses();
    let memory_columns = addresses
        .iter()
        .filter(|address| matches!(address, crate::upstream::GKRAddress::BaseLayerMemory(_)))
        .count();
    let witness_columns = addresses
        .iter()
        .filter(|address| matches!(address, crate::upstream::GKRAddress::BaseLayerWitness(_)))
        .count();
    assert_eq!(
        memory_columns + witness_columns,
        base.columns(),
        "Proth120 raw claim columns mismatch"
    );
    let gathered = schedule_gather_base_claims_pr(
        backward.final_claims(),
        addresses,
        memory_columns,
        witness_columns,
        setup.raw().columns_count,
        context,
    )?;
    let (seed, point) = backward.final_device_seed_and_claim_point_mut();
    assert_eq!(
        point.len(),
        base.log_rows() as usize,
        "Proth120 base claim point log mismatch"
    );
    let mut output = schedule_packed_merge_pr(
        gathered,
        seed,
        point,
        pack_log2,
        batching_pow_bits,
        proof,
        context,
    )?;
    output._coefficient_upload_callbacks = backward.coefficient_upload_callbacks.take();
    Ok(output)
}

pub struct GkrWhirHandoffPr<'a> {
    pub seed: &'a mut DeviceSlice<u8>,
    pub claims: &'a DeviceSlice<PR>,
    pub base_layer_point: &'a DeviceSlice<PR>,
    pub batching_challenge: &'a DeviceSlice<PR>,
}

impl GkrOutputPr {
    pub fn merged_claims(&self) -> &DeviceSlice<PR> {
        &self.claims
    }
    pub fn memory_claims(&self) -> &DeviceSlice<PR> {
        &self.claims[..self.memory_claim_count]
    }
    pub fn setup_claims(&self) -> &DeviceSlice<PR> {
        &self.claims[self.memory_claim_count..]
    }
    pub fn evaluation_point(&self) -> &DeviceSlice<PR> {
        &self.point
    }
    pub fn batching_challenge(&self) -> &DeviceVariable<PR> {
        &self.batching[0]
    }
    pub fn seed(&mut self) -> &mut DeviceSlice<u8> {
        &mut self.seed
    }
    pub fn whir_handoff(&mut self) -> GkrWhirHandoffPr<'_> {
        GkrWhirHandoffPr {
            seed: &mut self.seed,
            claims: &self.claims,
            base_layer_point: &self.point,
            batching_challenge: &self.batching,
        }
    }
}

fn assert_supported_pack_pr(pack_log2: u32) {
    assert!(
        (1..=4).contains(&pack_log2),
        "Proth120 packed merge supports pack_log2 1..=4, got {pack_log2}"
    );
}

pub(crate) fn launch_merge_claims_pr(
    claims: &DeviceSlice<PR>,
    extra: &DeviceSlice<PR>,
    pack_log2: u32,
    merged: &mut DeviceSlice<PR>,
    context: &ProverContext,
) -> CudaResult<()> {
    assert_supported_pack_pr(pack_log2);
    assert_eq!(
        extra.len(),
        pack_log2 as usize,
        "Proth120 packed merge coordinate count mismatch"
    );
    assert_eq!(
        merged.len(),
        claims.len().div_ceil(1 << pack_log2),
        "Proth120 packed merge output count mismatch"
    );
    if claims.is_empty() {
        return Ok(());
    }
    let count = u32::try_from(claims.len()).expect("Proth120 packed merge count exceeds u32");
    let groups =
        u32::try_from(merged.len()).expect("Proth120 packed merge group count exceeds u32");
    PrMergeClaimsFunction(ab_pr_gkr_merge_claims_kernel).launch(
        &CudaLaunchConfig::basic(groups.div_ceil(4), 128, context.get_exec_stream()),
        &PrMergeClaimsArguments::new(
            claims.as_ptr(),
            count,
            extra.as_ptr(),
            pack_log2,
            merged.as_mut_ptr(),
        ),
    )
}

pub(crate) fn schedule_packed_merge_pr(
    gathered: GatheredBaseClaimsPr,
    seed: &mut DeviceAllocation<u8>,
    claim_point: &DeviceSlice<PR>,
    pack_log2: u32,
    batching_pow_bits: u32,
    proof: &mut ProofSlabPr,
    context: &ProverContext,
) -> CudaResult<GkrOutputPr> {
    schedule_packed_merge_pr_with_snapshots(
        gathered,
        seed,
        claim_point,
        pack_log2,
        batching_pow_bits,
        proof,
        context,
        |_, _| Ok(()),
    )
}

pub(crate) fn schedule_packed_merge_pr_with_snapshots<F>(
    gathered: GatheredBaseClaimsPr,
    seed: &mut DeviceAllocation<u8>,
    claim_point: &DeviceSlice<PR>,
    pack_log2: u32,
    batching_pow_bits: u32,
    proof: &mut ProofSlabPr,
    context: &ProverContext,
    mut snapshot: F,
) -> CudaResult<GkrOutputPr>
where
    F: FnMut(usize, &DeviceSlice<u8>) -> CudaResult<()>,
{
    assert_supported_pack_pr(pack_log2);
    let pack_width = 1usize << pack_log2;
    let pack_coordinates = pack_log2 as usize;
    assert_eq!(seed.len(), 32, "Proth120 packed merge seed length mismatch");
    assert_eq!(
        gathered.values.len(),
        gathered.memory_witness_count + gathered.setup_count,
        "Proth120 packed merge dense claim count mismatch"
    );
    let memory_claim_count = gathered.memory_witness_count.div_ceil(pack_width);
    let setup_claim_count = gathered.setup_count.div_ceil(pack_width);
    assert_eq!(
        memory_claim_count * 16,
        proof.layout.memory_claims.len(),
        "Proth120 packed merge memory mirror count mismatch"
    );
    assert_eq!(
        setup_claim_count * 16,
        proof.layout.setup_claims.len(),
        "Proth120 packed merge setup mirror count mismatch"
    );
    assert_eq!(
        (claim_point.len() + pack_coordinates) * 16,
        proof.layout.evaluation_point.len(),
        "Proth120 packed merge point mirror count mismatch"
    );
    let stream = context.get_exec_stream();
    let mut extra = context.alloc(pack_coordinates, AllocationPlacement::BestFit)?;
    transcript_draw_fields(seed, &mut extra, stream)?;
    snapshot(0, seed)?;
    let mut claims = context.alloc(
        memory_claim_count + setup_claim_count,
        AllocationPlacement::BestFit,
    )?;
    launch_merge_claims_pr(
        &gathered.values[..gathered.memory_witness_count],
        &extra,
        pack_log2,
        &mut claims[..memory_claim_count],
        context,
    )?;
    launch_merge_claims_pr(
        &gathered.values[gathered.memory_witness_count..],
        &extra,
        pack_log2,
        &mut claims[memory_claim_count..],
        context,
    )?;
    memory_copy_async(
        proof.memory_claims_device_mut(),
        &claims[..memory_claim_count],
        stream,
    )?;
    memory_copy_async(
        proof.setup_claims_device_mut(),
        &claims[memory_claim_count..],
        stream,
    )?;
    let mut point = context.alloc(
        claim_point.len() + pack_coordinates,
        AllocationPlacement::BestFit,
    )?;
    memory_copy_async(&mut point[..claim_point.len()], claim_point, stream)?;
    memory_copy_async(&mut point[claim_point.len()..], &extra[..], stream)?;
    memory_copy_async(proof.evaluation_point_device_mut(), &point[..], stream)?;
    keccak256_pow(
        seed,
        batching_pow_bits,
        proof.batched_nonce_device_mut(),
        stream,
    )?;
    snapshot(1, seed)?;
    let mut batching = context.alloc(1, AllocationPlacement::BestFit)?;
    transcript_draw_fields(seed, &mut batching, stream)?;
    snapshot(2, seed)?;
    memory_copy_async(proof.batching_challenge_device_mut(), &batching[0], stream)?;
    memory_copy_async(proof.seed_snapshot_device_mut(), &seed[..], stream)?;
    let mut output_seed = context.alloc(32, AllocationPlacement::BestFit)?;
    memory_copy_async(&mut output_seed, &seed[..], stream)?;
    for (owner, allocation) in [
        ("claims.extra", &extra),
        ("claims.merged", &claims),
        ("claims.point", &point),
        ("claims.batching", &batching),
    ] {
        note_device(
            context,
            "claims",
            None,
            ResourceEventPr::Allocated,
            owner,
            allocation,
        );
    }
    note_device(
        context,
        "claims",
        None,
        ResourceEventPr::Allocated,
        "claims.seed",
        &output_seed,
    );
    Ok(GkrOutputPr {
        claims,
        memory_claim_count,
        point,
        batching,
        seed: output_seed,
        _extra: extra,
        _gathered: gathered,
        _coefficient_upload_callbacks: None,
        backward: None,
    })
}
