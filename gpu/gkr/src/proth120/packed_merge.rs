use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_hash::keccak256::{keccak256_pow, transcript_draw_fields};
use gpu_prover_context::ProverContext;

use crate::proth120::base_layer_claims::GatheredBaseClaimsPr;
use crate::proth120::proof_layout::ProofSlabPr;
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

pub(crate) fn launch_merge_claims_pr(
    claims: &DeviceSlice<PR>,
    extra: &DeviceSlice<PR>,
    pack_log2: u32,
    merged: &mut DeviceSlice<PR>,
    context: &ProverContext,
) -> CudaResult<()> {
    assert_eq!(pack_log2, 4, "Proth120 packed merge requires pack_log2=4");
    assert_eq!(
        extra.len(),
        4,
        "Proth120 packed merge coordinate count mismatch"
    );
    assert_eq!(
        merged.len(),
        claims.len().div_ceil(16),
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
    assert_eq!(pack_log2, 4, "Proth120 packed merge requires pack_log2=4");
    assert_eq!(seed.len(), 32, "Proth120 packed merge seed length mismatch");
    assert_eq!(
        gathered.values.len(),
        gathered.memory_witness_count + gathered.setup_count,
        "Proth120 packed merge dense claim count mismatch"
    );
    let memory_claim_count = gathered.memory_witness_count.div_ceil(16);
    let setup_claim_count = gathered.setup_count.div_ceil(16);
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
        (claim_point.len() + 4) * 16,
        proof.layout.evaluation_point.len(),
        "Proth120 packed merge point mirror count mismatch"
    );
    let stream = context.get_exec_stream();
    let mut extra = context.alloc(4, AllocationPlacement::BestFit)?;
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
    let mut point = context.alloc(claim_point.len() + 4, AllocationPlacement::BestFit)?;
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
    Ok(GkrOutputPr {
        claims,
        memory_claim_count,
        point,
        batching,
        seed: output_seed,
        _extra: extra,
        _gathered: gathered,
    })
}
