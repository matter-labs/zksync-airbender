use std::collections::BTreeMap;
use std::sync::Arc;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;

use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{
    DeviceAllocation, HostAllocation, ProverContext, UnsafeMutAccessor,
};
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::base_layer_claims::{
    clone_base_layer_extra_evaluations_from_slab, ScheduledBaseLayerClaimsState,
};
use crate::prover::proof::layout::ProofLayout;
use crate::prover::whir::fold::{take_scheduled_whir_proof, ScheduledWhirProofState};
use crate::upstream::{DefaultTreeConstructor, GKRExternalChallenges, GKRProof};

use super::grand_product_accumulator_from_explicit_evaluations;

pub(in crate::prover::proof) fn schedule_terminal_proof_assembly(
    proof_slab: &Arc<DeviceAllocation<E4>>,
    proof_layout: &ProofLayout,
    proof_slot: UnsafeMutAccessor<Option<GKRProof<BF, E4, DefaultTreeConstructor>>>,
    whir_shared_state: UnsafeMutAccessor<ScheduledWhirProofState>,
    base_layer_claims_shared_state: UnsafeMutAccessor<ScheduledBaseLayerClaimsState<E4>>,
    external_challenges: GKRExternalChallenges<BF, E4>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<HostAllocation<[u8]>> {
    let stream = context.get_exec_stream();

    // Terminal D2H of the whole proof slab into a pinned host mirror, scheduled
    // after all slab-write work above. The mirror drives the single host-side
    // parse that replaces per-piece host bookkeeping.
    let mut mirror = unsafe { context.alloc_host_uninit_slice::<u8>(proof_layout.total_bytes) };
    let slab_u8 = unsafe {
        era_cudart::slice::DeviceSlice::from_raw_parts(
            proof_slab.as_ptr() as *const u8,
            proof_layout.total_bytes,
        )
    };
    memory_copy_async(&mut mirror, slab_u8, stream)?;
    let proof_host_mirror_accessor = mirror.get_accessor();
    callbacks.schedule(
        {
            let external_challenges = external_challenges.clone();
            let proof_layout_for_parse = proof_layout.clone();
            move || {
                // Phase 4: source all device-produced proof fields from the
                // terminal-D2H'd slab — including `final_explicit_evaluations`,
                // which final forward dim-reduction wrote directly into the
                // slab's `output_evaluations` block.
                let slab_bytes = unsafe { proof_host_mirror_accessor.get() };
                let final_explicit_evaluations =
                    proof_layout_for_parse.parse_final_explicit_evaluations(slab_bytes);
                let mut extra_by_layer = BTreeMap::new();
                let base_layer_idx = 0usize;
                let extra = clone_base_layer_extra_evaluations_from_slab(
                    base_layer_claims_shared_state,
                    &proof_layout_for_parse,
                    slab_bytes,
                );
                if !extra.is_empty() {
                    extra_by_layer.insert(base_layer_idx, extra);
                }
                let sumcheck_intermediate_values = proof_layout_for_parse
                    .parse_sumcheck_intermediate_values(slab_bytes, extra_by_layer);
                let mut whir_proof = proof_layout_for_parse.parse_whir_proof(slab_bytes);
                let host_whir_proof = take_scheduled_whir_proof(whir_shared_state);
                whir_proof.setup_commitment.queries = host_whir_proof.setup_commitment.queries;
                whir_proof.memory_commitment.queries = host_whir_proof.memory_commitment.queries;
                whir_proof.witness_commitment.queries = host_whir_proof.witness_commitment.queries;
                whir_proof.final_monomials = host_whir_proof.final_monomials;
                whir_proof.intermediate_whir_oracles = host_whir_proof.intermediate_whir_oracles;
                let grand_product_accumulator_computed =
                    grand_product_accumulator_from_explicit_evaluations(
                        &final_explicit_evaluations,
                    );
                unsafe { proof_slot.get_mut() }.replace(GKRProof {
                    external_challenges: external_challenges.clone(),
                    final_explicit_evaluations,
                    sumcheck_intermediate_values,
                    whir_proof,
                    grand_product_accumulator_computed,
                });
            }
        },
        stream,
    )?;

    Ok(mirror)
}
