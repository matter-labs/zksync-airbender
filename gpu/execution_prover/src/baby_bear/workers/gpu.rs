use crate::upstream::{CommitmentMode, GKRCircuitArtifact, ProverConfig};
use crate::workers::gpu::{
    follower_label, JobType, PhaseOne, PhaseOneInputs, RequestKind, RequestState,
};
use crate::workers::gpu_manager::{GpuWorkRequest, GpuWorkResult};
use crate::A;
use era_cudart::result::CudaResult;
use execution_prover::messages::{
    MemoryCommitmentRequest, MemoryCommitmentResult, MemoryPartialTrees, ProofRequest, ProofResult,
};
use execution_prover::ProofProfile;
use gpu_circuit_prover::baby_bear::GpuGKRProofJob;
use gpu_core::primitives::field::BF;
use gpu_gkr::baby_bear::setup::GpuGKRSetupTransfer;
use gpu_gkr::baby_bear::stage1::merged_commitment::commit_merged_from_transfers;
use gpu_gkr::baby_bear::stage1::merged_commitment::GpuGKRMergedCommitTransfer;
use gpu_prover_context::ProverContext;
use gpu_trace::baby_bear::trace::memory::{
    commit_memory_from_transfers_for_geometry, MemoryCommitmentJob,
};
use gpu_trace::baby_bear::trace::memory_cap::{
    GpuGKRMemoryCapHost, GpuGKRMemoryCapTransfer, PartialTrees,
};
use gpu_trace::trace::decoder::DecoderTableTransfer;
use gpu_trace::trace::holder::resolve_partial_tree_reduction_layers;
use gpu_trace::trace::memory_cap::PartialTreesGeometry;
use gpu_trace::trace::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};
use gpu_trace::witness::circuit_type::CircuitType;
use log::{debug, trace};
use std::sync::Arc;

const FINAL_TRACE_SIZE_LOG_2: u32 = 4;

pub(crate) fn schedule_phase_one<'a>(
    device_id: i32,
    context: &ProverContext,
    request: GpuWorkRequest<A>,
) -> CudaResult<PhaseOne<'a>> {
    // Decompose the request into bookkeeping plus the host buffers that
    // become Phase 1 H2D inputs.
    let (mut state, inits_and_teardowns_host, tracing_data_host) = match request {
        GpuWorkRequest::L1WrapProof(_) => {
            unreachable!("L1Wrap proof requests return early above")
        }
        GpuWorkRequest::MemoryCommitment(req) => {
            let MemoryCommitmentRequest {
                batch_id,
                circuit_type,
                sequence_id,
                precomputations,
                inits_and_teardowns,
                tracing_data,
                profile,
                partial_tree_buffer,
            } = req;

            let state = RequestState {
                batch_id,
                circuit_type,
                sequence_id,
                precomputations,
                kind: RequestKind::MemoryCommitment,
                external_challenges: None,
                memory_caps: None,
                memory_partial_trees: None,
                partial_tree_buffer,
                inits_and_teardowns_result: inits_and_teardowns.clone(),
                tracing_data_result: tracing_data.clone(),

                profile,
                device_peak_bytes: None,
                direction: None,
                follower: None,
            };
            (state, inits_and_teardowns, tracing_data)
        }
        GpuWorkRequest::Proof(req) => {
            let ProofRequest {
                batch_id,
                circuit_type,
                sequence_id,
                precomputations,
                inits_and_teardowns,
                tracing_data,
                external_challenges,
                memory_caps,
                memory_partial_trees,
                profile,
            } = req;

            let state = RequestState {
                batch_id,
                circuit_type,
                sequence_id,
                precomputations,
                kind: RequestKind::Proof,
                external_challenges: Some(external_challenges),
                memory_caps: Some(memory_caps),
                memory_partial_trees,
                partial_tree_buffer: None,
                inits_and_teardowns_result: inits_and_teardowns.clone(),
                tracing_data_result: tracing_data.clone(),

                profile,
                device_peak_bytes: None,
                direction: None,
                follower: None,
            };
            (state, inits_and_teardowns, tracing_data)
        }
        GpuWorkRequest::SetupInitialization(_) => {
            unreachable!("setup initialization returns early above")
        }
    };
    let batch_id = state.batch_id;
    let circuit_type = state.circuit_type;
    let sequence_id = state.sequence_id;
    let is_proof = matches!(state.kind, RequestKind::Proof);
    let memory_partial_trees = state.memory_partial_trees.take();

    let resolved = state
        .precomputations
        .baby_bear()
        .profile_config(state.profile);
    let config = &resolved.0;
    let geometry = resolved.1;
    let setup_host = state
        .precomputations
        .baby_bear()
        .setup_host
        .get_initialized(state.profile);
    let memory_host = state.memory_caps.as_deref().map(|caps| {
        Arc::new(GpuGKRMemoryCapHost::from_per_coset_caps_for_geometry(
            caps, geometry,
        ))
    });
    let decoder_transfer =
        if let Some(host) = state.precomputations.baby_bear().decoder_host.as_ref() {
            Some(DecoderTableTransfer::new(Arc::clone(host), context)?)
        } else {
            None
        };

    // Captured before the host buffer is consumed below. `None` covers both
    // circuits that carry no i&t at all and the TRIVIAL (dummy) leading unified
    // chunks — only a unified execution's trailing circuits hold real i&t data.
    let carried_top_bits = inits_and_teardowns_host
        .as_ref()
        .map(|host| host.top_bits.clone());

    let num_teardown_sets = state
        .precomputations
        .baby_bear()
        .gkr_programs
        .compiled_circuit()
        .memory_layout
        .teardown_sets
        .len();
    let trace_len = circuit_type.get_domain_size();
    let inits_and_teardowns_transfer = if num_teardown_sets > 0 {
        Some(InitsAndTeardownsTransfer::new(
            inits_and_teardowns_host,
            num_teardown_sets,
            trace_len,
            context,
        )?)
    } else {
        None
    };

    let tracing_data_transfer = if let Some(tracing_data_host) = tracing_data_host {
        Some(TracingDataTransfer::new(
            tracing_data_host,
            trace_len,
            context,
        )?)
    } else {
        None
    };

    let inputs: PhaseOneInputs<'a> = if is_proof {
        let setup_transfer = setup_host
            .as_ref()
            .map(|host| {
                GpuGKRSetupTransfer::new(
                    Arc::clone(host),
                    crate::memory_policy::partial_trees(circuit_type, state.profile).setup,
                    context,
                )
            })
            .transpose()?;
        let admitted_memory_host =
            Arc::clone(memory_host.as_ref().expect("a proof needs memory caps"));
        let memory_host =
            match proof_partial_trees(circuit_type, state.profile, memory_partial_trees) {
                Some(trees) => {
                    let host = GpuGKRMemoryCapHost::from_per_coset_caps_and_partial_trees(
                        state.memory_caps.as_deref().expect("proof caps"),
                        geometry,
                        memory_partial_trees_geometry(
                            state
                                .precomputations
                                .baby_bear()
                                .gkr_programs
                                .compiled_circuit(),
                            config,
                            config.commitment_mode,
                            crate::memory_policy::partial_trees(circuit_type, state.profile).memory,
                        ),
                        trees,
                    );
                    Arc::new(host)
                }
                None => admitted_memory_host,
            };
        let memory_transfer = GpuGKRMemoryCapTransfer::new(memory_host, context)?;
        let external_challenges_value = state
            .external_challenges
            .expect("Proof requires external_challenges");
        // Without i&t data the windows are all zero, which is what the unified
        // verifier requires of its leading instances.
        let top_bits = carried_top_bits.unwrap_or_else(|| vec![0u32; num_teardown_sets]);
        assert_eq!(
            top_bits.len(),
            num_teardown_sets,
            "inits-and-teardowns top bits must cover every teardown set of {circuit_type:?}"
        );
        let mut bundle = gpu_circuit_prover::baby_bear::inputs::GpuGKRProofTransfer::<'_, A>::new(
            setup_transfer,
            decoder_transfer,
            inits_and_teardowns_transfer,
            tracing_data_transfer,
            memory_transfer,
            &top_bits,
            external_challenges_value,
            context,
        )?;
        trace!(
            "BATCH[{batch_id}] GPU_WORKER[{device_id}] scheduling proof H2D bundle for circuit {circuit_type:?}[{sequence_id}]"
        );
        bundle.schedule(context)?;
        PhaseOneInputs::Proof(bundle)
    } else if config.commitment_mode == CommitmentMode::MergedMemoryAndWitness {
        let setup_transfer = GpuGKRSetupTransfer::new(
            Arc::clone(setup_host.as_ref().expect("a merged commit needs a setup")),
            crate::memory_policy::partial_trees(circuit_type, state.profile).setup,
            context,
        )?;
        let mut bundle = GpuGKRMergedCommitTransfer::new(
            setup_transfer,
            decoder_transfer,
            inits_and_teardowns_transfer,
            tracing_data_transfer,
            context,
        )?;
        bundle.schedule(context)?;
        PhaseOneInputs::MergedCommitment(bundle)
    } else {
        let mut bundle =
            gpu_trace::baby_bear::trace::memory::GpuGKRCommitMemoryTransfer::<'_, A>::new(
                decoder_transfer,
                inits_and_teardowns_transfer,
                tracing_data_transfer,
                context,
            )?;
        trace!(
            "BATCH[{batch_id}] GPU_WORKER[{device_id}] scheduling commit-memory H2D bundle for circuit {circuit_type:?}[{sequence_id}]"
        );
        bundle.schedule(context)?;
        PhaseOneInputs::MemoryCommitment(bundle)
    };

    Ok(PhaseOne { state, inputs })
}

pub(crate) fn enqueue_phase_two<'a>(
    device_id: i32,
    context: &ProverContext,
    state: &mut RequestState,
    inputs: PhaseOneInputs<'a>,
) -> CudaResult<JobType<'a>> {
    let batch_id = state.batch_id;
    let circuit_type = state.circuit_type;
    let sequence_id = state.sequence_id;
    let job = {
        let resolved = state
            .precomputations
            .baby_bear()
            .profile_config(state.profile);
        let prover_config = &resolved.0;
        let final_trace_size_log_2 = FINAL_TRACE_SIZE_LOG_2;
        let compiled_circuit_arc = Arc::clone(
            state
                .precomputations
                .baby_bear()
                .gkr_programs
                .compiled_circuit(),
        );
        match inputs {
            PhaseOneInputs::Proof(bundle) => {
                trace!(
            "BATCH[{batch_id}] GPU_WORKER[{device_id}] producing proof for circuit {circuit_type:?}[{sequence_id}]"
        );
                context.reset_used_mem_peak();
                let job = gpu_circuit_prover::proof::prove(
                    gpu_circuit_prover::baby_bear::BabyBearProofRequest::new(
                        &state.precomputations.baby_bear().gkr_programs,
                        prover_config,
                        final_trace_size_log_2,
                        bundle,
                        crate::memory_policy::policy(
                            circuit_type,
                            state.profile,
                            context.get_mem_size(),
                        ),
                        crate::memory_policy::partial_trees(circuit_type, state.profile),
                    ),
                    context,
                )?;
                state.device_peak_bytes = Some(context.get_used_mem_peak());
                JobType::Proof(job)
            }
            PhaseOneInputs::MemoryCommitment(bundle) => {
                trace!(
            "BATCH[{batch_id}] GPU_WORKER[{device_id}] producing memory commitment for circuit {circuit_type:?}[{sequence_id}]"
        );
                context.reset_used_mem_peak();
                let job = commit_memory_from_transfers_for_geometry::<A>(
                    circuit_type,
                    &compiled_circuit_arc,
                    bundle,
                    resolved.1,
                    crate::memory_policy::partial_trees(circuit_type, state.profile).memory,
                    context,
                )?;
                state.device_peak_bytes = Some(context.get_used_mem_peak());
                JobType::MemoryCommitment(job)
            }
            PhaseOneInputs::MergedCommitment(bundle) => {
                trace!(
            "BATCH[{batch_id}] GPU_WORKER[{device_id}] producing merged memory+witness commitment for circuit {circuit_type:?}[{sequence_id}]"
        );
                context.reset_used_mem_peak();
                let job = commit_merged_from_transfers::<A>(
                    &state.precomputations.baby_bear().gkr_programs,
                    prover_config,
                    bundle,
                    gpu_circuit_prover::baby_bear::presets::merged_commit_strategy(
                        circuit_type,
                        state.profile,
                    ),
                    crate::memory_policy::partial_trees(circuit_type, state.profile),
                    state.partial_tree_buffer.take(),
                    context,
                )?;
                state.device_peak_bytes = Some(context.get_used_mem_peak());
                JobType::MemoryCommitment(job)
            }
            PhaseOneInputs::SetupInitialization => {
                unreachable!("setup initialization returns early above")
            }
            PhaseOneInputs::L1Wrap(..) => {
                unreachable!("wrap inputs are handled by the outer dispatch")
            }
        }
    };
    Ok(job)
}

pub(crate) fn finish_memory_commitment(
    device_id: i32,
    state: RequestState,
    job: MemoryCommitmentJob<'_, A>,
) -> CudaResult<GpuWorkResult<A>> {
    let RequestState {
        batch_id,
        circuit_type,
        sequence_id,
        inits_and_teardowns_result,
        tracing_data_result,
        profile,
        device_peak_bytes,
        direction,
        follower,
        ..
    } = state;
    let follower = follower_label(follower);
    let (merkle_tree_caps, partial_trees, commitment_time_ms) = job.finish_with_partial_trees()?;
    let memory_partial_trees =
        partial_trees.map(|trees| persisted_partial_trees(circuit_type, profile, trees));
    let bytes = device_peak_bytes.expect("memory commitment device peak was recorded");
    let direction = direction.expect("memory commitment allocation direction was recorded");
    debug!(
        "BATCH[{batch_id}] GPU_WORKER[{device_id}] produced memory commitment for circuit {circuit_type:?}[{sequence_id}] profile {profile:?} direction {direction:?} follower {follower} device peak {bytes} B in {commitment_time_ms:.3} ms"
    );
    Ok(GpuWorkResult::MemoryCommitment(MemoryCommitmentResult {
        batch_id,
        circuit_type,
        sequence_id,
        inits_and_teardowns: inits_and_teardowns_result,
        tracing_data: tracing_data_result,
        merkle_tree_caps,
        memory_partial_trees,
    }))
}

pub(crate) fn finish_proof(
    device_id: i32,
    state: RequestState,
    job: GpuGKRProofJob<'_>,
) -> CudaResult<GpuWorkResult<A>> {
    let RequestState {
        batch_id,
        circuit_type,
        sequence_id,
        inits_and_teardowns_result,
        tracing_data_result,
        profile,
        device_peak_bytes,
        direction,
        follower,
        ..
    } = state;
    let follower = follower_label(follower);
    let (proof, proof_time_ms) = job.finish()?;
    let bytes = device_peak_bytes.expect("proof device peak was recorded");
    let direction = direction.expect("proof allocation direction was recorded");
    debug!(
        "BATCH[{batch_id}] GPU_WORKER[{device_id}] produced proof for circuit {circuit_type:?}[{sequence_id}] profile {profile:?} direction {direction:?} follower {follower} device peak {bytes} B in {proof_time_ms:.3} ms"
    );
    Ok(GpuWorkResult::Proof(ProofResult {
        batch_id,
        circuit_type,
        sequence_id,
        inits_and_teardowns: inits_and_teardowns_result,
        tracing_data: tracing_data_result,
        proof,
    }))
}

/// The geometry of a proof's memory-oracle partial trees: the oracle stage 1
/// builds for `commitment_mode` at the policy's resolved memory depth.
pub(crate) fn memory_partial_trees_geometry(
    compiled_circuit: &GKRCircuitArtifact<BF>,
    prover_config: &ProverConfig,
    commitment_mode: CommitmentMode,
    memory_reduction_layers: u32,
) -> PartialTreesGeometry {
    assert_eq!(prover_config.commitment_mode, commitment_mode);
    let geometry = crate::upstream::BaseCommitmentGeometry::from_config(
        prover_config,
        crate::upstream::BaseColumns::of(compiled_circuit),
    );
    let log_domain_size =
        u32::try_from(geometry.message_size_log2()).expect("message log2 exceeds u32");
    let log_lde_factor = geometry.lde_factor().trailing_zeros();
    let log_rows_per_leaf = geometry.values_per_leaf().trailing_zeros();
    let log_tree_cap_size = geometry.cap_size().trailing_zeros();
    let columns_count = geometry
        .oracle(crate::upstream::BaseOracleRole::Memory)
        .physical_columns();
    PartialTreesGeometry {
        log_domain_size,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        reduction_layers: resolve_partial_tree_reduction_layers(
            memory_reduction_layers,
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
        ),
        columns_count,
    }
}

/// The trees a proof request carries: required exactly when its profile
/// persists them, and only those of its own circuit and profile.
pub(crate) fn proof_partial_trees<T: fft::GoodAllocator>(
    circuit_type: CircuitType,
    profile: ProofProfile,
    trees: Option<MemoryPartialTrees<T>>,
) -> Option<PartialTrees<T>> {
    let required = crate::memory_policy::persists_memory_partial_trees(circuit_type, profile);
    let trees = match (required, trees) {
        (true, Some(trees)) => trees,
        (true, None) => panic!(
            "{circuit_type:?}/{profile:?} proof requires the memory partial trees persisted by its commitment"
        ),
        (false, Some(_)) => {
            panic!("{circuit_type:?}/{profile:?} proof does not take memory partial trees")
        }
        (false, None) => return None,
    };
    let MemoryPartialTrees {
        layout_version,
        circuit_type: trees_circuit_type,
        profile: trees_profile,
        log_domain_size,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        reduction_layers,
        columns_count,
        nodes,
    } = trees;
    assert_eq!(
        (trees_circuit_type, trees_profile),
        (circuit_type, profile),
        "memory partial trees belong to another circuit or profile"
    );
    Some(PartialTrees {
        layout_version,
        geometry: PartialTreesGeometry {
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            reduction_layers,
            columns_count,
        },
        nodes,
    })
}

fn persisted_partial_trees(
    circuit_type: CircuitType,
    profile: ProofProfile,
    trees: PartialTrees<A>,
) -> MemoryPartialTrees<A> {
    let PartialTrees {
        layout_version,
        geometry,
        nodes,
    } = trees;
    MemoryPartialTrees {
        layout_version,
        circuit_type,
        profile,
        log_domain_size: geometry.log_domain_size,
        log_lde_factor: geometry.log_lde_factor,
        log_rows_per_leaf: geometry.log_rows_per_leaf,
        log_tree_cap_size: geometry.log_tree_cap_size,
        reduction_layers: geometry.reduction_layers,
        columns_count: geometry.columns_count,
        nodes,
    }
}

#[cfg(test)]
mod tests;
