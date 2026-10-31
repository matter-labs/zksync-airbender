use super::factory::{stable_external_challenges, PreparedCircuit};
use crate::upstream::{CommitmentMode, DefaultTreeConstructor, GKRProof, MerkleTreeCapVarLength};
use crate::workers::gpu::memory_partial_trees_geometry;
use crate::A;
use era_cudart::result::CudaResult;
use gpu_circuit_prover::proof::inputs::GpuGKRProofTransfer;
use gpu_circuit_prover::proof::memory_policy::{PartialTreePolicy, ProofMemoryPolicy};
use gpu_circuit_prover::proof::merged_commitment::{
    commit_merged_from_transfers_with_policy, GpuGKRMergedCommitTransfer,
};
use gpu_circuit_prover::proof::ProofPreflight;
use gpu_circuit_prover::proof::{admit_dr_tail_before_transfers, prove, DrTailPreflightRequest};
use gpu_core::allocator::tracker::AllocationDirection;
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr::setup::GpuGKRSetupTransfer;
use gpu_prover_context::{AllocationMode, ProverContext};
use gpu_trace::trace::decoder::DecoderTableTransfer;
use gpu_trace::trace::memory::commit_memory_from_transfers_for_geometry;
use gpu_trace::trace::memory_transfer::{
    GpuGKRCommitMemoryTransfer, GpuGKRMemoryTransfer, GpuGKRMemoryTransferHost,
};
use gpu_trace::trace::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

const FINAL_TRACE_SIZE_LOG_2: u32 = 4;

pub(crate) fn drain(context: &ProverContext) -> CudaResult<()> {
    context.get_h2d_stream().synchronize()?;
    context.get_exec_stream().synchronize()?;
    Ok(())
}

pub(super) type InputTransfers<'a> = (
    Option<DecoderTableTransfer<'a>>,
    Option<InitsAndTeardownsTransfer<'a, A>>,
    Option<TracingDataTransfer<'a, A>>,
);

pub(super) fn input_transfers<'a>(
    context: &ProverContext,
    circuit: &PreparedCircuit,
) -> CudaResult<InputTransfers<'a>> {
    // Match production's allocation order so fragmentation is represented.
    let decoder = circuit
        .precomputations
        .baby_bear()
        .decoder_host
        .as_ref()
        .map(|host| DecoderTableTransfer::new(Arc::clone(host), context))
        .transpose()?;
    let num_teardown_sets = circuit
        .precomputations
        .baby_bear()
        .gkr_programs
        .compiled_circuit()
        .memory_layout
        .teardown_sets
        .len();
    let trace_len = circuit.circuit.get_domain_size();
    let inits = (num_teardown_sets > 0)
        .then(|| {
            InitsAndTeardownsTransfer::new(
                circuit.inputs.inits_and_teardowns.clone(),
                num_teardown_sets,
                trace_len,
                context,
            )
        })
        .transpose()?;
    let trace = circuit
        .inputs
        .tracing_data
        .clone()
        .map(|host| TracingDataTransfer::new(host, trace_len, context))
        .transpose()?;
    Ok((decoder, inits, trace))
}

pub(super) fn commit_memory(
    context: &ProverContext,
    circuit: &PreparedCircuit,
) -> CudaResult<Vec<MerkleTreeCapVarLength>> {
    let result = (|| {
        let resolved = circuit
            .precomputations
            .baby_bear()
            .resolved_config(circuit.profile);
        let config = resolved.config();
        let geometry = resolved.geometry();
        let (setup_host, _) = circuit.precomputations.admit_inputs_before_transfers(
            circuit.circuit,
            circuit.security_level,
            circuit.profile,
            None,
            context
                .ntt_device_context()
                .whir_leaf_transform_params()
                .omega_log_order,
        );
        let (decoder, inits, trace) = input_transfers(context, circuit)?;
        let job = if config.commitment_mode == CommitmentMode::MergedMemoryAndWitness {
            let setup = GpuGKRSetupTransfer::new(
                setup_host.expect("merged setup metadata admitted"),
                preset_setup_reduction_layers(circuit),
                context,
            )?;
            let mut inputs =
                GpuGKRMergedCommitTransfer::new(setup, decoder, inits, trace, context)?;
            if let Err(error) = inputs.schedule(context) {
                drain(context)?;
                return Err(error);
            }
            commit_merged_from_transfers_with_policy::<A>(
                &circuit.precomputations.baby_bear().gkr_programs,
                config,
                geometry,
                inputs,
                crate::memory_policy::merged_commit_strategy(circuit.circuit, circuit.profile),
                crate::memory_policy::partial_trees(circuit.circuit, circuit.profile),
                crate::memory_policy::persists_memory_partial_trees(
                    circuit.circuit,
                    circuit.profile,
                ),
                context,
            )?
        } else {
            let mut inputs = GpuGKRCommitMemoryTransfer::new(decoder, inits, trace, context)?;
            if let Err(error) = inputs.schedule(context) {
                drain(context)?;
                return Err(error);
            }
            commit_memory_from_transfers_for_geometry::<A>(
                circuit.circuit,
                circuit
                    .precomputations
                    .baby_bear()
                    .gkr_programs
                    .compiled_circuit(),
                inputs,
                config,
                geometry,
                preset_memory_reduction_layers(circuit),
                context,
            )?
        };
        job.finish().map(|(caps, _)| caps)
    })();
    drain(context)?;
    result
}

pub(super) fn preset_setup_reduction_layers(circuit: &PreparedCircuit) -> u32 {
    crate::memory_policy::partial_trees(circuit.circuit, circuit.profile).setup
}

pub(super) fn preset_memory_reduction_layers(circuit: &PreparedCircuit) -> u32 {
    crate::memory_policy::partial_trees(circuit.circuit, circuit.profile).memory
}

pub(super) fn schedule_proof_inputs<'a>(
    device_id: i32,
    context: &ProverContext,
    circuit: &PreparedCircuit,
    policy: Option<ProofMemoryPolicy>,
    partial_trees: Option<PartialTreePolicy>,
) -> CudaResult<(GpuGKRProofTransfer<'a, A>, ProofPreflight<BF>)> {
    let resolved = circuit
        .precomputations
        .baby_bear()
        .resolved_config(circuit.profile);
    let programs = &circuit.precomputations.baby_bear().gkr_programs;
    let config = resolved.config();
    let (setup_host, _memory_host) = circuit.precomputations.admit_inputs_before_transfers(
        circuit.circuit,
        circuit.security_level,
        circuit.profile,
        Some(
            circuit
                .memory_caps
                .as_deref()
                .expect("warm memory commitment"),
        ),
        context
            .ntt_device_context()
            .whir_leaf_transform_params()
            .omega_log_order,
    );
    let partial_trees = partial_trees
        .unwrap_or_else(|| crate::memory_policy::partial_trees(circuit.circuit, circuit.profile));
    let setup_reduction_layers = partial_trees.setup;
    let memory_reduction_layers = partial_trees.memory;
    let plan = admit_dr_tail_before_transfers(
        Some(DrTailPreflightRequest {
            gkr_programs: programs,
            prover_config: config,
            final_trace_size_log_2: FINAL_TRACE_SIZE_LOG_2,
            device_id,
            partial_trees,
            memory_policy: policy.unwrap_or_else(|| {
                crate::memory_policy::policy(
                    circuit.circuit,
                    circuit.profile,
                    context.get_mem_size(),
                )
            }),
            twiddle_domain_log2: context
                .ntt_device_context()
                .whir_leaf_transform_params()
                .omega_log_order,
        }),
        |plan| plan.unwrap(),
    )?;
    let (decoder, inits, trace) = input_transfers(context, circuit)?;
    let setup = setup_host
        .map(|host| GpuGKRSetupTransfer::new(host, setup_reduction_layers, context))
        .transpose()?;
    let memory_caps = circuit
        .memory_caps
        .as_ref()
        .expect("warm memory commitment");
    let memory_host =
        if crate::memory_policy::persists_memory_partial_trees(circuit.circuit, circuit.profile) {
            GpuGKRMemoryTransferHost::from_per_coset_caps_and_partial_trees(
                memory_caps,
                memory_partial_trees_geometry(
                    programs.compiled_circuit(),
                    config,
                    CommitmentMode::MergedMemoryAndWitness,
                    memory_reduction_layers,
                ),
                circuit
                    .memory_partial_trees
                    .as_ref()
                    .expect("proof inputs require the partial trees persisted by the commitment"),
            )
        } else {
            assert!(
                circuit.memory_partial_trees.is_none(),
                "{:?}/{:?} proof inputs do not take memory partial trees",
                circuit.circuit,
                circuit.profile
            );
            GpuGKRMemoryTransferHost::from_per_coset_caps_for_geometry(
                memory_caps,
                resolved.geometry(),
            )
        };
    let mut memory_host = memory_host;
    memory_host.bind_base_commitment_geometry(resolved.geometry());
    let memory = GpuGKRMemoryTransfer::new(Arc::new(memory_host), context)?;
    let num_teardown_sets = programs
        .compiled_circuit()
        .memory_layout
        .teardown_sets
        .len();
    let top_bits = circuit
        .inputs
        .inits_and_teardowns
        .as_ref()
        .map(|host| host.top_bits.clone())
        .unwrap_or_else(|| vec![0; num_teardown_sets]);
    assert_eq!(top_bits.len(), num_teardown_sets);
    let mut inputs = GpuGKRProofTransfer::new(
        setup,
        decoder,
        inits,
        trace,
        memory,
        &top_bits,
        stable_external_challenges(),
        context,
    )?;
    if let Err(error) = inputs.schedule(context) {
        // Partial scheduling can leave H2D callbacks using this bundle.
        drain(context)?;
        return Err(error);
    }
    Ok((inputs, plan))
}

/// Measure production input allocations outside timed proof ranges.
pub(super) fn input_footprint(
    device_id: i32,
    context: &ProverContext,
    circuit: &PreparedCircuit,
) -> CudaResult<usize> {
    let before = context.get_used_mem_current();
    let inputs = schedule_proof_inputs(device_id, context, circuit, None, None);
    drain(context)?;
    let inputs = inputs?;
    let bytes = context.get_used_mem_current() - before;
    drop(inputs);
    Ok(bytes)
}

pub(super) struct Sample {
    pub elapsed_ms: f32,
    pub fingerprint: u64,
}

pub(super) fn run_case(
    device_id: i32,
    context: &mut ProverContext,
    target: &PreparedCircuit,
    target_override: Option<ProofMemoryPolicy>,
    follower: &PreparedCircuit,
    direction: AllocationDirection,
) -> CudaResult<(Sample, ProofMemoryPolicy)> {
    let follower_direction = match direction {
        AllocationDirection::Ascending => AllocationDirection::Descending,
        AllocationDirection::Descending => AllocationDirection::Ascending,
    };
    let policy = target_override.unwrap_or_else(|| {
        crate::memory_policy::policy(target.circuit, target.profile, context.get_mem_size())
    });
    // On pool OOM, queued operations must finish before freed arena ranges can
    // be reused. The runner retains PreparedCircuit host inputs throughout.
    context.set_allocation_mode(AllocationMode::Inputs(direction));
    let (inputs, plan) = match schedule_proof_inputs(device_id, context, target, Some(policy), None)
    {
        Ok(inputs) => inputs,
        Err(error) => {
            drain(context)?;
            return Err(error);
        }
    };
    // Target H2D must complete before a prove error can release its pinned
    // sources. Follower H2D still overlaps the proof.
    context.get_h2d_stream().synchronize()?;
    context.set_allocation_mode(AllocationMode::Inputs(follower_direction));
    let follower = schedule_proof_inputs(device_id, context, follower, None, None);
    context.set_allocation_mode(AllocationMode::Proof(direction));
    let result = match &follower {
        Ok(_) => {
            let config = target
                .precomputations
                .baby_bear()
                .resolved_config(target.profile)
                .config();
            prove::<A>(
                &target.precomputations.baby_bear().gkr_programs,
                config,
                FINAL_TRACE_SIZE_LOG_2,
                inputs,
                &plan,
                policy,
                crate::memory_policy::partial_trees(target.circuit, target.profile),
                context,
            )
            .and_then(|job| job.finish())
        }
        Err(error) => {
            drain(context)?;
            drop(inputs);
            Err(*error)
        }
    };
    // The follower is not proved: target.finish() alone does not join its H2D.
    drain(context)?;
    drop(follower);
    result.map(|(proof, elapsed_ms)| {
        (
            Sample {
                elapsed_ms,
                fingerprint: fingerprint(&proof),
            },
            policy,
        )
    })
}

fn fingerprint(proof: &GKRProof<BF, E4, DefaultTreeConstructor>) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    serde_json::to_vec(proof)
        .expect("serializable proof")
        .hash(&mut hasher);
    hasher.finish()
}
