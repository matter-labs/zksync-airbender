use super::factory::{stable_external_challenges, PreparedCircuit};
use crate::upstream::{DefaultTreeConstructor, GKRProof, MerkleTreeCapVarLength};
use crate::A;
use era_cudart::result::CudaResult;
use gpu_circuit_prover::config::prover_config;
use gpu_circuit_prover::proof::inputs::GpuGKRProofTransfer;
use gpu_circuit_prover::proof::memory_policy::ProofMemoryPolicy;
use gpu_circuit_prover::proof::{admit_dr_tail_before_transfers, prove, DrTailPreflightRequest};
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr::setup::GpuGKRSetupTransfer;
use gpu_gkr::DrTailProofPlan;
use gpu_prover_context::{AllocationMode, AllocationSide, ProverContext};
use gpu_trace::trace::decoder::DecoderTableTransfer;
use gpu_trace::trace::memory::commit_memory_from_transfers;
use gpu_trace::trace::memory_transfer::{
    GpuGKRCommitMemoryTransfer, GpuGKRMemoryTransfer, GpuGKRMemoryTransferHost,
};
use gpu_trace::trace::tracing_data::{
    inits_and_teardowns_capacity_pages, InitsAndTeardownsReservation, InitsAndTeardownsTransfer,
    TracingDataTransfer,
};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

const FINAL_TRACE_SIZE_LOG_2: u32 = 4;

pub(super) fn drain(context: &ProverContext) -> CudaResult<()> {
    context.get_h2d_stream().synchronize()?;
    context.get_exec_stream().synchronize()?;
    context.get_side_stream().synchronize()
}

type InputTransfers<'a> = (
    Option<DecoderTableTransfer<'a>>,
    Option<InitsAndTeardownsTransfer<'a, A>>,
    Option<InitsAndTeardownsReservation>,
    Option<TracingDataTransfer<'a, A>>,
);

fn input_transfers<'a>(
    context: &ProverContext,
    circuit: &PreparedCircuit,
) -> CudaResult<InputTransfers<'a>> {
    // Match production's allocation order so fragmentation is represented.
    let decoder = circuit
        .precomputations
        .decoder_host
        .as_ref()
        .map(|host| DecoderTableTransfer::new(Arc::clone(host), context))
        .transpose()?;
    let num_teardown_sets = circuit
        .precomputations
        .gkr_programs
        .compiled_circuit()
        .memory_layout
        .teardown_sets
        .len();
    let capacity_pages = inits_and_teardowns_capacity_pages(
        num_teardown_sets,
        circuit.circuit.get_domain_size_log2(),
    );
    let reservation = (circuit.inputs.inits_and_teardowns.is_none() && num_teardown_sets > 0)
        .then(|| InitsAndTeardownsReservation::new(capacity_pages, context))
        .transpose()?;
    let inits = circuit
        .inputs
        .inits_and_teardowns
        .clone()
        .map(|host| InitsAndTeardownsTransfer::new(host, capacity_pages, context))
        .transpose()?;
    let trace = circuit
        .inputs
        .tracing_data
        .clone()
        .map(|host| TracingDataTransfer::new(host, circuit.circuit.get_domain_size(), context))
        .transpose()?;
    Ok((decoder, inits, reservation, trace))
}

pub(super) fn commit_memory(
    context: &ProverContext,
    circuit: &PreparedCircuit,
) -> CudaResult<Vec<MerkleTreeCapVarLength>> {
    let result = (|| {
        let config = prover_config(circuit.circuit, circuit.security_level).unwrap();
        let (decoder, inits, reservation, trace) = input_transfers(context, circuit)?;
        let mut inputs = GpuGKRCommitMemoryTransfer::new(decoder, inits, trace, context)?;
        if let Some(reservation) = reservation {
            inputs.hold_inits_and_teardowns_reservation(reservation);
        }
        if let Err(error) = inputs.schedule(context) {
            drain(context)?;
            return Err(error);
        }
        let job = commit_memory_from_transfers::<A>(
            circuit.circuit,
            circuit.precomputations.gkr_programs.compiled_circuit(),
            inputs,
            &config,
            context,
        )?;
        job.finish().map(|(caps, _)| caps)
    })();
    drain(context)?;
    result
}

fn schedule_proof_inputs<'a>(
    device_id: i32,
    context: &ProverContext,
    circuit: &PreparedCircuit,
) -> CudaResult<(GpuGKRProofTransfer<'a, A>, DrTailProofPlan)> {
    let config = prover_config(circuit.circuit, circuit.security_level).unwrap();
    let programs = &circuit.precomputations.gkr_programs;
    let plan = admit_dr_tail_before_transfers(
        Some(DrTailPreflightRequest {
            gkr_programs: programs,
            prover_config: &config,
            final_trace_size_log_2: FINAL_TRACE_SIZE_LOG_2,
            device_id,
        }),
        |plan| plan.unwrap(),
    )?;
    let (decoder, inits, reservation, trace) = input_transfers(context, circuit)?;
    let setup = circuit
        .precomputations
        .setup_host
        .get_initialized()
        .map(|host| GpuGKRSetupTransfer::new(host, context))
        .transpose()?;
    let memory_host = GpuGKRMemoryTransferHost::from_per_coset_caps(
        circuit
            .memory_caps
            .as_ref()
            .expect("warm memory commitment"),
        config.lde_factor.trailing_zeros(),
        config.cap_size.trailing_zeros(),
    )?;
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
    if let Some(reservation) = reservation {
        inputs.hold_inits_and_teardowns_reservation(reservation);
    }
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
    let inputs = schedule_proof_inputs(device_id, context, circuit);
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
) -> CudaResult<(Sample, ProofMemoryPolicy)> {
    let policy = target_override
        .unwrap_or_else(|| crate::memory_policy::policy(target.circuit, context.get_mem_size()));
    // On pool OOM, queued operations must finish before freed arena ranges can
    // be reused. The runner retains PreparedCircuit host inputs throughout.
    context.set_allocation_mode(AllocationMode::Proof(AllocationSide::Low));
    let (inputs, plan) = match schedule_proof_inputs(device_id, context, target) {
        Ok(inputs) => inputs,
        Err(error) => {
            drain(context)?;
            return Err(error);
        }
    };
    // Target H2D must complete before a prove error can release its pinned
    // sources. Follower H2D still overlaps the proof.
    context.get_h2d_stream().synchronize()?;
    context.set_allocation_mode(AllocationMode::Proof(AllocationSide::High));
    let follower = schedule_proof_inputs(device_id, context, follower);
    context.set_allocation_mode(AllocationMode::Proof(AllocationSide::Low));
    let result = match &follower {
        Ok(_) => {
            let config = prover_config(target.circuit, target.security_level).unwrap();
            prove::<A>(
                &target.precomputations.gkr_programs,
                &config,
                FINAL_TRACE_SIZE_LOG_2,
                inputs,
                &plan,
                policy,
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
