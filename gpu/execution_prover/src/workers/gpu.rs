use crate::precomputations::CircuitPrecomputations;
use crate::workers::gpu_manager::{GpuWorkRequest, GpuWorkResult};
use crate::A;
use crossbeam_channel::{Receiver, Sender};
use era_cudart::device::{get_device_properties, set_device};
use era_cudart::result::CudaResult;
use execution_prover::messages::{
    L1WrapProofRequest, L1WrapProofResult, MemoryCommitmentRequest, MemoryCommitmentResult,
    ProofRequest, ProofResult, SetupInitializationRequest, SetupInitializationResult,
};
use execution_prover::ProofProfile;
use gpu_circuit_prover::l1_wrap::{GpuL1WrapProofJob, L1WrapInputs};
use gpu_circuit_prover::proof::merged_commitment::{
    commit_merged_from_transfers, GpuGKRMergedCommitTransfer,
};
use gpu_circuit_prover::proof::{
    admit_dr_tail_before_transfers, DrTailPreflightRequest, GpuGKRProofJob,
};
use gpu_core::allocator::tracker::AllocationDirection::{self, Ascending, Descending};
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr::proth120::backward::{preflight_dr_tail_resources_pr, DrTailProofPlanPr};
use gpu_gkr::setup::GpuGKRSetupTransfer;
use gpu_prover_context::{AllocationMode, ProverContext, ProverContextConfig};
use gpu_trace::trace::decoder::DecoderTableTransfer;
use gpu_trace::trace::memory::{commit_memory_from_transfers, MemoryCommitmentJob};
use gpu_trace::trace::memory_transfer::{GpuGKRMemoryTransfer, GpuGKRMemoryTransferHost};
use gpu_trace::trace::tracing_data::{
    InitsAndTeardownsTransfer, TracingDataHost, TracingDataTransfer, UnrolledTracingDataHost,
};
use gpu_trace::witness::circuit_type::CircuitType;
use gpu_trace::witness::trace_unrolled::InitsAndTeardownsTraceHost;
use log::{debug, error, info, trace};

use crate::upstream::{
    CommitmentMode, GKRExternalChallenges, MerkleTreeCapVarLength, SecurityLevel,
};
use std::ffi::CStr;
use std::mem;
use std::process::exit;
use std::sync::Arc;

pub(crate) fn get_gpu_worker_func(
    device_id: i32,
    prover_context_config: ProverContextConfig,
    is_initialized: Sender<()>,
    requests: Receiver<Option<GpuWorkRequest<A>>>,
    results: Sender<Option<GpuWorkResult<A>>>,
) -> impl FnOnce() + Send + 'static {
    move || {
        let result = gpu_worker(
            device_id,
            prover_context_config,
            is_initialized,
            requests,
            results,
        );
        if let Err(e) = result {
            error!("GPU_WORKER[{device_id}] worker encountered an error: {e}");
            exit(1);
        }
    }
}

const FINAL_TRACE_SIZE_LOG_2: u32 = 4;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RequestKind {
    L1WrapProof,
    MemoryCommitment,
    Proof,
    SetupInitialization,
}

/// Per-request bookkeeping carried across all three phases. Owns the
/// precomputations Arc (which holds the compiled circuit, lazy-init setup
/// host, and optional decoder host), so it outlives any Phase-2 borrow,
/// and the original host data the orchestrator expects back on the
/// memory-commit path.
struct RequestState {
    batch_id: u64,
    circuit_type: CircuitType,
    sequence_id: usize,
    precomputations: CircuitPrecomputations,
    kind: RequestKind,
    /// Set only for Proof requests; consumed in Phase 2 by `prove()`.
    external_challenges: Option<GKRExternalChallenges<BF, E4>>,
    /// Per-coset caps from a prior commit_memory phase; only present for
    /// Proof requests and consumed in Phase 1 to build the memory transfer.
    memory_caps: Option<Vec<MerkleTreeCapVarLength>>,
    /// Original host witnesses returned to the orchestrator after the GPU work
    /// completes so their allocators return to the pool.
    inits_and_teardowns_result: Option<InitsAndTeardownsTraceHost<A>>,
    tracing_data_result: Option<gpu_trace::trace::tracing_data::TracingDataHost<A>>,
    security_level: SecurityLevel,
    commitment_mode: CommitmentMode,
    profile: ProofProfile,
    device_peak_bytes: Option<usize>,
    direction: Option<AllocationDirection>,
    /// The request whose phase one was staged while this request's phase two
    /// was enqueued: its inputs stay resident in the arena during this proof.
    follower: Option<RequestIdentity>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct RequestIdentity {
    circuit_type: CircuitType,
    profile: ProofProfile,
    kind: RequestKind,
}

impl RequestState {
    fn identity(&self) -> RequestIdentity {
        RequestIdentity {
            circuit_type: self.circuit_type,
            profile: self.profile,
            kind: self.kind,
        }
    }
}

fn follower_label(follower: Option<RequestIdentity>) -> String {
    match follower {
        Some(RequestIdentity {
            circuit_type,
            profile,
            kind,
        }) => format!("{circuit_type:?}/{profile:?}/{kind:?}"),
        None => "none".to_string(),
    }
}

/// Phase-1 state: H2D transfers scheduled, no GPU job enqueued yet.
struct PhaseOne<'a> {
    state: RequestState,
    inputs: PhaseOneInputs<'a>,
}

/// Per-phase-1 bundle, scheduled on h2d_stream against a single shared
/// `Transfer`. Variant matches the eventual phase-2 job type.
// Short-lived per-request state moved through the worker's hot dispatch
// loop (one instance per in-flight request, swapped every iteration), not a
// long-lived collection; boxing `Proof` would add a heap alloc per request
// for no steady-state benefit.
#[allow(clippy::large_enum_variant)]
enum PhaseOneInputs<'a> {
    Proof(
        gpu_circuit_prover::proof::inputs::GpuGKRProofTransfer<'a, A>,
        gpu_gkr::DrTailProofPlan,
    ),
    MemoryCommitment(gpu_trace::trace::memory_transfer::GpuGKRCommitMemoryTransfer<'a, A>),
    MergedCommitment(GpuGKRMergedCommitTransfer<'a, A>),
    L1Wrap(L1WrapInputs<'a, A>, DrTailProofPlanPr),
    SetupInitialization,
}

/// Phase-2 state: GPU job enqueued, awaiting `finish()`.
struct PhaseTwo<'a> {
    state: RequestState,
    job: JobType<'a>,
}

// Same rationale as `PhaseOneInputs` above: one instance per in-flight
// request, swapped through the worker's hot dispatch loop, so boxing `Proof`
// would add a per-request heap alloc rather than shrink a steady-state
// collection.
#[allow(clippy::large_enum_variant)]
enum JobType<'a> {
    MemoryCommitment(MemoryCommitmentJob<'a>),
    Proof(GpuGKRProofJob<'a>),
    L1Wrap(GpuL1WrapProofJob<'a>),
    SetupInitialization,
}

fn gpu_worker(
    device_id: i32,
    prover_context_config: ProverContextConfig,
    is_initialized: Sender<()>,
    requests: Receiver<Option<GpuWorkRequest<A>>>,
    results: Sender<Option<GpuWorkResult<A>>>,
) -> CudaResult<()> {
    trace!("GPU_WORKER[{device_id}] started");
    set_device(device_id)?;
    let props = get_device_properties(device_id)?;
    let name = unsafe { CStr::from_ptr(props.name.as_ptr()).to_string_lossy() };
    info!(
        "GPU_WORKER[{device_id}] GPU: {} ({} SMs, {:.3} GB RAM)",
        name,
        props.multiProcessorCount,
        props.totalGlobalMem as f64 / 1024.0 / 1024.0 / 1024.0
    );
    let mut context = ProverContext::new_with_auto_arena_size(
        &prover_context_config,
        crate::memory_policy::select_auto_arena_bytes,
    )?;
    crate::memory_policy::select_arena_bytes(context.get_mem_size());
    info!(
        "GPU_WORKER[{device_id}] initialized the GPU memory allocator with {:.3} GB ({} B) of usable memory",
        context.get_mem_size() as f64 / 1024.0 / 1024.0 / 1024.0,
        context.get_mem_size()
    );
    is_initialized
        .send(())
        .expect("GPU worker initialization channel closed before readiness signal");
    drop(is_initialized);
    let mut even_odd_index = 0;
    let mut current_phase_one: Option<PhaseOne> = None;
    let mut current_phase_two: Option<PhaseTwo> = None;
    for request in requests {
        let mut phase_one = if let Some(request) = request {
            context.set_allocation_mode(match request {
                GpuWorkRequest::SetupInitialization(_) => AllocationMode::Unbounded,
                _ => AllocationMode::Inputs([Ascending, Descending][even_odd_index]),
            });
            Some(schedule_phase_one(device_id, &context, request)?)
        } else {
            None
        };
        mem::swap(&mut current_phase_one, &mut phase_one);
        let direction = [Descending, Ascending][even_odd_index];
        context.set_allocation_mode(AllocationMode::Proof(direction));
        let follower = current_phase_one.as_ref().map(|p1| p1.state.identity());
        let mut phase_two = if let Some(p1) = phase_one {
            Some(enqueue_phase_two(
                device_id, &context, p1, direction, follower,
            )?)
        } else {
            None
        };
        mem::swap(&mut current_phase_two, &mut phase_two);
        even_odd_index = 1 - even_odd_index;
        let result = if let Some(p2) = phase_two {
            Some(finish_phase_three(device_id, p2)?)
        } else {
            None
        };
        results
            .send(result)
            .expect("GPU worker results channel closed before queued work completed")
    }
    assert!(current_phase_one.is_none());
    assert!(current_phase_two.is_none());
    trace!("GPU_WORKER[{device_id}] finished");
    Ok(())
}

fn schedule_phase_one<'a>(
    device_id: i32,
    context: &ProverContext,
    request: GpuWorkRequest<A>,
) -> CudaResult<PhaseOne<'a>> {
    if let GpuWorkRequest::SetupInitialization(request) = request {
        let SetupInitializationRequest {
            batch_id,
            circuit_type,
            sequence_id,
            precomputations,
            security_level,
        } = request;
        trace!(
            "BATCH[{batch_id}] GPU_WORKER[{device_id}] initializing setup for circuit {circuit_type:?}[{sequence_id}]"
        );
        let timer = std::time::Instant::now();
        match &precomputations {
            CircuitPrecomputations::BabyBear(precomputations) => {
                precomputations.setup_host.get_or_init(context)?
            }
            CircuitPrecomputations::L1Wrap(precomputed) => {
                precomputed.initialize(security_level, context)?
            }
        }
        debug!(
            "BATCH[{batch_id}] GPU_WORKER[{device_id}] initialized setup for circuit {circuit_type:?}[{sequence_id}] in {:.3} ms",
            timer.elapsed().as_secs_f64() * 1e3
        );
        let state = RequestState {
            batch_id,
            circuit_type,
            sequence_id,
            precomputations,
            kind: RequestKind::SetupInitialization,
            external_challenges: None,
            memory_caps: None,
            inits_and_teardowns_result: None,
            tracing_data_result: None,
            security_level,
            commitment_mode: CommitmentMode::SeparateMemoryAndWitness,
            profile: if circuit_type == CircuitType::L1Wrap21 {
                ProofProfile::L1Wrap
            } else {
                ProofProfile::Standard
            },
            device_peak_bytes: None,
            direction: None,
            follower: None,
        };
        return Ok(PhaseOne {
            state,
            inputs: PhaseOneInputs::SetupInitialization,
        });
    }
    if let GpuWorkRequest::L1WrapProof(request) = request {
        return schedule_l1_wrap_phase_one(device_id, context, request);
    }
    // Decompose the request into bookkeeping plus the host buffers that
    // become Phase 1 H2D inputs.
    let (state, inits_and_teardowns_host, tracing_data_host) = match request {
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
                security_level,
                commitment_mode,
                profile,
            } = req;
            if profile == ProofProfile::L1Feeder {
                crate::memory_policy::admit_l1_feeder(context.get_mem_size());
            }
            let state = RequestState {
                batch_id,
                circuit_type,
                sequence_id,
                precomputations,
                kind: RequestKind::MemoryCommitment,
                external_challenges: None,
                memory_caps: None,
                inits_and_teardowns_result: inits_and_teardowns.clone(),
                tracing_data_result: tracing_data.clone(),
                security_level,
                commitment_mode,
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
                security_level,
                commitment_mode,
                profile,
            } = req;
            if profile == ProofProfile::L1Feeder {
                crate::memory_policy::admit_l1_feeder(context.get_mem_size());
            }
            let state = RequestState {
                batch_id,
                circuit_type,
                sequence_id,
                precomputations,
                kind: RequestKind::Proof,
                external_challenges: Some(external_challenges),
                memory_caps: Some(memory_caps),
                inits_and_teardowns_result: inits_and_teardowns.clone(),
                tracing_data_result: tracing_data.clone(),
                security_level,
                commitment_mode,
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

    let proof_prover_config = is_proof.then(|| {
        gpu_circuit_prover::config::prover_config(circuit_type, state.profile, state.security_level)
            .expect("ExecutionProverConfiguration validated GPU security level before GPU work")
    });
    let preflight_request =
        proof_prover_config
            .as_ref()
            .map(|prover_config| DrTailPreflightRequest {
                gkr_programs: &state.precomputations.baby_bear().gkr_programs,
                prover_config,
                final_trace_size_log_2: FINAL_TRACE_SIZE_LOG_2,
                device_id,
            });

    let inputs = admit_dr_tail_before_transfers(
        preflight_request,
        |dr_tail_plan| -> CudaResult<PhaseOneInputs<'a>> {
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
                let setup_transfer = if let Some(setup_host) = state
                    .precomputations
                    .baby_bear()
                    .setup_host
                    .get_initialized(state.profile)
                {
                    Some(GpuGKRSetupTransfer::new(
                        setup_host,
                        crate::memory_policy::partial_trees(circuit_type, state.profile).setup,
                        context,
                    )?)
                } else {
                    None
                };
                // Geometry must match the configuration used to commit the caps.
                // `circuit_type.get_lde_factor()` / `get_tree_cap_size()` are derived
                // from `OPTIMAL_FOLDING_PROPERTIES` and can disagree with the
                // `prover_config` the commit phase actually used, so use the
                // prover_config geometry directly here.
                let prover_config = proof_prover_config
                    .as_ref()
                    .expect("proof requests construct their prover config before transfers");
                let log_lde_factor = prover_config.lde_factor.trailing_zeros();
                let log_tree_cap_size = prover_config.cap_size.trailing_zeros();
                let memory_caps = state
                    .memory_caps
                    .as_ref()
                    .expect("Proof requires memory_caps");
                let memory_host = GpuGKRMemoryTransferHost::from_per_coset_caps(
                    memory_caps,
                    log_lde_factor,
                    log_tree_cap_size,
                )?;
                let memory_transfer = GpuGKRMemoryTransfer::new(Arc::new(memory_host), context)?;
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
                let mut bundle =
                    gpu_circuit_prover::proof::inputs::GpuGKRProofTransfer::<'_, A>::new(
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
                PhaseOneInputs::Proof(
                    bundle,
                    dr_tail_plan.expect("proof preflight must return a DR-tail plan"),
                )
            } else if matches!(
                state.commitment_mode,
                CommitmentMode::MergedAndPackedMemoryAndWitness { .. }
            ) {
                panic!(
                    "the GPU prover does not support CommitmentMode::MergedAndPackedMemoryAndWitness"
                )
            } else if state.commitment_mode == CommitmentMode::MergedMemoryAndWitness {
                let setup_host = state
                    .precomputations
                    .baby_bear()
                    .setup_host
                    .get_initialized(state.profile)
                    .expect("merged memory+witness commitment requires the initialized setup");
                let mut bundle = GpuGKRMergedCommitTransfer::<'_, A>::new(
                    GpuGKRSetupTransfer::new(
                        setup_host,
                        crate::memory_policy::partial_trees(circuit_type, state.profile).setup,
                        context,
                    )?,
                    decoder_transfer,
                    inits_and_teardowns_transfer,
                    tracing_data_transfer,
                    context,
                )?;
                trace!(
            "BATCH[{batch_id}] GPU_WORKER[{device_id}] scheduling commit-merged H2D bundle for circuit {circuit_type:?}[{sequence_id}]"
        );
                bundle.schedule(context)?;
                PhaseOneInputs::MergedCommitment(bundle)
            } else {
                let mut bundle =
                    gpu_trace::trace::memory_transfer::GpuGKRCommitMemoryTransfer::<'_, A>::new(
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
            Ok(inputs)
        },
    )??;

    Ok(PhaseOne { state, inputs })
}

fn schedule_l1_wrap_phase_one<'a>(
    device_id: i32,
    context: &ProverContext,
    request: L1WrapProofRequest<A, CircuitPrecomputations>,
) -> CudaResult<PhaseOne<'a>> {
    let L1WrapProofRequest {
        batch_id,
        circuit_type,
        precomputations,
        inits_and_teardowns,
        tracing_data,
        commitment_mode,
    } = request;
    assert_eq!(
        circuit_type,
        CircuitType::L1Wrap21,
        "the GPU backend proves only the 2^21 L1 wrap (CircuitType::L1Wrap21)"
    );
    crate::memory_policy::admit_l1_wrap(context.get_mem_size());
    let precomputed = Arc::clone(precomputations.l1_wrap());
    let state = RequestState {
        batch_id,
        circuit_type,
        sequence_id: 0,
        precomputations,
        kind: RequestKind::L1WrapProof,
        external_challenges: None,
        memory_caps: None,
        inits_and_teardowns_result: Some(inits_and_teardowns.clone()),
        tracing_data_result: Some(TracingDataHost::Unrolled(UnrolledTracingDataHost::Unified(
            tracing_data.clone(),
        ))),
        security_level: precomputed.security,
        commitment_mode,
        profile: ProofProfile::L1Wrap,
        device_peak_bytes: None,
        direction: None,
        follower: None,
    };
    let dr_tail_plan =
        preflight_dr_tail_resources_pr(&precomputed.programs, FINAL_TRACE_SIZE_LOG_2, context);
    let mut inputs = L1WrapInputs::new(
        &precomputed.geometry,
        precomputed.decoder_host.clone(),
        inits_and_teardowns,
        tracing_data,
        precomputed.host(),
        context,
    )?;
    trace!("BATCH[{batch_id}] GPU_WORKER[{device_id}] scheduling L1 wrap H2D bundle");
    inputs.schedule(context)?;
    Ok(PhaseOne {
        state,
        inputs: PhaseOneInputs::L1Wrap(inputs, dr_tail_plan),
    })
}

fn enqueue_phase_two<'a>(
    device_id: i32,
    context: &ProverContext,
    p1: PhaseOne<'a>,
    direction: AllocationDirection,
    follower: Option<RequestIdentity>,
) -> CudaResult<PhaseTwo<'a>> {
    let PhaseOne { mut state, inputs } = p1;
    state.follower = follower;
    if let PhaseOneInputs::SetupInitialization = inputs {
        return Ok(PhaseTwo {
            state,
            job: JobType::SetupInitialization,
        });
    }
    if let PhaseOneInputs::L1Wrap(inputs, dr_tail_plan) = inputs {
        let precomputed = Arc::clone(state.precomputations.l1_wrap());
        trace!(
            "BATCH[{}] GPU_WORKER[{device_id}] producing L1 wrap proof",
            state.batch_id
        );
        state.direction = Some(direction);
        context.reset_used_mem_peak();
        let job = gpu_circuit_prover::l1_wrap::prove::<A>(
            &precomputed.programs,
            &precomputed.circuit,
            &precomputed.geometry,
            &precomputed.config,
            state.commitment_mode,
            inputs,
            &dr_tail_plan,
            crate::memory_policy::policy(
                state.circuit_type,
                ProofProfile::L1Wrap,
                context.get_mem_size(),
            ),
            crate::memory_policy::partial_trees(state.circuit_type, ProofProfile::L1Wrap),
            context,
        )?;
        state.device_peak_bytes = Some(context.get_used_mem_peak());
        return Ok(PhaseTwo {
            state,
            job: JobType::L1Wrap(job),
        });
    }
    let batch_id = state.batch_id;
    let circuit_type = state.circuit_type;
    let sequence_id = state.sequence_id;
    let prover_config = gpu_circuit_prover::config::prover_config(
        circuit_type,
        state.profile,
        state.security_level,
    )
    .expect("ExecutionProverConfiguration validated GPU security level before GPU work");
    let final_trace_size_log_2 = FINAL_TRACE_SIZE_LOG_2;
    let compiled_circuit_arc = Arc::clone(
        state
            .precomputations
            .baby_bear()
            .gkr_programs
            .compiled_circuit(),
    );

    state.direction = Some(direction);
    let job = match inputs {
        PhaseOneInputs::Proof(bundle, dr_tail_plan) => {
            trace!(
                "BATCH[{batch_id}] GPU_WORKER[{device_id}] producing proof for circuit {circuit_type:?}[{sequence_id}]"
            );
            context.reset_used_mem_peak();
            let job = gpu_circuit_prover::proof::prove::<A>(
                &state.precomputations.baby_bear().gkr_programs,
                &prover_config,
                state.commitment_mode,
                final_trace_size_log_2,
                bundle,
                &dr_tail_plan,
                crate::memory_policy::policy(circuit_type, state.profile, context.get_mem_size()),
                crate::memory_policy::partial_trees(circuit_type, state.profile),
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
            let job = commit_memory_from_transfers::<A>(
                circuit_type,
                &compiled_circuit_arc,
                bundle,
                &prover_config,
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
                &prover_config,
                bundle,
                crate::memory_policy::merged_commit_strategy(circuit_type, state.profile),
                crate::memory_policy::partial_trees(circuit_type, state.profile),
                context,
            )?;
            state.device_peak_bytes = Some(context.get_used_mem_peak());
            JobType::MemoryCommitment(job)
        }
        PhaseOneInputs::L1Wrap(..) => unreachable!("L1Wrap proofs return early above"),
        PhaseOneInputs::SetupInitialization => {
            unreachable!("setup initialization returns early above")
        }
    };

    Ok(PhaseTwo { state, job })
}

fn finish_phase_three<'a>(device_id: i32, p2: PhaseTwo<'a>) -> CudaResult<GpuWorkResult<A>> {
    let PhaseTwo { state, job } = p2;
    #[cfg(test)]
    tests::observe(&state);
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
    match job {
        JobType::MemoryCommitment(job) => {
            let (merkle_tree_caps, commitment_time_ms) = job.finish()?;
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
            }))
        }
        JobType::Proof(job) => {
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
        JobType::L1Wrap(job) => {
            let result = job.finish()?;
            let bytes = device_peak_bytes.expect("L1 wrap proof device peak was recorded");
            let direction = direction.expect("L1 wrap proof allocation direction was recorded");
            debug!(
                "BATCH[{batch_id}] GPU_WORKER[{device_id}] produced L1 wrap proof for circuit {circuit_type:?}[{sequence_id}] profile {profile:?} direction {direction:?} follower {follower} device peak {bytes} B"
            );
            let inits_and_teardowns =
                inits_and_teardowns_result.expect("L1 wrap proof returns its inits and teardowns");
            let Some(TracingDataHost::Unrolled(UnrolledTracingDataHost::Unified(tracing_data))) =
                tracing_data_result
            else {
                panic!("L1 wrap proof returns its unified tracing data")
            };
            Ok(GpuWorkResult::L1WrapProof(L1WrapProofResult {
                batch_id,
                circuit_type,
                inits_and_teardowns,
                tracing_data,
                result,
            }))
        }
        JobType::SetupInitialization => {
            trace!(
                "BATCH[{batch_id}] GPU_WORKER[{device_id}] initialized setup for circuit {circuit_type:?}[{sequence_id}]"
            );
            Ok(GpuWorkResult::SetupInitialization(
                SetupInitializationResult {
                    batch_id,
                    circuit_type,
                    sequence_id,
                },
            ))
        }
    }
}

#[cfg(test)]
mod tests;
