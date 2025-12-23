use super::A;
use crate::circuit_type::CircuitType;
use crate::cudart::device::set_device;
use crate::cudart::result::CudaResult;
use crate::execution::messages::{
    GpuWorkRequest, GpuWorkResult, MemoryCommitmentRequest, MemoryCommitmentResult, ProofRequest,
    ProofResult,
};
use crate::prover::context::{ProverContext, ProverContextConfig};
use crate::prover::decoder::DecoderTableTransfer;
use crate::prover::memory::{commit_memory, MemoryCommitmentJob};
use crate::prover::precomputations::Precomputations;
use crate::prover::proof::{prove, ProofJob};
use crate::prover::setup::SetupPrecomputations;
use crate::prover::trace_holder::TreesCacheMode;
use crate::prover::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};
use crate::witness::trace_unrolled::get_aux_arguments_boundary_values;
use crossbeam_channel::{Receiver, Sender};
use era_cudart::device::get_device_properties;
use log::{debug, error, info, trace};
use prover::definitions::AuxArgumentsBoundaryValues;
use std::ffi::CStr;
use std::mem;
use std::ops::Deref;
use std::process::exit;
use verifier_common::num_queries_for_security_params;

pub fn get_gpu_worker_func(
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

enum JobType<'a> {
    MemoryCommitment(MemoryCommitmentJob<'a>),
    Proof(ProofJob<'a>),
}

fn get_trees_cache_mode(_circuit_type: CircuitType, _context: &ProverContext) -> TreesCacheMode {
    // match circuit_type {
    //     CircuitType::Main(main) => match main {
    //         MainCircuitType::ReducedRiscVLog23Machine if (context.get_mem_size() >> 30) < 28 => {
    //             TreesCacheMode::CacheNone
    //         } // less than 28GB
    //         _ => TreesCacheMode::CacheFull,
    //     },
    //     _ => TreesCacheMode::CacheFull,
    // }
    TreesCacheMode::CachePatrial
}

fn gpu_worker(
    device_id: i32,
    prover_context_config: ProverContextConfig,
    is_initialized: Sender<()>,
    requests: Receiver<Option<GpuWorkRequest<A>>>,
    results: Sender<Option<GpuWorkResult<A>>>,
) -> CudaResult<()> {
    trace!("GPU_WORKER[{device_id}] started");
    Precomputations::ensure_initialized();
    set_device(device_id)?;
    let props = get_device_properties(device_id)?;
    let name = unsafe { CStr::from_ptr(props.name.as_ptr()).to_string_lossy() };
    info!(
        "GPU_WORKER[{device_id}] GPU: {} ({} SMs, {:.3} GB RAM)",
        name,
        props.multiProcessorCount,
        props.totalGlobalMem as f64 / 1024.0 / 1024.0 / 1024.0
    );
    let mut context = ProverContext::new(&prover_context_config)?;
    info!(
        "GPU_WORKER[{device_id}] initialized the GPU memory allocator with {:.3} GB of usable memory",
        context.get_mem_size() as f64 / 1024.0 / 1024.0 / 1024.0
    );
    is_initialized.send(()).unwrap();
    drop(is_initialized);
    let mut even_odd_index = 0;
    let mut current_phase_one = None;
    let mut current_phase_two = None;
    for request in requests {
        context.set_reversed_allocation_placement(even_odd_index == 1);
        let mut phase_one = if let Some(request) = request {
            let batch_id = request.batch_id();
            let circuit_type = request.circuit_type();
            let sequence_id = request.sequence_id();
            let precomputations = &request.precomputations();
            let setup = match &request {
                GpuWorkRequest::MemoryCommitment(_) => None,
                GpuWorkRequest::Proof(_) => {
                    let lde_factor = circuit_type.get_lde_factor();
                    assert!(lde_factor.is_power_of_two());
                    let log_lde_factor = lde_factor.trailing_zeros();
                    let tree_cap_size = circuit_type.get_tree_cap_size();
                    assert!(tree_cap_size.is_power_of_two());
                    let log_tree_cap_size = tree_cap_size.trailing_zeros();
                    let circuit = &precomputations.compiled_circuit;
                    let trace = &precomputations.setup_trace;
                    let setup_trees_and_caps = precomputations
                        .setup_trees_and_caps
                        .get_or_try_init(|| {
                            trace!("GPU_WORKER[{device_id}] computing setup trees and caps for circuit {circuit_type:?}");
                            SetupPrecomputations::get_trees_and_caps(
                                circuit,
                                log_lde_factor,
                                log_tree_cap_size,
                                trace.clone(),
                                &context,
                            )
                        })?
                        .clone();
                    let mut setup = SetupPrecomputations::new(
                        circuit,
                        log_lde_factor,
                        log_tree_cap_size,
                        false,
                        setup_trees_and_caps,
                        &context,
                    )?;
                    trace!("BATCH[{batch_id}] GPU_WORKER[{device_id}] transferring setup for circuit {circuit_type:?}");
                    setup.schedule_transfer(trace.clone(), &context)?;
                    Some(setup)
                }
            };
            let decoder_table_transfer = if let Some(decoder_data) = &precomputations.decoder_data {
                trace!("BATCH[{batch_id}] GPU_WORKER[{device_id}] transferring decoder table for circuit {circuit_type:?}");
                let mut decoder_table_transfer =
                    DecoderTableTransfer::new(decoder_data.clone(), &context)?;
                decoder_table_transfer.schedule_transfer(&context)?;
                Some(decoder_table_transfer)
            } else {
                None
            };
            let inits_and_teardowns_transfer = if let Some(inits_and_teardowns) =
                request.inits_and_teardowns()
            {
                trace!("BATCH[{batch_id}] GPU_WORKER[{device_id}] transferring inits and teardowns for circuit {circuit_type:?}[{sequence_id}]");
                let mut inits_and_teardowns_transfer =
                    InitsAndTeardownsTransfer::new(inits_and_teardowns.clone(), &context)?;
                inits_and_teardowns_transfer.schedule_transfer(&context)?;
                Some(inits_and_teardowns_transfer)
            } else {
                None
            };
            let tracing_data_transfer = if let Some(tracing_data) = request.tracing_data() {
                trace!("BATCH[{batch_id}] GPU_WORKER[{device_id}] transferring trace for circuit {circuit_type:?}[{sequence_id}]");
                let mut tracing_data_transfer =
                    TracingDataTransfer::new(tracing_data.clone(), &context)?;
                tracing_data_transfer.schedule_transfer(&context)?;
                Some(tracing_data_transfer)
            } else {
                None
            };
            Some((
                request,
                setup,
                decoder_table_transfer,
                inits_and_teardowns_transfer,
                tracing_data_transfer,
            ))
        } else {
            None
        };
        mem::swap(&mut current_phase_one, &mut phase_one);
        context.set_reversed_allocation_placement(even_odd_index == 0);
        let mut phase_two = if let Some((
            request,
            setup,
            decoder_table_transfer,
            inits_and_teardowns_transfer,
            tracing_data_transfer,
        )) = phase_one
        {
            let batch_id = request.batch_id();
            let circuit_type = request.circuit_type();
            let sequence_id = request.sequence_id();
            let lde_factor = circuit_type.get_lde_factor();
            assert!(lde_factor.is_power_of_two());
            let log_lde_factor = lde_factor.trailing_zeros();
            let tree_cap_size = circuit_type.get_tree_cap_size();
            assert!(tree_cap_size.is_power_of_two());
            let log_tree_cap_size = tree_cap_size.trailing_zeros();
            let precomputations = request.precomputations();
            let compiled_circuit = &precomputations.compiled_circuit;
            let decoder_table_allocation = if let Some(transfer) = decoder_table_transfer {
                let DecoderTableTransfer {
                    data_device,
                    transfer,
                    ..
                } = transfer;
                transfer.ensure_transferred(&context)?;
                Some(data_device)
            } else {
                None
            };
            let decoder_table = decoder_table_allocation.as_ref().map(|t| t.deref());
            let job = match &request {
                GpuWorkRequest::MemoryCommitment(_) => {
                    trace!("BATCH[{batch_id}] GPU_WORKER[{device_id}] producing memory commitment for circuit {circuit_type:?}[{sequence_id}]");
                    let job = commit_memory(
                        circuit_type,
                        compiled_circuit,
                        decoder_table,
                        inits_and_teardowns_transfer,
                        tracing_data_transfer,
                        log_lde_factor,
                        log_tree_cap_size,
                        &context,
                    )?;
                    JobType::MemoryCommitment(job)
                }
                GpuWorkRequest::Proof(request) => {
                    let aux_boundary_values =
                        if let Some(inits_and_teardowns) = &inits_and_teardowns_transfer {
                            let inits_and_teardowns = &inits_and_teardowns.data_host;
                            get_aux_arguments_boundary_values(compiled_circuit, inits_and_teardowns)
                        } else {
                            let sets_count = compiled_circuit
                                .memory_layout
                                .shuffle_ram_inits_and_teardowns
                                .len();
                            assert_eq!(
                                sets_count,
                                compiled_circuit.lazy_init_address_aux_vars.len()
                            );
                            vec![AuxArgumentsBoundaryValues::default(); sets_count]
                        };
                    let mut setup = setup.unwrap();
                    let delegation_processing_type = match circuit_type {
                        CircuitType::Delegation(delegation) => Some(delegation as u16),
                        CircuitType::Unrolled(_) => None,
                    };
                    let num_queries = num_queries_for_security_params(
                        verifier_common::SECURITY_BITS,
                        verifier_common::POW_BITS,
                        log_lde_factor as usize,
                    );
                    let pow_bits = verifier_common::POW_BITS as u32;
                    let trees_cache_mode = get_trees_cache_mode(circuit_type, &context);
                    trace!("BATCH[{batch_id}] GPU_WORKER[{device_id}] producing proof for circuit {circuit_type:?}[{sequence_id}]");
                    let job = prove(
                        circuit_type,
                        compiled_circuit.clone(),
                        request.external_challenges,
                        aux_boundary_values,
                        &mut setup,
                        decoder_table,
                        inits_and_teardowns_transfer,
                        tracing_data_transfer,
                        &precomputations.lde_precomputations,
                        delegation_processing_type,
                        precomputations.lde_precomputations.lde_factor,
                        num_queries,
                        pow_bits,
                        None,
                        false,
                        trees_cache_mode,
                        &context,
                    )?;
                    JobType::Proof(job)
                }
            };
            Some((request, job))
        } else {
            None
        };
        mem::swap(&mut current_phase_two, &mut phase_two);
        even_odd_index = 1 - even_odd_index;
        let result = if let Some((request, job)) = phase_two {
            match request {
                GpuWorkRequest::MemoryCommitment(request) => {
                    let MemoryCommitmentRequest {
                        batch_id,
                        circuit_type,
                        sequence_id,
                        inits_and_teardowns,
                        tracing_data,
                        ..
                    } = request;
                    let (merkle_tree_caps, commitment_time_ms) = match job {
                        JobType::MemoryCommitment(job) => job.finish()?,
                        JobType::Proof(_) => unreachable!(),
                    };
                    debug!("BATCH[{batch_id}] GPU_WORKER[{device_id}] produced memory commitment for circuit {circuit_type:?}[{sequence_id}] in {commitment_time_ms:.3} ms");
                    let result = MemoryCommitmentResult {
                        batch_id,
                        circuit_type,
                        sequence_id,
                        inits_and_teardowns,
                        tracing_data,
                        merkle_tree_caps,
                    };
                    Some(GpuWorkResult::MemoryCommitment(result))
                }
                GpuWorkRequest::Proof(request) => {
                    let ProofRequest {
                        batch_id,
                        circuit_type,
                        sequence_id,
                        inits_and_teardowns,
                        tracing_data,
                        ..
                    } = request;
                    let (proof, proof_time_ms) = match job {
                        JobType::MemoryCommitment(_) => unreachable!(),
                        JobType::Proof(job) => job.finish()?,
                    };
                    debug!("BATCH[{batch_id}] GPU_WORKER[{device_id}] produced proof for circuit {circuit_type:?}[{sequence_id}] in {proof_time_ms:.3} ms");
                    let result = ProofResult {
                        batch_id,
                        circuit_type,
                        sequence_id,
                        inits_and_teardowns,
                        tracing_data,
                        proof,
                    };
                    Some(GpuWorkResult::Proof(result))
                }
            }
        } else {
            None
        };
        results.send(result).unwrap()
    }
    assert!(current_phase_one.is_none());
    assert!(current_phase_two.is_none());
    trace!("GPU_WORKER[{device_id}] finished");
    Ok(())
}
