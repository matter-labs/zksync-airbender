use crate::circuit_type::CircuitType;
use crate::execution::messages::GpuWorkRequest;
use crate::execution::A;
use crate::prover::context::ProverContext;
use crate::prover::decoder::DecoderTableTransfer;
use crate::prover::memory_policy::MemoryPolicy;
use crate::prover::proof::prove;
use crate::prover::setup::SetupPrecomputations;
use crate::prover::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};
use crate::witness::trace_unrolled::get_aux_arguments_boundary_values;
use era_cudart::result::CudaResult;
use prover::definitions::AuxArgumentsBoundaryValues;
use verifier_common::SecurityMarker;

struct SweepInput<'a> {
    request: GpuWorkRequest<A>,
    policy: MemoryPolicy,
    setup: SetupPrecomputations<'a>,
    decoder: Option<DecoderTableTransfer<'a>>,
    inits_and_teardowns: Option<InitsAndTeardownsTransfer<'a, A>>,
    tracing_data: Option<TracingDataTransfer<'a, A>>,
}

fn allocate_inputs<'a>(
    request: GpuWorkRequest<A>,
    policy: MemoryPolicy,
    context: &ProverContext,
) -> CudaResult<SweepInput<'a>> {
    let GpuWorkRequest::Proof(_) = &request else {
        unreachable!("the memory sweep only creates proof requests")
    };
    let circuit_type = request.circuit_type();
    let precomputations = request.precomputations();
    let log_lde_factor = circuit_type.get_lde_factor().trailing_zeros();
    let log_tree_cap_size = circuit_type.get_tree_cap_size().trailing_zeros();
    let setup_trees_and_caps = precomputations
        .setup_trees_and_caps
        .get_or_try_init(|| {
            SetupPrecomputations::get_trees_and_caps(
                &precomputations.compiled_circuit,
                log_lde_factor,
                log_tree_cap_size,
                precomputations.setup_trace.clone(),
                context,
            )
        })?
        .clone();
    let mut setup = SetupPrecomputations::new(
        &precomputations.compiled_circuit,
        log_lde_factor,
        log_tree_cap_size,
        policy.setup,
        setup_trees_and_caps,
        context,
    )?;
    setup.schedule_transfer(precomputations.setup_trace.clone(), context)?;

    let decoder = precomputations
        .decoder_data
        .as_ref()
        .map(|data| {
            let mut transfer = DecoderTableTransfer::new(data.clone(), context)?;
            transfer.schedule_transfer(context)?;
            Ok(transfer)
        })
        .transpose()?;
    let inits_and_teardowns = request
        .inits_and_teardowns()
        .as_ref()
        .map(|data| {
            let mut transfer = InitsAndTeardownsTransfer::new(data.clone(), context)?;
            transfer.schedule_transfer(context)?;
            Ok(transfer)
        })
        .transpose()?;
    let tracing_data = request
        .tracing_data()
        .as_ref()
        .map(|data| {
            let mut transfer = TracingDataTransfer::new(data.clone(), context)?;
            transfer.schedule_transfer(context)?;
            Ok(transfer)
        })
        .transpose()?;

    Ok(SweepInput {
        request,
        policy,
        setup,
        decoder,
        inits_and_teardowns,
        tracing_data,
    })
}

pub(super) fn warm_setup_cache(
    context: &mut ProverContext,
    request: GpuWorkRequest<A>,
) -> CudaResult<()> {
    context.set_reversed_allocation_placement(false);
    drop(allocate_inputs(
        request,
        MemoryPolicy::all_recompute(),
        context,
    )?);
    Ok(())
}

pub(super) fn run_sweep_case<S: SecurityMarker>(
    context: &mut ProverContext,
    target_request: GpuWorkRequest<A>,
    target_policy: MemoryPolicy,
    follower_request: GpuWorkRequest<A>,
) -> CudaResult<f32> {
    context.set_reversed_allocation_placement(false);
    let target = allocate_inputs(target_request, target_policy, context)?;
    context.set_reversed_allocation_placement(true);
    let follower = allocate_inputs(follower_request, MemoryPolicy::all_recompute(), context)?;
    context.set_reversed_allocation_placement(false);

    let SweepInput {
        request,
        policy,
        mut setup,
        decoder,
        inits_and_teardowns,
        tracing_data,
    } = target;
    let GpuWorkRequest::Proof(request) = request else {
        unreachable!()
    };
    let circuit_type = request.circuit_type;
    let precomputations = request.precomputations;
    let compiled_circuit = &precomputations.compiled_circuit;
    let decoder_allocation = decoder
        .map(|transfer| {
            let DecoderTableTransfer {
                data_device,
                transfer,
                ..
            } = transfer;
            transfer.ensure_transferred(context)?;
            Ok(data_device)
        })
        .transpose()?;
    let decoder_table = decoder_allocation.as_deref();
    let aux_boundary_values = if let Some(data) = &inits_and_teardowns {
        get_aux_arguments_boundary_values(compiled_circuit, &data.data_host)
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
    let delegation_processing_type = match circuit_type {
        CircuitType::Delegation(delegation) => Some(delegation as u16),
        CircuitType::Unrolled(_) => None,
    };
    let job = prove(
        circuit_type,
        compiled_circuit.clone(),
        request.external_challenges,
        aux_boundary_values,
        &mut setup,
        decoder_table,
        inits_and_teardowns,
        tracing_data,
        &precomputations.lde_precomputations,
        delegation_processing_type,
        precomputations.lde_precomputations.lde_factor,
        &circuit_type.get_security_config_for::<S>(),
        None,
        &policy,
        context,
    )?;
    drop(decoder_allocation);
    let (proof, elapsed_ms) = job.finish()?;
    drop(proof);
    drop(follower);
    Ok(elapsed_ms)
}
