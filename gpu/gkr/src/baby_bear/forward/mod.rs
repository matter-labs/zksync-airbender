use std::sync::Arc;

use era_cudart::result::CudaResult;
use gpu_core::primitives::{
    device_tracing::Range,
    field::{BF, E4},
};
use gpu_prover_context::ProverContext;

pub use crate::baby_bear::forward::recompute::GkrMemoryPolicy;
use crate::{
    baby_bear::{
        backward::GpuGKRDimensionReducingBackwardState,
        setup::{bootstrap_storage_from_trace_holders, GpuGKRForwardSetup},
        stage1::GpuGKRStage1Output,
        GkrPrograms,
    },
    forward::*,
    gkr_address_audit::AddressClass,
    upstream::{GKRAddress, GKRCircuitArtifact, GKRExternalChallenges},
    GpuBaseFieldPoly, GpuGKRStorage,
};

impl GpuGKRForwardOutput<BF, E4> {
    pub fn into_dimension_reducing_backward_state(self) -> GpuGKRDimensionReducingBackwardState {
        GpuGKRDimensionReducingBackwardState::new(
            self.tracing_ranges,
            self.storage,
            self.initial_layer_for_sumcheck,
            self.dimension_reducing_inputs,
        )
    }
}

pub(crate) mod kernels;
pub(crate) mod recompute;
pub(crate) mod recompute_plan;
pub(crate) mod vm;

// The optional slab target transfers ownership into the scheduled forward pass.
#[allow(clippy::needless_pass_by_value)]
pub fn schedule_forward_pass(
    setup_trace_holder: Option<&gpu_trace::trace::holder::TraceHolder<BF>>,
    synthetic_setup_trace_holder: Option<&gpu_trace::trace::holder::TraceHolder<BF>>,
    stage1: &mut GpuGKRStage1Output,
    forward_setup: &mut GpuGKRForwardSetup,
    external_challenges: &GKRExternalChallenges<BF, E4>,
    inits_and_teardowns_top_bits: &[u32],
    final_trace_size_log_2: u32,
    output_evaluations_slab: Option<ForwardOutputSlabTarget<E4>>,
    programs: &GkrPrograms,
    memory_policy: GkrMemoryPolicy,
    context: &ProverContext,
) -> CudaResult<GpuGKRForwardOutput<BF, E4>> {
    let compiled_circuit = programs.runtime_circuit();
    let trace_len = compiled_circuit.trace_len;
    let stream = context.get_exec_stream();
    let mut tracing_ranges = Vec::new();
    let forward_range = Range::new("gkr.forward.schedule")?;
    forward_range.start(stream)?;
    let setup_trace_holder = setup_trace_holder
        .or(synthetic_setup_trace_holder)
        .expect("forward pass requires either uploaded or synthetic setup trace holder");
    let mut storage = bootstrap_storage_from_trace_holders::<E4>(
        Some(setup_trace_holder),
        setup_trace_holder.columns_count,
        setup_trace_holder.log_domain_size,
        setup_trace_holder.log_lde_factor,
        setup_trace_holder.log_rows_per_leaf,
        setup_trace_holder.log_tree_cap_size,
        &stage1.memory_trace_holder,
        &stage1.witness_trace_holder,
        stage1.merged_witness_offset,
    )?;
    let storage_layout = std::sync::Arc::new(
        crate::storage_layout::GpuGKRStorageLayout::from_artifact_with_tower(
            compiled_circuit,
            final_trace_size_log_2 as usize,
        ),
    );
    storage.set_layout(storage_layout);
    bind_scratch_space_into_storage(compiled_circuit, stage1, &mut storage);

    assert_eq!(
        programs.forward.layers.len(),
        compiled_circuit.layers.len(),
        "forward GKR program must cover every main layer",
    );

    let (mut lowered_vm, replay, workspace) = match memory_policy {
        GkrMemoryPolicy::Materialize => (
            vm::production_bind::prepare_vm(
                compiled_circuit,
                &programs.forward.layers,
                &mut storage,
                stage1,
                forward_setup,
                external_challenges,
                trace_len,
                inits_and_teardowns_top_bits,
                context,
            )?,
            None,
            None,
        ),
        GkrMemoryPolicy::Recompute { .. } => {
            let (replay, lowered, workspace) = recompute::ForwardReplay::prepare(
                programs,
                &mut storage,
                stage1,
                forward_setup,
                external_challenges,
                inits_and_teardowns_top_bits,
                memory_policy,
                context,
            )?;
            (lowered, Some(replay), Some(workspace))
        }
    };

    let prepared_reductions = prepare_dimension_reduction_forward(
        &mut storage,
        compiled_circuit.layers.len(),
        &compiled_circuit.global_output_map,
        trace_len.trailing_zeros(),
        final_trace_size_log_2,
        output_evaluations_slab.as_ref(),
        context,
    )?;

    let vm_range = Range::new("gkr.forward.vm")?;
    vm_range.start(stream)?;
    vm::production_bind::schedule_vm(
        &mut lowered_vm,
        &prepared_reductions,
        replay.as_ref().map(recompute::ForwardReplay::blocks),
        programs.circuit_type(),
        forward_setup,
        context,
    )?;
    drop(workspace);
    storage.replay = replay;
    vm_range.end(stream)?;
    tracing_ranges.push(vm_range);

    stage1.lookup_mappings.release_generic_family();
    stage1.lookup_mappings.release_range_check_16();
    stage1.lookup_mappings.release_timestamp();
    drop(forward_setup.take_generic_lookup());

    for (output_type, addresses) in compiled_circuit.global_output_map.iter() {
        for address in addresses.iter().copied() {
            assert!(
                storage.try_get_ext_poly(address).is_some(),
                "missing GPU forward output for {:?} at {:?}",
                output_type,
                address,
            );
        }
    }

    let dimension_reduction_range = Range::new("gkr.forward.dimension_reduction")?;
    dimension_reduction_range.start(stream)?;
    schedule_prepared_dimension_reduction_forward(
        &prepared_reductions,
        prepared_reductions.fused_prefix_rounds(),
        context,
    )?;
    dimension_reduction_range.end(stream)?;
    tracing_ranges.push(dimension_reduction_range);
    let initial_layer_for_sumcheck = prepared_reductions.final_layer_idx;
    let dimension_reducing_inputs = prepared_reductions.dimension_reduction_description;
    forward_range.end(stream)?;
    tracing_ranges.push(forward_range);

    Ok(GpuGKRForwardOutput {
        tracing_ranges,
        storage,
        initial_layer_for_sumcheck,
        dimension_reducing_inputs,
    })
}

fn hydrate_scratch_space_layer<E>(
    layer_idx: usize,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    stage1: &GpuGKRStage1Output,
    storage: &mut GpuGKRStorage<BF, E>,
) {
    let Some(scratch_space_trace) = stage1.scratch_space_trace.as_ref() else {
        return;
    };
    let trace_len = compiled_circuit.trace_len;
    for (scratch_idx, address) in compiled_circuit.scratch_space_mapping_rev.iter() {
        let GKRAddress::InnerLayer { layer, .. } = *address else {
            continue;
        };
        if layer != layer_idx || storage.try_get_base_poly(*address).is_some() {
            continue;
        }
        let offset = scratch_idx * trace_len;
        storage.insert_base_field_at_layer(
            layer_idx,
            *address,
            GpuBaseFieldPoly::from_arc(Arc::clone(scratch_space_trace), offset, trace_len),
        );
    }
}

/// Register scratch columns and their consolidated backing for layout-driven backward.
fn bind_scratch_space_into_storage<E>(
    compiled_circuit: &GKRCircuitArtifact<BF>,
    stage1: &GpuGKRStage1Output,
    storage: &mut GpuGKRStorage<BF, E>,
) {
    let Some(scratch_space_trace) = stage1.scratch_space_trace.as_ref() else {
        return;
    };
    if compiled_circuit.scratch_space_size == 0 {
        return;
    }
    let trace_len = compiled_circuit.trace_len;
    let scratch_space_size = compiled_circuit.scratch_space_size;
    for scratch_idx in 0..scratch_space_size {
        let address = GKRAddress::ScratchSpace(scratch_idx);
        if storage.try_get_base_poly(address).is_some() {
            continue;
        }
        let offset = scratch_idx * trace_len;
        storage.insert_base_field_at_layer(
            0,
            address,
            GpuBaseFieldPoly::from_arc(Arc::clone(scratch_space_trace), offset, trace_len),
        );
    }
    if storage.layers.is_empty() {
        storage
            .layers
            .resize_with(1, crate::GpuGKRLayerSource::default);
    }
    let prev = storage.layers[0].base_class_backings.insert(
        AddressClass::ScratchSpace,
        crate::ClassBacking {
            backing: Arc::clone(scratch_space_trace),
            offset: 0,
        },
    );
    assert!(
        prev.is_none(),
        "scratch_space backing already registered for layer 0 AddressClass::ScratchSpace"
    );
}

#[cfg(test)]
pub(crate) mod tests;
