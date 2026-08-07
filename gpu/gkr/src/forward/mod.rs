use std::collections::BTreeMap;
use std::sync::Arc;

use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;

use super::backward::GpuGKRDimensionReducingBackwardState;
use super::gkr_address_audit::AddressClass;
use super::setup::{bootstrap_storage_from_trace_holders, GpuGKRForwardSetup};
use super::stage1::GpuGKRStage1Output;
use super::{GpuBaseFieldPoly, GpuExtensionFieldPoly, GpuGKRLayerSource, GpuGKRStorage};
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr_compiler::CompiledLayer;
use gpu_ops::simple::{Add, BinaryOp, Mul, SetByRef, SetByVal, Sub};
use gpu_prover_context::ProverContext;

use crate::GkrPrograms;

pub struct GpuGKRForwardOutput<B, E> {
    tracing_ranges: Vec<Range>,
    pub storage: GpuGKRStorage<B, E>,
    pub initial_layer_for_sumcheck: usize,
    pub dimension_reducing_inputs:
        BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
}

pub struct GpuGKRTranscriptHandoff<E> {
    flat_evaluations_backing: Arc<DeviceAllocation<E>>,
    flat_total_len: usize,
}

pub struct ForwardOutputSlabTarget<E> {
    pub backing: Arc<DeviceAllocation<E>>,
    pub len: usize,
}

impl<E> GpuGKRTranscriptHandoff<E> {
    pub fn device_flat_evaluations(&self) -> &DeviceSlice<E> {
        &self.flat_evaluations_backing[..self.flat_total_len]
    }
}

impl<B, E: Copy> GpuGKRForwardOutput<B, E> {
    pub fn transcript_handoff(&self) -> GpuGKRTranscriptHandoff<E> {
        let reduced_outputs = self
            .dimension_reducing_inputs
            .get(&self.initial_layer_for_sumcheck)
            .expect("reduced outputs for initial sumcheck layer must exist");

        let output_layer = self.initial_layer_for_sumcheck + 1;
        let class = super::gkr_address_audit::AddressClass::ThisLayerInnerLayerWrite;
        let flat_evaluations_backing: Arc<DeviceAllocation<E>> = Arc::clone(
            self.storage
                .layers
                .get(output_layer)
                .and_then(|layer| layer.ext_class_backings.get(&class))
                .expect(
                    "consolidated backing Arc for reduced-output polys must exist after the \
                     forward dim-reduction pass",
                ),
        );

        let mut flat_total_len = 0usize;
        for reduced_io in reduced_outputs.values() {
            let [first_addr, second_addr]: [GKRAddress; 2] = reduced_io
                .output
                .clone()
                .try_into()
                .expect("transcript handoff expects exactly two reduced outputs per type");
            for addr in [first_addr, second_addr] {
                let poly = self
                    .storage
                    .try_get_ext_poly(addr)
                    .unwrap_or_else(|| panic!("missing reduced extension poly for {:?}", addr));
                flat_total_len += poly.len();
            }
        }
        assert!(
            flat_total_len <= flat_evaluations_backing.len(),
            "consolidated backing must contain the reduced-output poly prefix"
        );

        GpuGKRTranscriptHandoff {
            flat_evaluations_backing,
            flat_total_len,
        }
    }
}

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
pub(super) use kernels::*;

mod dimension_reducing;
mod lookup_lifetime;
pub(crate) mod vm;

use crate::upstream::{
    DimensionReducingInputOutput, Field, FieldExtension, GKRAddress, GKRCircuitArtifact,
    GKRExternalChallenges, GKRLayerDescription, OutputType,
};
use dimension_reducing::schedule_dimension_reduction_forward;
use lookup_lifetime::{analyze_forward_lookup_usage, release_forward_lookup_resources_after_layer};

// The optional slab target transfers ownership into the scheduled forward pass.
#[allow(clippy::needless_pass_by_value)]
pub fn schedule_forward_pass(
    setup_trace_holder: Option<&gpu_trace::trace::holder::TraceHolder<BF>>,
    synthetic_setup_trace_holder: Option<&gpu_trace::trace::holder::TraceHolder<BF>>,
    stage1: &mut GpuGKRStage1Output,
    forward_setup: &mut GpuGKRForwardSetup,
    external_challenges: &GKRExternalChallenges<BF, E4>,
    // ACTUAL per-circuit inits-and-teardowns top bits (one per teardown set):
    // canonical `0..sets` for circuits with real i&t data, all zeros for
    // trivial (dummy) unified chunks. Values feed only constant terms in the
    // i&t initial-pair materialization; plan structure is invariant to them.
    inits_and_teardowns_top_bits: &[u32],
    final_trace_size_log_2: u32,
    output_evaluations_slab: Option<ForwardOutputSlabTarget<E4>>,
    programs: &GkrPrograms,
    context: &ProverContext,
) -> CudaResult<GpuGKRForwardOutput<BF, E4>> {
    let compiled_circuit = programs.runtime_circuit();
    let trace_len = compiled_circuit.trace_len;
    let stream = context.get_exec_stream();
    let mut tracing_ranges = Vec::new();
    let forward_range = Range::new("gkr.forward.schedule")?;
    forward_range.start(stream)?;
    let usage = analyze_forward_lookup_usage(programs);
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
    )?;
    let storage_layout = std::sync::Arc::new(
        crate::storage_layout::GpuGKRStorageLayout::from_artifact_with_tower(
            &compiled_circuit,
            final_trace_size_log_2 as usize,
        ),
    );
    storage.set_layout(storage_layout);
    bind_scratch_space_into_storage(&compiled_circuit, stage1, &mut storage);

    if usage.last_generic_mapping_layer.is_none() {
        stage1.lookup_mappings.release_generic_family();
    }
    if usage.last_range_mapping_layer.is_none() {
        stage1.lookup_mappings.release_range_check_16();
    }
    if usage.last_timestamp_mapping_layer.is_none() {
        stage1.lookup_mappings.release_timestamp();
    }
    if usage.last_generic_lookup_layer.is_none() {
        forward_setup.release_generic_lookup();
    }

    assert_eq!(
        programs.forward.layers.len(),
        compiled_circuit.layers.len(),
        "forward GKR program must cover every main layer",
    );

    for (layer_idx, layer) in compiled_circuit.layers.iter().enumerate() {
        let layer_range = Range::new(format!("gkr.forward.layer.{layer_idx}"))?;
        layer_range.start(stream)?;
        schedule_layer(
            layer_idx,
            layer,
            &compiled_circuit,
            &mut storage,
            stage1,
            forward_setup,
            external_challenges,
            trace_len,
            inits_and_teardowns_top_bits,
            &programs.forward.layers[layer_idx],
            context,
        )?;
        layer_range.end(stream)?;
        tracing_ranges.push(layer_range);
        release_forward_lookup_resources_after_layer(layer_idx, &usage, stage1, forward_setup);
    }

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
    let (initial_layer_for_sumcheck, dimension_reducing_inputs) =
        schedule_dimension_reduction_forward(
            &mut storage,
            compiled_circuit.layers.len(),
            &compiled_circuit.global_output_map,
            trace_len.trailing_zeros(),
            final_trace_size_log_2,
            output_evaluations_slab.as_ref(),
            &mut tracing_ranges,
            context,
        )?;
    dimension_reduction_range.end(stream)?;
    tracing_ranges.push(dimension_reduction_range);
    forward_range.end(stream)?;
    tracing_ranges.push(forward_range);

    Ok(GpuGKRForwardOutput {
        tracing_ranges,
        storage,
        initial_layer_for_sumcheck,
        dimension_reducing_inputs,
    })
}

fn schedule_layer(
    layer_idx: usize,
    layer: &GKRLayerDescription,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    storage: &mut GpuGKRStorage<BF, E4>,
    stage1: &GpuGKRStage1Output,
    forward_setup: &GpuGKRForwardSetup,
    external_challenges: &GKRExternalChallenges<BF, E4>,
    trace_len: usize,
    inits_and_teardowns_top_bits: &[u32],
    program: &CompiledLayer,
    context: &ProverContext,
) -> CudaResult<()> {
    hydrate_scratch_space_layer(layer_idx, compiled_circuit, stage1, storage);
    vm::production_bind::schedule_vm_layer(
        layer_idx,
        layer,
        program,
        storage,
        stage1,
        forward_setup,
        external_challenges,
        trace_len,
        inits_and_teardowns_top_bits,
        context,
    )?;
    Ok(())
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

/// Register `stage1.scratch_space_trace` as the consolidated `AddressClass::ScratchSpace`
/// backing at layer 0, plus per-`ScratchSpace` poly views. Mirrors the trace-holder
/// pattern in `bind_trace_holder_columns_into_storage`: scratch is a first-class
/// trace-aligned class (poly_idx == scratch_idx), so the layout-driven backward
/// path picks it up uniformly with witness/memory.
///
/// Called once by `schedule_forward_pass` after the storage layout is bound and
/// before per-layer scheduling begins.
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
    let prev = storage.layers[0]
        .base_class_backings
        .insert(AddressClass::ScratchSpace, Arc::clone(scratch_space_trace));
    assert!(
        prev.is_none(),
        "scratch_space backing already registered for layer 0 AddressClass::ScratchSpace"
    );
}

#[cfg(test)]
mod tests;
