use std::sync::Arc;

use era_cudart::result::CudaResult;
use gpu_core::primitives::device_tracing::Range;
use gpu_prover_context::ProverContext;
use gpu_trace::trace::holder::TraceHolder;
use gpu_trace::trace::packed::PackedCosetRecomputeOracle;

use super::inputs::Proth120GkrWitnessInputs;
use super::programs::GkrProgramsPr;
use crate::forward::{
    prepare_dimension_reduction_forward, schedule_prepared_dimension_reduction_forward,
    ForwardOutputSlabTarget, GpuGKRForwardOutput,
};
use crate::gkr_address_audit::AddressClass;
use crate::setup::PackedSetupSource;
use crate::upstream::{GKRAddress, PR};
use crate::{ClassBacking, GpuBaseFieldPoly, GpuGKRStorage};

pub(crate) mod bind;
pub mod challenge_banks;
pub mod desc;
pub mod handoff;
pub(crate) mod kernels;
pub(crate) mod lower;
pub(crate) mod setup;
pub use challenge_banks::{
    schedule_forward_challenge_banks, ForwardChallengeBanks, ForwardChallengePlan,
};
pub use handoff::{
    prepare_backward_handoff_pr, ForwardToBackwardHandoffPr, GpuGKRDimensionReducingBackwardStatePr,
};

fn bind_columns(
    storage: &mut GpuGKRStorage<PR, PR>,
    holder: &TraceHolder<PR>,
    first: usize,
    columns: usize,
    address: fn(usize) -> GKRAddress,
) {
    assert!(
        first
            .checked_add(columns)
            .is_some_and(|end| end <= holder.columns_count),
        "Proth120 raw column range exceeds holder"
    );
    let backing = holder.raw_hypercube_backing();
    let rows = 1usize << holder.log_domain_size;
    for column in 0..columns {
        storage.insert_base_field_at_layer(
            0,
            address(column),
            GpuBaseFieldPoly::from_arc(Arc::clone(&backing), (first + column) * rows, rows),
        );
    }
}

pub(crate) fn bootstrap_storage(
    base: &PackedCosetRecomputeOracle<PR>,
    setup: &PackedSetupSource<'_>,
    witness: &Proth120GkrWitnessInputs<'_>,
    programs: &GkrProgramsPr,
) -> GpuGKRStorage<PR, PR> {
    let circuit = &programs.runtime_circuit;
    let raw = base.raw();
    assert_eq!(
        1usize << raw.log_domain_size,
        circuit.trace_len,
        "Proth120 merged raw rows mismatch"
    );
    assert_eq!(
        raw.columns_count,
        circuit.memory_layout.total_width + circuit.witness_layout.total_width,
        "Proth120 merged raw columns mismatch"
    );
    assert_eq!(
        setup.raw().log_domain_size,
        raw.log_domain_size,
        "Proth120 setup raw rows mismatch"
    );
    let mut storage = GpuGKRStorage::default();
    storage.set_layout(Arc::clone(&programs.storage_layout));
    bind_columns(
        &mut storage,
        raw,
        0,
        circuit.memory_layout.total_width,
        GKRAddress::BaseLayerMemory,
    );
    bind_columns(
        &mut storage,
        raw,
        circuit.memory_layout.total_width,
        circuit.witness_layout.total_width,
        GKRAddress::BaseLayerWitness,
    );
    bind_columns(
        &mut storage,
        setup.raw(),
        0,
        circuit.generic_lookup_tables_width,
        GKRAddress::Setup,
    );
    for column in 0..witness.scratch_columns {
        storage.insert_base_field_at_layer(
            0,
            GKRAddress::ScratchSpace(column),
            GpuBaseFieldPoly::from_arc(
                Arc::clone(&witness.scratch),
                column * witness.scratch_stride,
                witness.scratch_stride,
            ),
        );
    }
    storage.layers[0].base_class_backings.insert(
        AddressClass::ScratchSpace,
        ClassBacking {
            backing: Arc::clone(&witness.scratch),
            offset: 0,
        },
    );
    storage
}

pub fn schedule_forward_pass_pr(
    base: &PackedCosetRecomputeOracle<PR>,
    setup: &PackedSetupSource<'_>,
    witness: &Proth120GkrWitnessInputs<'_>,
    banks: &ForwardChallengeBanks,
    inits_and_teardowns_top_bits: &[u32],
    final_trace_size_log_2: u32,
    output_evaluations_slab: ForwardOutputSlabTarget<PR>,
    programs: &GkrProgramsPr,
    context: &ProverContext,
) -> CudaResult<GpuGKRForwardOutput<PR, PR>> {
    assert_eq!(
        final_trace_size_log_2, 4,
        "Proth120 forward final trace log must be 4"
    );
    let mut storage = bootstrap_storage(base, setup, witness, programs);
    let range = Range::new("gkr.proth120.forward.schedule")?;
    range.start(context.get_exec_stream())?;
    let setup = setup::schedule_setup(setup, &programs.runtime_circuit, banks, context)?;
    let mut lowered = bind::prepare_vm(
        programs,
        &mut storage,
        witness,
        &setup,
        banks,
        inits_and_teardowns_top_bits,
        context,
    )?;
    let circuit = &programs.runtime_circuit;
    let prepared = prepare_dimension_reduction_forward(
        &mut storage,
        circuit.layers.len(),
        &circuit.global_output_map,
        circuit.trace_len.trailing_zeros(),
        final_trace_size_log_2,
        Some(&output_evaluations_slab),
        context,
    )?;
    let start_round = bind::schedule_vm(&mut lowered, &prepared, context)?;
    schedule_prepared_dimension_reduction_forward(&prepared, start_round, context)?;
    range.end(context.get_exec_stream())?;
    Ok(GpuGKRForwardOutput::new(
        vec![range],
        storage,
        prepared.final_layer_idx,
        prepared.dimension_reduction_description,
    ))
}
