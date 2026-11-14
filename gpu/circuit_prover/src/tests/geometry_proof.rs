use super::*;

pub(super) fn gpu_memory_caps(
    base: &BasicUnrolledFixture,
    geometry: BaseCommitmentGeometry,
) -> Vec<MerkleTreeCapVarLength> {
    let context = &base.context;
    let baseline = context.get_used_mem_current();
    let decoder = base
        .compiled_circuit
        .has_decoder_lookup
        .then(|| DecoderTableTransfer::new(Arc::clone(&base.decoder_table_host), context).unwrap());
    let inits = base.inits_and_teardowns_host.clone().map(|host| {
        InitsAndTeardownsTransfer::new(
            Some(host),
            base.compiled_circuit.memory_layout.teardown_sets.len(),
            base.compiled_circuit.trace_len,
            context,
        )
        .unwrap()
    });
    let trace = base
        .tracing_data_host
        .as_ref()
        .map(|host| {
            TracingDataTransfer::new(host.clone(), base.compiled_circuit.trace_len, context)
        })
        .transpose()
        .unwrap();
    let job = if geometry.commitment_mode() == CommitmentMode::MergedMemoryAndWitness {
        use gpu_gkr::stage1::merged_commitment::{
            commit_merged_from_transfers, GpuGKRMergedCommitTransfer,
        };
        let setup = gpu_gkr::setup::GpuGKRSetupTransfer::new(
            Arc::clone(base.gpu_setup_host.as_ref().unwrap()),
            base.partial_trees().setup,
            context,
        )
        .unwrap();
        let mut inputs =
            GpuGKRMergedCommitTransfer::new(setup, decoder, inits, trace, context).unwrap();
        inputs.schedule(context).unwrap();
        commit_merged_from_transfers(
            &base.gkr_programs,
            &base.prover_config,
            inputs,
            presets::merged_commit_strategy(base.circuit_type, base.profile),
            base.partial_trees(),
            None,
            context,
        )
        .unwrap()
    } else {
        let mut inputs = gpu_trace::trace::memory::GpuGKRCommitMemoryTransfer::new(
            decoder, inits, trace, context,
        )
        .unwrap();
        inputs.schedule(context).unwrap();
        gpu_trace::trace::memory::commit_memory_from_transfers_for_geometry(
            base.circuit_type,
            &base.compiled_circuit,
            inputs,
            geometry,
            gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS,
            context,
        )
        .unwrap()
    };
    let (caps, _) = job.finish().unwrap();
    assert_eq!(context.get_used_mem_current(), baseline);
    caps
}
