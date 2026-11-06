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
    let trace = TracingDataTransfer::new(
        base.tracing_data_host.clone(),
        base.compiled_circuit.trace_len,
        context,
    )
    .unwrap();
    let job = if geometry.commitment_mode() == CommitmentMode::MergedMemoryAndWitness {
        use gpu_gkr::stage1::merged_commitment::{
            commit_merged_from_transfers, GpuGKRMergedCommitTransfer,
        };
        let setup = gpu_gkr::setup::GpuGKRSetupTransfer::new(
            Arc::clone(base.gpu_setup_host.as_ref().unwrap()),
            context,
        )
        .unwrap();
        let mut inputs =
            GpuGKRMergedCommitTransfer::new(setup, decoder, inits, Some(trace), context).unwrap();
        inputs.schedule(context).unwrap();
        commit_merged_from_transfers(&base.gkr_programs, &base.prover_config, inputs, context)
            .unwrap()
    } else {
        let mut inputs = gpu_trace::trace::memory_transfer::GpuGKRCommitMemoryTransfer::new(
            decoder,
            inits,
            Some(trace),
            context,
        )
        .unwrap();
        inputs.schedule(context).unwrap();
        gpu_trace::trace::memory::commit_memory_from_transfers_for_geometry(
            base.circuit_type,
            &base.compiled_circuit,
            inputs,
            geometry,
            context,
        )
        .unwrap()
    };
    let (caps, _) = job.finish().unwrap();
    assert_eq!(context.get_used_mem_current(), baseline);
    caps
}

pub(super) fn geometry_proof(mut fixture: BasicUnrolledProofFixture) {
    let base = &mut fixture.base;
    let geometry = BaseCommitmentGeometry::from_config(
        &base.prover_config,
        BaseColumns::of(&base.compiled_circuit),
    );
    base.memory_tree_caps = gpu_memory_caps(base, geometry);
    let baseline = base.context.get_used_mem_current();
    let (proof, _) = base.schedule_prove().unwrap().finish().unwrap();
    assert_gkr_proof_eq_for_test(&proof, &fixture.expected_cpu_proof);
    assert_eq!(
        serde_json::to_vec(&proof).unwrap(),
        serde_json::to_vec(&fixture.expected_cpu_proof).unwrap()
    );
    assert_eq!(base.context.get_used_mem_current(), baseline);
}
