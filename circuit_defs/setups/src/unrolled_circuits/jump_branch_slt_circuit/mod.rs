use super::*;

pub fn jump_branch_slt_circuit_setup<A: GoodAllocator + 'static, B: GoodAllocator>(
    binary_image: &[u32],
    bytecode: &[u32],
    worker: &Worker,
) -> UnrolledCircuitPrecomputations<A, B> {
    let circuit = ::jump_branch_slt::get_circuit_for_rom_bound::<
        { ::jump_branch_slt::ROM_ADDRESS_SPACE_SECOND_WORD_BITS },
    >(binary_image);
    let table_driver = ::jump_branch_slt::get_table_driver(binary_image);
    let (decoder_table_data, witness_gen_data) =
        ::jump_branch_slt::get_decoder_table::<B>(bytecode);
    use prover::cs::machine::ops::unrolled::materialize_flattened_decoder_table;
    let decoder_table = materialize_flattened_decoder_table::<Mersenne31Field>(&decoder_table_data);

    let twiddles = Twiddles::get(::jump_branch_slt::DOMAIN_SIZE, &worker);
    let lde_precomputations = LdePrecomputations::new(
        ::jump_branch_slt::DOMAIN_SIZE,
        ::jump_branch_slt::LDE_FACTOR,
        ::jump_branch_slt::LDE_SOURCE_COSETS,
        &worker,
    );
    let setup =
        SetupPrecomputations::<DEFAULT_TRACE_PADDING_MULTIPLE, A, DefaultTreeConstructor>::from_tables_and_trace_len_with_decoder_table(
            &table_driver,
            &decoder_table,
            ::jump_branch_slt::DOMAIN_SIZE,
            &circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            ::jump_branch_slt::LDE_FACTOR,
            ::jump_branch_slt::TREE_CAP_SIZE,
            &worker,
        );

    #[cfg(feature = "witness_eval_fn")]
    let witness_eval_fn = Some(UnrolledCircuitWitnessEvalFn::NonMemory {
        witness_fn: ::jump_branch_slt::witness_eval_fn_for_gpu_tracer,
        decoder_table: witness_gen_data,
        default_pc_value_in_padding: 0,
    });

    #[cfg(not(feature = "witness_eval_fn"))]
    let witness_eval_fn = None;

    UnrolledCircuitPrecomputations {
        family_idx: ::jump_branch_slt::FAMILY_IDX,
        trace_len: ::jump_branch_slt::DOMAIN_SIZE,
        lde_factor: ::jump_branch_slt::LDE_FACTOR,
        tree_cap_size: ::jump_branch_slt::TREE_CAP_SIZE,
        compiled_circuit: circuit,
        table_driver,
        twiddles,
        lde_precomputations,
        setup,
        witness_eval_fn_for_gpu_tracer: witness_eval_fn,
    }
}
