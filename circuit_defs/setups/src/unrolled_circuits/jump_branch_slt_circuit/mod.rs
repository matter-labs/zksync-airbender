use common_constants::PC_STEP;

use super::*;

pub fn jump_branch_slt_circuit_setup<A: GoodAllocator>(
    decoder_table_data: &[Option<ExecutorFamilyDecoderData>],
    use_caches: bool,
    worker: &Worker,
) -> CircuitSetup<A> {
    type C = ::jump_branch_slt::JumpBranchSltCircuit;

    #[cfg(not(feature = "witness_eval_fn"))]
    let witness_eval_fn = None;

    #[cfg(feature = "witness_eval_fn")]
    let witness_eval_fn: Option<
        fn(&mut ColumnMajorWitnessProxy<'_, NonMemoryCircuitOracle<'_>, BabyBearField>),
    > = Some(::jump_branch_slt::witness_eval_fn);

    make_setup_for_non_mem_circuit::<C, A>(
        witness_eval_fn,
        PC_STEP as u32,
        decoder_table_data,
        use_caches,
    )
}
