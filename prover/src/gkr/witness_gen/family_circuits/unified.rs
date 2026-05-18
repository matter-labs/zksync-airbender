use super::{
    evaluate_gkr_memory_witness_for_executor_family, evaluate_gkr_witness_for_executor_family,
    GKRFullWitnessTrace, GKRMemoryOnlyWitnessTrace,
};
use crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use cs::gkr_compiler::GKRCircuitArtifact;
use cs::oracle::Oracle;
use cs::tables::TableDriver;
use fft::GoodAllocator;
use field::PrimeField;
use worker::Worker;

pub fn build_unified_table_driver<F: PrimeField>(binary: &[u32]) -> TableDriver<F> {
    let mut table_driver = TableDriver::<F>::new();
    cs::gkr_circuits::unified_reduced_machine::unified_reduced_machine_table_driver_fn(
        &mut table_driver,
    );
    let extra_tables = cs::gkr_circuits::mem_word_only::create_mem_word_only_special_tables::<
        _,
        { common_constants::ROM_SECOND_WORD_BITS },
    >(binary);
    for (table_type, table) in extra_tables {
        table_driver.add_table_with_content(table_type, table);
    }
    table_driver
}

pub fn evaluate_gkr_memory_witness_for_unified_family<
    F: PrimeField,
    O: Oracle<F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    circuit: &GKRCircuitArtifact<F>,
    num_cycles: usize,
    oracle: &O,
    worker: &Worker,
    inits_and_teardowns: Option<Vec<([Vec<F, A>; 2], [Vec<F, A>; 2])>>,
    inner_alloc: A,
    outer_alloc: B,
) -> GKRMemoryOnlyWitnessTrace<F, A, B> {
    evaluate_gkr_memory_witness_for_executor_family(
        circuit,
        num_cycles,
        oracle,
        worker,
        inits_and_teardowns,
        inner_alloc,
        outer_alloc,
    )
}

pub fn evaluate_gkr_witness_for_unified_family<
    F: PrimeField,
    O: Oracle<F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    circuit: &GKRCircuitArtifact<F>,
    witness_eval_fn: fn(&mut ColumnMajorWitnessProxy<'_, O, F>),
    num_cycles: usize,
    oracle: &O,
    table_driver: &TableDriver<F>,
    worker: &Worker,
    inits_and_teardowns: Option<Vec<([Vec<F, A>; 2], [Vec<F, A>; 2])>>,
    inner_alloc: A,
    outer_alloc: B,
) -> GKRFullWitnessTrace<F, A, B> {
    evaluate_gkr_witness_for_executor_family(
        circuit,
        witness_eval_fn,
        num_cycles,
        oracle,
        table_driver,
        worker,
        inits_and_teardowns,
        inner_alloc,
        outer_alloc,
    )
}
