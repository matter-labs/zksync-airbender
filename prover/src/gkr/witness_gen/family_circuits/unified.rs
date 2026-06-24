use cs::tables::TableDriver;
use field::PrimeField;

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
