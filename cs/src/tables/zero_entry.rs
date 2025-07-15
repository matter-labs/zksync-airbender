use super::*;

pub fn create_zero_entry_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let keys = vec![[F::ZERO; 3]];
    const TABLE_NAME: &'static str = "zero entry table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        3,
        |_keys| (0, [F::ZERO; 3]),
        Some(|_| 0),
        id,
    )
}
