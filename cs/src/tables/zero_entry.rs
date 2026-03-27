use super::*;

pub fn create_zero_entry_table<F: PrimeField, const TOTAL_WIDTH: usize>(id: u32) -> LookupTable<F> {
    assert!(TOTAL_WIDTH > 0);
    let keys = vec![[]];
    const TABLE_NAME: &'static str = "zero entry table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        0,
        TOTAL_WIDTH,
        |_keys| {
            let mut values = ArrayVec::new();
            for _ in 0..TOTAL_WIDTH {
                values.push(F::ZERO);
            }
            (0, values)
        },
        Some(|_| 0),
        id,
    )
}
