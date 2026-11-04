use super::*;

pub fn create_jump_cleanup_offset_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let keys = key_for_continuous_log2_range(16);
    const TABLE_NAME: &'static str = "Jump offset check-cleanup table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < (1u64 << 16));

            let check_bit = (a >> 1) & 0x01;
            let output = a & (!0x3);

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(check_bit as u64);
            result[1] = F::from_u64_unchecked(output as u64);

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}
