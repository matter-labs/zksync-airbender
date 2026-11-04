use super::*;

pub fn create_rom_separator_table<
    F: PrimeField,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    id: u32,
) -> LookupTable<F, 3> {
    let keys = key_for_continuous_log2_range(16);
    const TABLE_NAME: &'static str = "ROM address space separator table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < (1u64 << 16));

            let bound = 1 << ROM_ADDRESS_SPACE_SECOND_WORD_BITS;
            let input = a;
            let is_ram = input >= bound;
            let rom_chunk = input % bound;

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(is_ram as u64);
            result[1] = F::from_u64_unchecked(rom_chunk);

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}
