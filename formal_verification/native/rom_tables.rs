// Artifact-only materialization. Production table constructors are unchanged.
// Each chunk uses the original native ROM constructor, including its padding
// and sign extension. Only address/tag positions are lifted to the full domain.
use cs::tables::{IndexLookupFn, LookupTable, LookupWrapper, TableType, ValueLookupFn};
use field::PrimeField;
use std::sync::Arc;

fn rom_table<F: PrimeField, const ROM_BITS: usize>(
    image: &[u32],
    kind: TableType,
) -> LookupTable<F> {
    const CHUNK_BITS: usize = 1;
    const ADDRESS_BITS: usize = 16 + CHUNK_BITS;
    const CHUNK_WORDS: usize = (1 << ADDRESS_BITS) / 4;
    assert!(ROM_BITS >= CHUNK_BITS && ROM_BITS <= common_constants::ROM_SECOND_WORD_BITS);
    assert!(image.len() <= (1 << (16 + ROM_BITS)) / 4);
    let byte = kind == TableType::LoadByteRomRead;
    assert!(byte || kind == TableType::LoadHalfwordRomRead);
    let mut rows = Vec::with_capacity(1 << (16 + ROM_BITS + usize::from(byte)));
    let mut prototype = None;
    for chunk_index in 0..(1 << (ROM_BITS - CHUNK_BITS)) {
        let start = chunk_index * CHUNK_WORDS;
        let chunk_image = if start < image.len() {
            &image[start..image.len().min(start + CHUNK_WORDS)]
        } else {
            &[]
        };
        let mut chunk = if byte {
            cs::tables::create_load_byte_from_rom_table::<F, CHUNK_BITS>(
                chunk_image,
                kind.to_table_id(),
            )
        } else {
            cs::tables::create_load_halfword_from_rom_table::<F, CHUNK_BITS>(
                chunk_image,
                kind.to_table_id(),
            )
        };
        // Export/compile consumers need the literal rows and table geometry.
        // Drop each chunk's eager witness indexes before constructing the next.
        chunk.lookup_data = Arc::default();
        chunk.content_data = Arc::default();
        chunk.quick_value_lookup_fn = ValueLookupFn::None;
        chunk.quick_index_lookup_fn = IndexLookupFn::None;
        let data = Arc::try_unwrap(std::mem::take(&mut chunk.data))
            .unwrap_or_else(|_| panic!("native ROM chunk unexpectedly shared"));
        let offset = (start * 4) as u32;
        rows.extend(data.into_iter().map(|mut row| {
            let key = row[0].as_u32_reduced();
            let address = (key & ((1 << ADDRESS_BITS) - 1)) | offset;
            let flags = key >> ADDRESS_BITS;
            row[0] = F::from_u32_unchecked(address | (flags << (16 + ROM_BITS)));
            row
        }));
        if prototype.is_none() {
            prototype = Some(chunk);
        }
    }
    let mut table = prototype.expect("nonempty ROM domain");
    assert_eq!(rows.len(), 1 << (16 + ROM_BITS + usize::from(byte)));
    table.data = Arc::new(rows);
    table
}

pub fn subword_rom_tables<F: PrimeField, const ROM_BITS: usize>(
    image: &[u32],
) -> impl Iterator<Item = (TableType, LookupWrapper<F>)> + '_ {
    [TableType::LoadHalfwordRomRead, TableType::LoadByteRomRead]
        .into_iter()
        .map(move |kind| {
            (
                kind,
                LookupWrapper::Initialized(rom_table::<F, ROM_BITS>(image, kind)),
            )
        })
}

#[allow(dead_code)] // The source/compiler capture example uses only the row builder.
pub fn compile_subword_circuit(
    image: &[u32],
    cached: bool,
) -> cs::gkr_compiler::GKRCircuitArtifact<field::baby_bear::base::BabyBearField> {
    use cs::cs::{circuit_impl::BasicAssembly, circuit_trait::Circuit};
    use cs::gkr_circuits::*;
    use field::baby_bear::base::BabyBearField as F;
    let mut assembly = BasicAssembly::<F>::new();
    mem_subword_only_table_addition_fn(&mut assembly);
    for (kind, table) in subword_rom_tables::<F, { common_constants::ROM_SECOND_WORD_BITS }>(image)
    {
        assembly.add_table_with_content(kind, table);
    }
    mem_subword_only_circuit_with_preprocessed_bytecode_for_gkr(&mut assembly);
    let (source, _) = assembly.finalize();
    cs::gkr_compiler::GKRCompiler::default().compile_family_circuit(
        source,
        common_constants::ROM_WORD_SIZE,
        0,
        24,
        cached,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use field::baby_bear::base::BabyBearField as F;

    fn compare(image: &[u32]) {
        for kind in [TableType::LoadHalfwordRomRead, TableType::LoadByteRomRead] {
            let chunked = rom_table::<F, 2>(image, kind);
            let original = if kind == TableType::LoadByteRomRead {
                cs::tables::create_load_byte_from_rom_table::<F, 2>(image, kind.to_table_id())
            } else {
                cs::tables::create_load_halfword_from_rom_table::<F, 2>(image, kind.to_table_id())
            };
            assert_eq!(chunked.data, original.data);
            assert_eq!(chunked.name, original.name);
            assert_eq!(chunked.id, original.id);
            assert_eq!(chunked.num_key_columns, original.num_key_columns);
            assert_eq!(chunked.num_value_columns, original.num_value_columns);
            assert!(chunked.lookup_data.is_empty() && chunked.content_data.is_empty());
        }
    }

    #[test]
    fn native_chunks_preserve_empty_image_padding() {
        compare(&[]);
    }

    #[test]
    fn native_chunks_preserve_cross_chunk_image_and_signed_values() {
        let mut image = vec![0; (1 << 17) / 4 + 2];
        image[0] = 0x807f_ff80;
        image[(1 << 17) / 4 - 1] = 0xffff_7f00;
        image[(1 << 17) / 4] = 0x0080_8000;
        image[(1 << 17) / 4 + 1] = 0xff00_00ff;
        compare(&image);
    }
}
