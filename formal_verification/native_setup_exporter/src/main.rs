#![feature(allocator_api, generic_const_exprs)]
#![allow(incomplete_features)]
//! Export actual native v2 table-driver/decoder rows, before physical trace assembly.
mod columns;
use columns::EncodedColumn;
use cs::machine::machine_configurations::pad_bytecode;
use cs::machine::ops::unrolled::load_store_word_only::{
    create_word_only_load_store_special_tables, word_only_load_store_table_driver_fn,
};
use cs::machine::ops::unrolled::{
    materialize_flattened_decoder_table, preprocess_bytecode, OpcodeFamilyDecoder,
    WordOnlyMemoryFamilyDecoder,
};
use cs::tables::{TableDriver, TableType};
use field::{Mersenne31Field, PrimeField};
use serde::{Deserialize, Serialize};
use std::alloc::Global;
use std::io::{Error, ErrorKind};
use std::path::Path;

const CAPACITY: usize = 1 << 20;
const MODULUS: u64 = (1 << 31) - 1;

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Matrix {
    length: usize,
    columns: Vec<EncodedColumn>,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Region {
    id: u32,
    offset: usize,
    data: Matrix,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Program {
    image_words: usize,
    image: EncodedColumn,
    text_words: usize,
    text: EncodedColumn,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Artifact {
    version: u32,
    field_modulus: u64,
    family: String,
    program: Program,
    generic_rows: usize,
    tables: Vec<Region>,
    decoder: Matrix,
    range16: Matrix,
}

fn column(length: usize, bound: u64, value: impl Fn(usize) -> u32) -> EncodedColumn {
    let encoded = EncodedColumn::encode(length, &value);
    encoded
        .validate(length, bound)
        .expect("canonical, complete column");
    assert!(
        encoded.matches_values(length, &value),
        "lossless native export"
    );
    assert_eq!(encoded.value_at(length), None, "column endpoint");
    if length != 0 {
        assert_eq!(encoded.value_at(0), Some(value(0)));
        assert_eq!(encoded.value_at(length - 1), Some(value(length - 1)));
    }
    encoded
}
fn matrix<const N: usize>(rows: &[[Mersenne31Field; N]]) -> Matrix {
    Matrix {
        length: rows.len(),
        columns: (0..N)
            .map(|i| column(rows.len(), MODULUS, |j| rows[j][i].as_u64_reduced() as u32))
            .collect(),
    }
}
fn read_words(path: &Path) -> Result<Vec<u32>, Error> {
    let bytes = std::fs::read(path)?;
    if bytes.len() % 4 != 0 || bytes.len() / 4 > CAPACITY {
        return Err(Error::new(
            ErrorKind::InvalidData,
            "expected at most 4 MiB of little-endian words",
        ));
    }
    Ok(bytes
        .chunks_exact(4)
        .map(|b| u32::from_le_bytes(b.try_into().unwrap()))
        .collect())
}
fn export(mut image: Vec<u32>, text: Vec<u32>) -> Artifact {
    pad_bytecode::<4194304>(&mut image);
    let program = Program {
        image_words: image.len(),
        image: column(image.len(), 1u64 << 32, |i| image[i]),
        text_words: text.len(),
        text: column(text.len(), 1u64 << 32, |i| text[i]),
    };
    let mut driver = TableDriver::<Mersenne31Field>::new();
    word_only_load_store_table_driver_fn(&mut driver);
    for (id, table) in create_word_only_load_store_special_tables::<_, 6>(&image) {
        driver.add_table_with_content(id, table);
    }
    let rows = driver.dump_tables();
    let mut offset = 0;
    let tables = driver
        .tables
        .iter()
        .filter(|t| t.get_size() != 0)
        .map(|table| {
            let length = table.get_size();
            let region = Region {
                id: table.get_table_id(),
                offset,
                data: matrix(&rows[offset..offset + length]),
            };
            offset += length;
            region
        })
        .collect();
    assert_eq!(offset, rows.len());
    let generic_rows = rows.len();
    drop(rows);
    drop(driver);
    let family: Box<dyn OpcodeFamilyDecoder> = Box::new(WordOnlyMemoryFamilyDecoder);
    let (entries, witness) =
        preprocess_bytecode::<Mersenne31Field, Global>(&text, CAPACITY, &family, &[]);
    drop(witness);
    let rows = materialize_flattened_decoder_table(&entries);
    drop(entries);
    let decoder = matrix(&rows);
    drop(rows);
    let range = TableType::RangeCheckLarge.generate_table::<Mersenne31Field>();
    let mut rows = Vec::new();
    range.dump_limited_columns::<1>(&mut rows);
    Artifact {
        version: 1,
        field_modulus: MODULUS,
        family: "load_store_word_only".into(),
        program,
        generic_rows,
        tables,
        decoder,
        range16: matrix(&rows),
    }
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args_os().collect();
    let artifact = if args.len() == 3 && args[1] == "--fixture" {
        let words = vec![0x0100a183, 0x0030a823, 0x0100a003, 0xc0001073];
        export(words.clone(), words)
    } else if args.len() == 4 {
        export(
            read_words(Path::new(&args[1]))?,
            read_words(Path::new(&args[2]))?,
        )
    } else {
        return Err(
            "usage: exporter IMAGE.bin TEXT.bin OUTPUT.json | exporter --fixture OUTPUT.json"
                .into(),
        );
    };
    // Reparse and compare every compressed field, including separate public image/text inputs.
    let bytes = serde_json::to_vec_pretty(&artifact)?;
    let recovered: Artifact = serde_json::from_slice(&bytes)?;
    assert_eq!(
        serde_json::to_value(&artifact)?,
        serde_json::to_value(recovered)?
    );
    std::fs::write(args.last().unwrap(), [bytes, vec![b'\n']].concat())?;
    Ok(())
}
