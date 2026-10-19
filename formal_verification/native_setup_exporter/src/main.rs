#![feature(allocator_api, generic_const_exprs)]
#![allow(incomplete_features)]
//! Export actual native v2 table-driver/decoder rows, before physical trace assembly.
mod columns;
use columns::EncodedColumn;
use cs::definitions::TIMESTAMP_COLUMNS_NUM_BITS;
use cs::machine::machine_configurations::pad_bytecode;
use cs::machine::ops::unrolled::load_store_word_only::{
    create_word_only_load_store_special_tables, word_only_load_store_table_driver_fn,
};
use cs::machine::ops::unrolled::{
    decoder_table_padding, materialize_flattened_decoder_table, preprocess_bytecode,
    AddSubLuiAuipcMopDecoder, JumpSltBranchDecoder, OpcodeFamilyDecoder, ShiftBinaryCsrrwDecoder,
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

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Scalars {
    version: u32,
    field_modulus: u64,
    profile: String,
    range16: Matrix,
    timestamp19: Matrix,
}

/// Actual native decoder rows plus their public little-endian text input.
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct DecoderArtifact {
    version: u32,
    field_modulus: u64,
    family: String,
    text_words: usize,
    text: EncodedColumn,
    decoder: Matrix,
}

/// The same native sentinel used by get_main_domain_trace beyond the prefix.
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct DecoderPadding {
    version: u32,
    field_modulus: u64,
    profile: String,
    row: [u32; 10],
}

/// Actual fixed tables registered by the native jump/branch/SLT family.
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ControlTables {
    version: u32,
    field_modulus: u64,
    profile: String,
    generic_rows: usize,
    tables: Vec<Region>,
}

fn export_control_tables() -> ControlTables {
    let mut driver = TableDriver::<Mersenne31Field>::new();
    cs::machine::ops::unrolled::jump_branch_slt::jump_branch_slt_table_driver_fn(&mut driver);
    let rows = driver.dump_tables();
    let mut offset = 0;
    let tables = driver
        .tables
        .iter()
        .filter(|table| table.get_size() != 0)
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
    ControlTables {
        version: 1,
        field_modulus: MODULUS,
        profile: "jump_branch_slt_fixed".into(),
        generic_rows: rows.len(),
        tables,
    }
}

fn export_small_range() -> ControlTables {
    let mut driver = TableDriver::<Mersenne31Field>::new();
    cs::machine::ops::unrolled::mul_div::mul_div_table_driver_fn(&mut driver);
    let rows = driver.dump_tables();
    let mut offset = 0;
    let tables = driver
        .tables
        .iter()
        .filter(|table| table.get_size() != 0)
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
    ControlTables {
        version: 1,
        field_modulus: MODULUS,
        profile: "unsigned_mul_div_fixed".into(),
        generic_rows: rows.len(),
        tables,
    }
}

/// The actual native zero/binary table prefix; large shifts and custom CSR
/// tables remain separate. Driver ordering supplies the native offsets/tags.
fn export_binary_prefix() -> ControlTables {
    let mut driver = TableDriver::<Mersenne31Field>::new();
    let family = cs::machine::ops::unrolled::shift_binary_csr::shift_binop_csrrw_tables();
    let selected = [TableType::ZeroEntry, TableType::Xor, TableType::Or, TableType::And];
    let mut prefix: Vec<_> = family.iter().copied().filter(|kind| (*kind as u32) < 8).collect();
    prefix.sort();
    assert_eq!(prefix.as_slice(), selected.as_slice());
    for kind in selected {
        driver.materialize_table(kind);
    }
    let rows = driver.dump_tables();
    let mut offset = 0;
    let tables = driver.tables.iter().filter(|table| table.get_size() != 0).map(|table| {
        let length = table.get_size();
        let region = Region {
            id: table.get_table_id(),
            offset,
            data: matrix(&rows[offset..offset + length]),
        };
        offset += length;
        region
    }).collect();
    assert_eq!(offset, rows.len());
    ControlTables {
        version: 1,
        field_modulus: MODULUS,
        profile: "shift_binop_binary_prefix".into(),
        generic_rows: rows.len(),
        tables,
    }
}

/// Selected actual native tables. Offsets come from the supplied compiled
/// layout, while row values/tags come only from the native table generator.
/// Each table is materialized and dropped separately to preserve headroom.
fn export_shift_scalars(layout_path: &Path) -> ControlTables {
    let layout: serde_json::Value = serde_json::from_slice(&std::fs::read(layout_path).unwrap()).unwrap();
    let family = cs::machine::ops::unrolled::shift_binary_csr::shift_binop_csrrw_tables();
    let selected = [TableType::TruncateShiftAmount, TableType::Sra16BitInputSignFill,
                    TableType::RangeCheck16WithZeroPads];
    let mut generic_rows = 0;
    let tables = selected.into_iter().map(|kind| {
        assert!(family.contains(&kind));
        let table = kind.generate_table::<Mersenne31Field>();
        let id = table.get_table_id();
        assert_eq!(id, kind as u32);
        let length = table.get_size();
        let mut rows = Vec::with_capacity(length);
        table.dump_into::<4>(&mut rows, Some(id));
        assert_eq!(rows.len(), length);
        let offset = layout["table_offsets"][id as usize].as_u64().unwrap() as usize;
        generic_rows += length;
        Region { id, offset, data: matrix(&rows) }
    }).collect();
    ControlTables { version: 1, field_modulus: MODULUS,
        profile: "shift_binop_scalar_regions".into(), generic_rows, tables }
}

fn export_decoder_padding() -> DecoderPadding {
    let row = decoder_table_padding::<Mersenne31Field>().map(|value| value.as_u64_reduced() as u32);
    assert!(row.iter().all(|&value| (value as u64) < MODULUS));
    DecoderPadding {
        version: 1,
        field_modulus: MODULUS,
        profile: "decoder_padding".into(),
        row,
    }
}

fn export_decoder(
    text: Vec<u32>,
    family: Box<dyn OpcodeFamilyDecoder>,
    profile: &str,
) -> DecoderArtifact {
    let (entries, witness) =
        preprocess_bytecode::<Mersenne31Field, Global>(&text, CAPACITY, &family, &[]);
    drop(witness);
    let rows = materialize_flattened_decoder_table(&entries);
    drop(entries);
    DecoderArtifact {
        version: 1,
        field_modulus: MODULUS,
        family: profile.into(),
        text_words: text.len(),
        text: column(text.len(), 1u64 << 32, |i| text[i]),
        decoder: matrix(&rows),
    }
}

fn export_arithmetic(text: Vec<u32>) -> DecoderArtifact {
    export_decoder(
        text,
        Box::new(AddSubLuiAuipcMopDecoder),
        "add_sub_lui_auipc_mop",
    )
}

fn export_control_decoder(text: Vec<u32>) -> DecoderArtifact {
    export_decoder(
        text,
        Box::new(JumpSltBranchDecoder::<true>),
        "jump_branch_slt_signed",
    )
}

fn export_shift_decoder(text: Vec<u32>) -> DecoderArtifact {
    export_decoder(text, Box::new(ShiftBinaryCsrrwDecoder), "shift_binop_csrrw")
}

fn export_scalars() -> Scalars {
    let range = TableType::RangeCheckLarge.generate_table::<Mersenne31Field>();
    let mut rows = Vec::new();
    range.dump_limited_columns::<1>(&mut rows);
    let range16 = matrix(&rows);
    drop(rows);
    // Unchanged generation clause from pinned prover/src/prover_stages/mod.rs.
    // Read the native constant through cs::definitions, without a prover build.
    let timestamp_range_check_table: Vec<_> = (0..(1 << TIMESTAMP_COLUMNS_NUM_BITS))
        .map(|el| Mersenne31Field(el as u32))
        .collect();
    Scalars {
        version: 1,
        field_modulus: MODULUS,
        profile: "range16_timestamp19".into(),
        range16,
        timestamp19: Matrix {
            length: timestamp_range_check_table.len(),
            columns: vec![column(timestamp_range_check_table.len(), MODULUS, |i| {
                timestamp_range_check_table[i].as_u64_reduced() as u32
            })],
        },
    }
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
    if (args.len() == 3 && args[1] == "--shift-decoder-fixture")
        || (args.len() == 4 && args[1] == "--shift-decoder")
    {
        let words = if args.len() == 3 {
            // Twelve original RV32 register/immediate forms, then their original
            // x0 destinations, and an unsupported ADD hole. No CSR is allowed.
            vec![
                0x002091b3, 0x0020d1b3, 0x4020d1b3, 0x0020c1b3, 0x0020e1b3, 0x0020f1b3, 0x01f09193,
                0x01f0d193, 0x41f0d193, 0xfff0c193, 0x8000e193, 0x7ff0f193, 0x00209033, 0x0020d033,
                0x4020d033, 0x0020c033, 0x0020e033, 0x0020f033, 0x01f09013, 0x01f0d013, 0x41f0d013,
                0xfff0c013, 0x8000e013, 0x7ff0f013, 0x001080b3,
            ]
        } else {
            read_words(Path::new(&args[2]))?
        };
        let artifact = export_shift_decoder(words);
        let bytes = serde_json::to_vec_pretty(&artifact)?;
        let recovered: DecoderArtifact = serde_json::from_slice(&bytes)?;
        assert_eq!(
            serde_json::to_value(&artifact)?,
            serde_json::to_value(recovered)?
        );
        std::fs::write(args.last().unwrap(), [bytes, vec![b'\n']].concat())?;
        return Ok(());
    }
    if args.len() == 4 && args[1] == "--shift-scalars" {
        let artifact = export_shift_scalars(Path::new(&args[2]));
        let bytes = serde_json::to_vec_pretty(&artifact)?;
        let recovered: ControlTables = serde_json::from_slice(&bytes)?;
        assert_eq!(serde_json::to_value(&artifact)?, serde_json::to_value(recovered)?);
        std::fs::write(args.last().unwrap(), [bytes, vec![b'\n']].concat())?;
        return Ok(());
    }
    if args.len() == 3 && args[1] == "--binary-prefix" {
        let artifact = export_binary_prefix();
        let bytes = serde_json::to_vec_pretty(&artifact)?;
        let recovered: ControlTables = serde_json::from_slice(&bytes)?;
        assert_eq!(
            serde_json::to_value(&artifact)?,
            serde_json::to_value(recovered)?
        );
        std::fs::write(args.last().unwrap(), [bytes, vec![b'\n']].concat())?;
        return Ok(());
    }
    if args.len() == 3 && args[1] == "--control" {
        let artifact = export_control_tables();
        let bytes = serde_json::to_vec_pretty(&artifact)?;
        let recovered: ControlTables = serde_json::from_slice(&bytes)?;
        assert_eq!(
            serde_json::to_value(&artifact)?,
            serde_json::to_value(recovered)?
        );
        std::fs::write(args.last().unwrap(), [bytes, vec![b'\n']].concat())?;
        return Ok(());
    }
    if args.len() == 3 && args[1] == "--small-range" {
        let artifact = export_small_range();
        let bytes = serde_json::to_vec_pretty(&artifact)?;
        let recovered: ControlTables = serde_json::from_slice(&bytes)?;
        assert_eq!(
            serde_json::to_value(&artifact)?,
            serde_json::to_value(recovered)?
        );
        std::fs::write(args.last().unwrap(), [bytes, vec![b'\n']].concat())?;
        return Ok(());
    }
    if args.len() == 3 && args[1] == "--decoder-padding" {
        let artifact = export_decoder_padding();
        let bytes = serde_json::to_vec_pretty(&artifact)?;
        let recovered: DecoderPadding = serde_json::from_slice(&bytes)?;
        assert_eq!(
            serde_json::to_value(&artifact)?,
            serde_json::to_value(recovered)?
        );
        std::fs::write(args.last().unwrap(), [bytes, vec![b'\n']].concat())?;
        return Ok(());
    }
    if (args.len() == 3 && args[1] == "--arithmetic-fixture")
        || (args.len() == 4 && args[1] == "--arithmetic")
    {
        let words = if args.len() == 3 {
            // ADD, signed ADDI, SUB to x0, raw U-type funct3 bits, UNIMP hole,
            // then ADD at its original PC 24. Custom modular MOPs are not tested here.
            vec![
                0x001080b3, 0xfff08113, 0x40208033, 0x000071b7, 0x00005217, 0xc0001073, 0x001080b3,
            ]
        } else {
            read_words(Path::new(&args[2]))?
        };
        let artifact = export_arithmetic(words);
        let bytes = serde_json::to_vec_pretty(&artifact)?;
        let recovered: DecoderArtifact = serde_json::from_slice(&bytes)?;
        assert_eq!(
            serde_json::to_value(&artifact)?,
            serde_json::to_value(recovered)?
        );
        std::fs::write(args.last().unwrap(), [bytes, vec![b'\n']].concat())?;
        return Ok(());
    }
    if (args.len() == 3 && args[1] == "--control-decoder-fixture")
        || (args.len() == 4 && args[1] == "--control-decoder")
    {
        let words = if args.len() == 3 {
            // Original JAL x1,-4 (raw funct3 seven), UNIMP hole, SLTIU x0,x1,-1.
            vec![0xffdff0ef, 0xc0001073, 0xfff0b013]
        } else {
            read_words(Path::new(&args[2]))?
        };
        let artifact = export_control_decoder(words);
        let bytes = serde_json::to_vec_pretty(&artifact)?;
        let recovered: DecoderArtifact = serde_json::from_slice(&bytes)?;
        assert_eq!(
            serde_json::to_value(&artifact)?,
            serde_json::to_value(recovered)?
        );
        std::fs::write(args.last().unwrap(), [bytes, vec![b'\n']].concat())?;
        return Ok(());
    }
    if args.len() == 3 && args[1] == "--scalars" {
        let artifact = export_scalars();
        let bytes = serde_json::to_vec_pretty(&artifact)?;
        let recovered: Scalars = serde_json::from_slice(&bytes)?;
        assert_eq!(
            serde_json::to_value(&artifact)?,
            serde_json::to_value(recovered)?
        );
        std::fs::write(args.last().unwrap(), [bytes, vec![b'\n']].concat())?;
        return Ok(());
    }
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
            "usage: exporter IMAGE.bin TEXT.bin OUTPUT.json | exporter --fixture OUTPUT.json | exporter --scalars OUTPUT.json | exporter --arithmetic TEXT.bin OUTPUT.json | exporter --arithmetic-fixture OUTPUT.json | exporter --decoder-padding OUTPUT.json | exporter --control OUTPUT.json | exporter --control-decoder TEXT.bin OUTPUT.json | exporter --control-decoder-fixture OUTPUT.json"
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
