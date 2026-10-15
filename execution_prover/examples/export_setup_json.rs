#![feature(allocator_api)]

//! Export one actual native setup, with its circuit and selected program inputs.
//!
//! Usage: export_setup_json FAMILY IMAGE.bin TEXT.bin OUTPUT.json [--cached]
//! Files contain little-endian u32 words; both input slices are padded exactly
//! as for proving. Delegation families ignore the program arguments (use `-`).

use execution_prover::setup::{
    build_delegation_setup_with_cache_mode, build_unrolled_setup_with_cache_mode,
    CanonicalCircuitSetup,
};
use execution_prover_model::circuit_type::{
    DelegationCircuitType as D, UnrolledCircuitType as U, UnrolledMemoryCircuitType as M,
    UnrolledNonMemoryCircuitType as N,
};
use execution_prover_model::MachineType;
use prover::gkr::prover::setup_artifact::SetupProgram;
use std::io::{self, BufWriter, Write};

fn read_words(path: &str) -> io::Result<Vec<u32>> {
    let bytes = std::fs::read(path)?;
    if bytes.len() % 4 != 0 || bytes.len() > common_constants::ROM_BYTE_SIZE {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "program must contain complete u32 words within the ROM domain",
        ));
    }
    let mut words: Vec<u32> = bytes
        .chunks_exact(4)
        .map(|bytes| u32::from_le_bytes(bytes.try_into().unwrap()))
        .collect();
    setups::pad_bytecode_for_proving(&mut words);
    Ok(words)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if !(args.len() == 4 || (args.len() == 5 && args[4] == "--cached")) {
        return Err(
            "usage: export_setup_json FAMILY IMAGE.bin TEXT.bin OUTPUT.json [--cached]".into(),
        );
    }
    let use_caches = args.len() == 5;
    let worker = worker::Worker::new();
    let delegation = match args[0].as_str() {
        "bigint" => Some(D::BigIntWithControl),
        "blake-g" => Some(D::Blake2GFunction),
        "blake-round" => Some(D::Blake2WithCompression),
        "keccak" => Some(D::KeccakSpecial5),
        _ => None,
    };
    let (setup, program) = if args[0] == "inits-and-teardowns" {
        if args[1] != "-" || args[2] != "-" {
            return Err(
                "program-independent initialization setup expects '-' for both program files"
                    .into(),
            );
        }
        (
            CanonicalCircuitSetup::Riscv(setups::inits_and_teardowns_circuit_setup::<
                std::alloc::Global,
            >(use_caches, &worker)),
            None,
        )
    } else if let Some(family) = delegation {
        if args[1] != "-" || args[2] != "-" {
            return Err(
                "program-independent delegation setup expects '-' for both program files".into(),
            );
        }
        (
            build_delegation_setup_with_cache_mode(family, use_caches, &worker),
            None,
        )
    } else {
        let family = match args[0].as_str() {
            "add-sub" => U::NonMemory(N::AddSubLuiAuipcMop),
            "jump-branch" => U::NonMemory(N::JumpBranchSlt),
            "mul-div" => U::NonMemory(N::MulDivUnsigned),
            "shift-binop" => U::NonMemory(N::ShiftBinary),
            "word-memory" => U::Memory(M::LoadStoreWordOnly),
            "subword-memory" => U::Memory(M::LoadStoreSubwordOnly),
            "unified" => U::Unified,
            _ => return Err("unknown setup family".into()),
        };
        let image = read_words(&args[1])?;
        let text = read_words(&args[2])?;
        let machine = if family == U::Unified {
            MachineType::Reduced
        } else {
            MachineType::FullUnsigned
        };
        let setup = build_unrolled_setup_with_cache_mode(
            machine, family, &image, &text, use_caches, &worker,
        );
        (setup, Some(SetupProgram::new(&image, &text)))
    };
    let mut writer = BufWriter::new(std::fs::File::create(&args[3])?);
    let result = match &setup {
        CanonicalCircuitSetup::Riscv(setup) => setup.setup.write_artifact_json(
            &mut writer,
            &setup.compiled_circuit,
            &setup.table_driver,
            program,
        ),
        CanonicalCircuitSetup::Delegation(setup) => setup.setup.write_artifact_json(
            &mut writer,
            &setup.compiled_circuit,
            &setup.table_driver,
            program,
        ),
    };
    result.map_err(io::Error::other)?;
    writer.flush()?;
    println!("Wrote complete setup JSON to {}", args[3]);
    Ok(())
}
