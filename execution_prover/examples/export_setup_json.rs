#![feature(allocator_api)]

//! Export one actual native setup, with its circuit and selected program inputs.
//!
//! Usage: export_setup_json FAMILY IMAGE.bin TEXT.bin OUTPUT.json [--cached] [--reduced]
//! Files contain little-endian u32 words; both input slices are padded exactly
//! as for proving. Delegation families ignore the program arguments (use `-`).

use common_constants::ROM_WORD_SIZE;
use cs::gkr_circuits::{
    opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization,
    opcodes_for_reduced_machine, process_binary_into_separate_tables_ext,
};
use execution_prover::setup::CanonicalCircuitSetup;
use execution_prover_model::MachineType;
use execution_prover_model::circuit_type::{
    DelegationCircuitType as D, UnrolledCircuitType as U, UnrolledMemoryCircuitType as M,
    UnrolledNonMemoryCircuitType as N,
};
use field::baby_bear::base::BabyBearField as BF;
use prover::gkr::prover::setup_artifact::SetupProgram;
use riscv_transpiler::ir::{FullUnsignedMachineDecoderConfig, ReducedMachineDecoderConfig};
use setups::circuits::{
    get_bigint_with_control_circuit_setup, get_blake2_g_function_circuit_setup,
    get_blake2_with_compression_circuit_setup, get_keccak_special5_circuit_setup,
};
use setups::unrolled_circuits::{
    add_sub_lui_auipc_mop_circuit_setup, jump_branch_slt_circuit_setup,
    load_store_subword_only_circuit_setup, load_store_word_only_circuit_setup,
    mul_div_unsigned_circuit_setup, shift_binary_circuit_setup,
    unified_reduced_machine_circuit_setup,
};
use std::alloc::Global;
use std::io::{self, BufWriter, Write};
use worker::Worker;

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

/// Select the circuit representation when exporting materialized setup.
fn build_delegation_setup_with_cache_mode(
    delegation_type: D,
    use_caches: bool,
    worker: &Worker,
) -> CanonicalCircuitSetup {
    // The split-Keccak delegation variants (column parity, theta/rho, chi5) are not in this
    // tree; the export of blake-round and the Keccak special5 circuit does not need them.
    let setup = match delegation_type {
        D::BigIntWithControl => get_bigint_with_control_circuit_setup(use_caches, worker),
        D::Blake2WithCompression => get_blake2_with_compression_circuit_setup(use_caches, worker),
        D::Blake2GFunction => get_blake2_g_function_circuit_setup(use_caches, worker),
        D::KeccakSpecial5 => get_keccak_special5_circuit_setup(use_caches, worker),
    };
    CanonicalCircuitSetup::Delegation(setup)
}

/// Explicit cache mode local to this artifact export binary.
fn build_unrolled_setup_with_cache_mode(
    machine_type: MachineType,
    circuit_type: U,
    binary_image: &[u32],
    text_section: &[u32],
    use_caches: bool,
    worker: &Worker,
) -> CanonicalCircuitSetup {
    let family_idx = match circuit_type {
        U::Memory(c) => c.get_family_idx(),
        U::NonMemory(c) => c.get_family_idx(),
        U::Unified => {
            return CanonicalCircuitSetup::Riscv(unified_reduced_machine_circuit_setup::<Global>(
                binary_image,
                text_section,
                use_caches,
                worker,
            ));
        }
        U::InitsAndTeardowns => {
            panic!("inits-and-teardowns is binary-independent and is set up as a common circuit")
        }
    };
    let supported_csrs: Vec<u16> = D::get_delegation_types_for_machine_type(machine_type)
        .iter()
        .map(D::get_delegation_type_id)
        .collect();
    let preprocessing = match machine_type {
        MachineType::Full | MachineType::FullUnsigned => {
            process_binary_into_separate_tables_ext::<BF, FullUnsignedMachineDecoderConfig, true, Global>(
                text_section,
                &opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(),
                ROM_WORD_SIZE,
                &supported_csrs,
            )
        }
        MachineType::Reduced => {
            process_binary_into_separate_tables_ext::<BF, ReducedMachineDecoderConfig, true, Global>(
                text_section,
                &opcodes_for_reduced_machine(),
                ROM_WORD_SIZE,
                &supported_csrs,
            )
        }
    };
    let table_data = preprocessing
        .get(&family_idx)
        .expect("missing decoder data for circuit family")
        .clone();

    let setup = match circuit_type {
        U::Memory(M::LoadStoreWordOnly) => load_store_word_only_circuit_setup::<Global>(
            &table_data,
            binary_image,
            use_caches,
            worker,
        ),
        U::Memory(M::LoadStoreSubwordOnly) => load_store_subword_only_circuit_setup::<Global>(
            &table_data,
            binary_image,
            use_caches,
            worker,
        ),
        U::NonMemory(N::AddSubLuiAuipcMop) => {
            add_sub_lui_auipc_mop_circuit_setup::<Global>(&table_data, use_caches, worker)
        }
        U::NonMemory(N::JumpBranchSlt) => {
            jump_branch_slt_circuit_setup::<Global>(&table_data, use_caches, worker)
        }
        U::NonMemory(N::ShiftBinary) => {
            shift_binary_circuit_setup::<Global>(&table_data, use_caches, worker)
        }
        U::NonMemory(N::MulDivUnsigned) => {
            mul_div_unsigned_circuit_setup::<Global>(&table_data, use_caches, worker)
        }
        U::InitsAndTeardowns | U::Unified => unreachable!(),
    };
    CanonicalCircuitSetup::Riscv(setup)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if !(4..=6).contains(&args.len()) {
        return Err(
            "usage: export_setup_json FAMILY IMAGE.bin TEXT.bin OUTPUT.json [--cached] [--reduced]"
                .into(),
        );
    }
    let mut use_caches = false;
    let mut reduced = false;
    for flag in &args[4..] {
        match flag.as_str() {
            "--cached" if !use_caches => use_caches = true,
            "--reduced" if !reduced => reduced = true,
            _ => return Err("unknown or duplicate setup export option".into()),
        }
    }
    let worker = worker::Worker::new();
    let delegation = match args[0].as_str() {
        "bigint" => Some(D::BigIntWithControl),
        "blake-g" => Some(D::Blake2GFunction),
        "blake-round" => Some(D::Blake2WithCompression),
        "keccak" => Some(D::KeccakSpecial5),
        _ => None,
    };
    let (setup, program) = if args[0] == "inits-and-teardowns" {
        if reduced {
            return Err("--reduced applies only to the four shared unrolled CPU families".into());
        }
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
        if reduced {
            return Err("--reduced applies only to the four shared unrolled CPU families".into());
        }
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
        if reduced
            && (family == U::Unified
                || family == U::NonMemory(N::MulDivUnsigned)
                || family == U::Memory(M::LoadStoreSubwordOnly))
        {
            return Err("--reduced applies only to the four shared unrolled CPU families".into());
        }
        let image = read_words(&args[1])?;
        let text = read_words(&args[2])?;
        let machine = if reduced || family == U::Unified {
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
