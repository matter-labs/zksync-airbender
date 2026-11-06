//! Static reduced-machine ISA gate over registered full-statement verifier ELFs.

use super::canonical_fsv_dir;
use object::{Object, ObjectSection, SectionFlags};
use riscv_transpiler::ir::simple_instruction_set::{preprocess_bytecode, InstructionName};
use riscv_transpiler::ir::ReducedMachineDecoderConfig;
use verifier_common::fsv_binaries::FSV_REGISTRY;

/// `unimp` (`csrrw x0, cycle, x0`), the deliberate refusing trap.
const TRAP: u32 = 0xc000_1073;

struct Section {
    name: String,
    address: u64,
    words: Vec<u32>,
}

fn section(name: &str, address: u64, data: &[u8]) -> Section {
    assert!(
        address.is_multiple_of(4) && data.len().is_multiple_of(4),
        "misaligned executable section {name} at {address:#x} with {} bytes",
        data.len()
    );
    Section {
        name: name.to_owned(),
        address,
        words: data
            .as_chunks::<4>()
            .0
            .iter()
            .map(|chunk| u32::from_le_bytes(*chunk))
            .collect(),
    }
}

fn executable_sections(bytes: &[u8]) -> Vec<Section> {
    let file = object::File::parse(bytes).expect("parse guest ELF");
    let mut sections = Vec::new();
    for candidate in file.sections() {
        let SectionFlags::Elf { sh_flags } = candidate.flags() else {
            panic!("guest is not an ELF");
        };
        if sh_flags & u64::from(object::elf::SHF_EXECINSTR) != 0 {
            sections.push(section(
                candidate.name().unwrap(),
                candidate.address(),
                candidate.data().unwrap(),
            ));
        }
    }
    assert!(!sections.is_empty(), "no executable section");
    sections
}

fn check_reduced_isa(sections: &[Section]) {
    for section in sections {
        let decoded = preprocess_bytecode::<ReducedMachineDecoderConfig, false>(&section.words);
        for (index, instruction) in decoded.iter().enumerate() {
            let word = section.words[index];
            assert!(
                instruction.name != InstructionName::Illegal || word == TRAP,
                "illegal instruction in {}+{:#x} at {:#x}: {word:#010x}",
                section.name,
                4 * index,
                section.address + 4 * index as u64
            );
        }
    }
}

#[test]
fn every_registered_guest_passes_the_reduced_isa_gate() {
    for registered in FSV_REGISTRY {
        let path = canonical_fsv_dir().join(registered.descriptor.relative_path());
        let bytes =
            std::fs::read(&path).unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        check_reduced_isa(&executable_sections(&bytes));
    }
}

fn code_with(word: u32) -> Vec<Section> {
    vec![section(".text", 0, &word.to_le_bytes())]
}

#[test]
fn exact_trap_is_accepted() {
    assert_eq!(
        preprocess_bytecode::<ReducedMachineDecoderConfig, false>(&[TRAP])[0].name,
        InstructionName::Illegal
    );
    check_reduced_isa(&code_with(TRAP));
}

#[test]
#[should_panic(expected = "illegal instruction in .text")]
fn illegal_word_is_refused() {
    // `csrrs x0, time, x0` is an illegal CSR access distinct from the trap.
    check_reduced_isa(&code_with(0xc010_2073));
}

#[test]
#[should_panic(expected = "misaligned executable section")]
fn misaligned_executable_section_is_refused() {
    section(".text", 2, &[0; 8]);
}
