//! RISCOF (RISC-V Compliance Framework) integration for running compliance tests.

use std::path::Path;

use object::{Object, ObjectSymbol};

use crate::ir::{preprocess_bytecode, FullMachineDecoderConfig, Instruction};
use crate::vm::{DelegationsCounters, RamPeek, RamWithRomRegion, Register, SimpleTape, State, VM};

/// Default entry point for RISCOF tests.
pub const DEFAULT_ENTRY_POINT: u32 = 0x0100_0000;

const ROM_SECOND_WORD_BITS: usize = common_constants::rom::ROM_SECOND_WORD_BITS;
const MEMORY_SIZE: usize = 1 << 30;

/// Run a RISCOF compliance test binary and extract signatures to the given path.
pub fn run_with_riscof_signature_extraction(
    binary: &[u8],
    elf_data: &[u8],
    signature_path: &Path,
    max_cycles: usize,
    entry_point: u32,
) {
    let ram = execute_binary(binary, max_cycles, entry_point);

    match find_signature_bounds(elf_data) {
        Some((begin, end)) => {
            let signatures = collect_signatures(&ram, begin, end);
            write_signatures(&signatures, signature_path);
        }
        None => {
            use std::io::Write;
            let mut file =
                std::fs::File::create(signature_path).expect("must create signature file");
            writeln!(file, "begin_signature or end_signature symbol not found in ELF")
                .expect("must write to signature file");
        }
    }
}

fn execute_binary(
    binary: &[u8],
    max_cycles: usize,
    entry_point: u32,
) -> RamWithRomRegion<ROM_SECOND_WORD_BITS> {
    let binary_words = bytes_to_words(binary);
    let entry_offset = (entry_point / 4) as usize;
    let total_words = entry_offset + binary_words.len();

    let mut padded_instructions = vec![0u32; total_words];
    padded_instructions[entry_offset..].copy_from_slice(&binary_words);

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullMachineDecoderConfig>(&padded_instructions);
    let tape = SimpleTape::new(&instructions);

    let ram_words = MEMORY_SIZE / core::mem::size_of::<u32>();
    let mut backing = vec![
        Register {
            value: 0,
            timestamp: 0
        };
        ram_words
    ];
    for (i, &word) in binary_words.iter().enumerate() {
        backing[entry_offset + i].value = word;
    }
    let mut ram = RamWithRomRegion::<ROM_SECOND_WORD_BITS> { backing };

    let mut state = State::initial_with_counters(DelegationsCounters::default());
    state.pc = entry_point;

    VM::<DelegationsCounters>::run_basic_unrolled(
        &mut state,
        &mut ram,
        &mut (),
        &tape,
        max_cycles,
        &mut (),
    );

    ram
}

fn bytes_to_words(bytes: &[u8]) -> Vec<u32> {
    let padded_len = (bytes.len() + 3) / 4 * 4;
    let mut padded = bytes.to_vec();
    padded.resize(padded_len, 0);

    padded
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect()
}

fn find_signature_bounds(elf_data: &[u8]) -> Option<(u64, u64)> {
    let elf = object::File::parse(elf_data).expect("must parse ELF file");

    let mut begin = None;
    let mut end = None;

    for symbol in elf.symbols() {
        if let Ok(name) = symbol.name() {
            if name == "begin_signature" {
                begin = Some(symbol.address());
            } else if name == "end_signature" {
                end = Some(symbol.address());
            }
            if begin.is_some() && end.is_some() {
                break;
            }
        }
    }

    match (begin, end) {
        (Some(b), Some(e)) => Some((b, e)),
        _ => None,
    }
}

fn collect_signatures(
    ram: &RamWithRomRegion<ROM_SECOND_WORD_BITS>,
    begin: u64,
    end: u64,
) -> Vec<u32> {
    assert!(begin <= end, "begin_signature > end_signature");
    assert!(begin % 4 == 0, "begin_signature not 4-byte aligned");
    assert!(end % 4 == 0, "end_signature not 4-byte aligned");

    let word_count = ((end - begin) / 4) as usize;
    let mut signatures = Vec::with_capacity(word_count);

    let mut addr = begin as u32;
    let end_addr = end as u32;

    while addr < end_addr {
        let word = ram.peek_word(addr);
        signatures.push(word);
        addr += 4;
    }

    signatures
}

fn write_signatures(signatures: &[u32], path: &Path) {
    use std::io::Write;

    let mut file = std::fs::File::create(path).expect("must create signature file");

    for &sig in signatures {
        writeln!(file, "{:08x}", sig).expect("must write to signature file");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_write_signatures() {
        use std::io::Read;

        let signatures = vec![0xdeadbeef, 0x12345678, 0x00000001];
        let temp_dir = std::env::temp_dir();
        let path = temp_dir.join("test_signatures.txt");

        write_signatures(&signatures, &path);

        let mut content = String::new();
        std::fs::File::open(&path)
            .expect("open should succeed")
            .read_to_string(&mut content)
            .expect("read should succeed");

        assert_eq!(content, "deadbeef\n12345678\n00000001\n");

        std::fs::remove_file(&path).ok();
    }
}
