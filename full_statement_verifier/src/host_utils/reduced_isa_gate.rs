//! Static reduced-machine ISA gate over every verifier guest ELF (the registered full-statement
//! verifiers, loaded digest-verified, and the per-circuit verifiers of every soundness mode). Every
//! word of every executable section is decoded with the reduced decoder; the only `Illegal` word
//! accepted is the exact `unimp` trap [`TRAP`], which refuses when reached. The gate is static: it
//! does not show which inputs reach the trap.

use super::fsv::{canonical_fsv_dir, fsv_manifest_entry, load_fsv_exact, FsvManifestEntry};
use object::{Object, ObjectSection, ObjectSymbol, SectionFlags, SymbolKind};
use riscv_transpiler::ir::simple_instruction_set::{preprocess_bytecode, InstructionName};
use riscv_transpiler::ir::ReducedMachineDecoderConfig;
use verifier_common::fsv_binaries::FSV_REGISTRY;
use verifier_common::prover::definitions::SoundnessMode;
use verifier_common::test_circuits::{SecurityLevel, CIRCUITS};

/// `unimp` (`csrrw x0, cycle, x0`), the deliberate refusing trap.
const TRAP: u32 = 0xc000_1073;

/// One executable section of a guest ELF.
struct Section {
    name: String,
    address: u64,
    words: Vec<u32>,
}

/// A guest's executable sections and its FUNC symbols as (name, address, size).
struct GuestCode {
    sections: Vec<Section>,
    functions: Vec<(String, u64, u64)>,
}

/// A word-aligned executable section with a word-multiple size.
fn section(name: &str, address: u64, data: &[u8]) -> Result<Section, String> {
    if !address.is_multiple_of(4) || !data.len().is_multiple_of(4) {
        return Err(format!(
            "MisalignedSection: {name} at {address:#x} with {} bytes",
            data.len()
        ));
    }
    let words = data
        .as_chunks::<4>()
        .0
        .iter()
        .map(|chunk| u32::from_le_bytes(*chunk))
        .collect();
    Ok(Section {
        name: name.to_owned(),
        address,
        words,
    })
}

/// Every executable (`SHF_EXECINSTR`) section of `bytes`, which must have at least one.
fn guest_code(bytes: &[u8]) -> Result<GuestCode, String> {
    let file = object::File::parse(bytes).map_err(|error| format!("Unparsable: {error}"))?;
    let mut sections = Vec::new();
    for candidate in file.sections() {
        let SectionFlags::Elf { sh_flags } = candidate.flags() else {
            return Err("NotElf".to_owned());
        };
        if sh_flags & u64::from(object::elf::SHF_EXECINSTR) == 0 {
            continue;
        }
        let name = candidate.name().map_err(|error| error.to_string())?;
        let data = candidate.data().map_err(|error| error.to_string())?;
        sections.push(section(name, candidate.address(), data)?);
    }
    if sections.is_empty() {
        return Err("NoExecutableSection".to_owned());
    }
    let functions = file
        .symbols()
        .filter(|symbol| symbol.kind() == SymbolKind::Text)
        .map(|symbol| {
            (
                symbol.name().unwrap_or("?").to_owned(),
                symbol.address(),
                symbol.size(),
            )
        })
        .collect();
    Ok(GuestCode {
        sections,
        functions,
    })
}

fn check_reduced_isa(code: &GuestCode) -> Result<(), String> {
    for section in &code.sections {
        let decoded = preprocess_bytecode::<ReducedMachineDecoderConfig, false>(&section.words);
        for (index, instruction) in decoded.iter().enumerate() {
            let word = section.words[index];
            if instruction.name != InstructionName::Illegal || word == TRAP {
                continue;
            }
            let address = section.address + 4 * index as u64;
            let owner = code
                .functions
                .iter()
                .find(|(_, start, size)| (*start..*start + *size).contains(&address))
                .map_or("?", |(name, ..)| name.as_str());
            return Err(format!(
                "Illegal: {}+{:#x} at {address:#x} {word:#010x} in {owner}",
                section.name,
                4 * index
            ));
        }
    }
    Ok(())
}

/// A registered guest's code, bound to the digest-verified guest the loader accepts.
fn registered_guest_code(entry: &FsvManifestEntry) -> GuestCode {
    let verified = load_fsv_exact(canonical_fsv_dir(), &entry.descriptor);
    let bytes = std::fs::read(canonical_fsv_dir().join(entry.relative_path)).unwrap();
    let code = guest_code(&bytes).unwrap_or_else(|error| panic!("{}: {error}", entry.descriptor));
    let text = code
        .sections
        .iter()
        .find(|section| section.name == ".text")
        .unwrap_or_else(|| panic!("{}: no .text section", entry.descriptor));
    assert_eq!(
        4 * text.words.len(),
        entry.text_bytes,
        "{}: raw .text length differs from the manifest",
        entry.descriptor
    );
    assert_eq!(
        &verified.text()[..text.words.len()],
        &text.words[..],
        "{}: raw .text differs from the verified guest",
        entry.descriptor
    );
    code
}

/// The committed per-circuit verifier ELFs of every soundness mode, as listed by
/// `verifier_common::test_circuits`.
fn per_circuit_verifier_paths() -> Vec<String> {
    SoundnessMode::ALL
        .iter()
        .flat_map(|&mode| {
            CIRCUITS
                .iter()
                .map(move |circuit| circuit.elf_path_for_mode(SecurityLevel::Sec100, mode))
        })
        .collect()
}

#[test]
fn every_registered_guest_passes_the_reduced_isa_gate() {
    assert!(!FSV_REGISTRY.is_empty());
    for registered in FSV_REGISTRY {
        let code = registered_guest_code(fsv_manifest_entry(&registered.descriptor));
        check_reduced_isa(&code)
            .unwrap_or_else(|error| panic!("{}: {error}", registered.descriptor));
    }
}

#[test]
fn every_per_circuit_verifier_passes_the_reduced_isa_gate() {
    let paths = per_circuit_verifier_paths();
    assert_eq!(paths.len(), CIRCUITS.len() * SoundnessMode::ALL.len());
    assert!(!paths.is_empty());
    // The listing must name every committed per-circuit ELF exactly once, so a missing or
    // duplicated entry cannot skip a guest.
    let listed: std::collections::BTreeSet<std::path::PathBuf> = paths
        .iter()
        .map(|path| std::fs::canonicalize(path).unwrap_or_else(|error| panic!("{path}: {error}")))
        .collect();
    assert_eq!(
        listed.len(),
        paths.len(),
        "duplicate per-circuit verifier paths"
    );
    let mut committed = std::collections::BTreeSet::new();
    for &mode in SoundnessMode::ALL {
        let directory = std::path::Path::new(&paths[0])
            .parent()
            .and_then(|mode_directory| mode_directory.parent())
            .unwrap()
            .join(verifier_common::test_circuits::verifier_dir_name(mode));
        for entry in std::fs::read_dir(&directory).unwrap() {
            let path = entry.unwrap().path();
            if path.extension().is_some_and(|extension| extension == "elf") {
                committed.insert(std::fs::canonicalize(path).unwrap());
            }
        }
    }
    assert_eq!(
        listed, committed,
        "listed per-circuit verifiers differ from the committed ELF set"
    );
    for path in &paths {
        let bytes = std::fs::read(path).unwrap_or_else(|error| panic!("{path}: {error}"));
        let code = guest_code(&bytes).unwrap_or_else(|error| panic!("{path}: {error}"));
        check_reduced_isa(&code).unwrap_or_else(|error| panic!("{path}: {error}"));
    }
}

/// Synthetic code for the gate's own tests, independent of the committed guests: four `nop`s
/// (`addi x0, x0, 0`) in one function.
fn fixture() -> GuestCode {
    GuestCode {
        sections: vec![Section {
            name: ".text".to_owned(),
            address: 0,
            words: vec![0x0000_0013; 4],
        }],
        functions: vec![("f".to_owned(), 0, 16)],
    }
}

fn decodes_illegal(word: u32) -> bool {
    preprocess_bytecode::<ReducedMachineDecoderConfig, false>(&[word])[0].name
        == InstructionName::Illegal
}

/// The fixture with its first word replaced by `word`.
fn with_first_word(word: u32) -> GuestCode {
    let mut code = fixture();
    assert!(!decodes_illegal(code.sections[0].words[0]));
    code.sections[0].words[0] = word;
    code
}

#[test]
fn exact_trap_is_accepted() {
    assert!(decodes_illegal(TRAP));
    check_reduced_isa(&with_first_word(TRAP)).unwrap();
}

#[test]
fn every_byte_and_halfword_access_is_refused() {
    // rd/rs2 = a0, rs1 = a1, offset 0.
    for (name, word) in [
        ("lb", 0x0005_8503),
        ("lh", 0x0005_9503),
        ("lbu", 0x0005_c503),
        ("lhu", 0x0005_d503),
        ("sb", 0x00a5_8023),
        ("sh", 0x00a5_9023),
    ] {
        assert!(decodes_illegal(word), "{name}");
        let error = check_reduced_isa(&with_first_word(word)).expect_err(name);
        assert!(
            error.starts_with("Illegal: .text+0x0 at "),
            "{name}: {error}"
        );
        assert!(error.contains(&format!("{word:#010x}")), "{name}: {error}");
    }
}

#[test]
fn other_illegal_word_is_refused() {
    // `csrrs x0, time, x0`: an Illegal CSR access that is not the `unimp` trap.
    let word = 0xc010_2073;
    assert!(decodes_illegal(word) && word != TRAP);
    assert!(check_reduced_isa(&with_first_word(word))
        .expect_err("the gate must refuse")
        .starts_with("Illegal: "));
}

#[test]
fn misaligned_executable_section_is_refused() {
    assert!(section(".text", 2, &[0; 8])
        .err()
        .unwrap()
        .starts_with("MisalignedSection: "));
    assert!(section(".text", 0, &[0; 6])
        .err()
        .unwrap()
        .starts_with("MisalignedSection: "));
}
