use super::*;
use crate::ir::simple_instruction_set::{preprocess_bytecode, Instruction};
use crate::ir::FullUnsignedMachineDecoderConfig;
use crate::vm::{DelegationsCounters, RamPeek, RamWithRomRegion, SimpleTape, State, VM};
use common_constants::rom::ROM_SECOND_WORD_BITS;
use field::Mersenne31Field;
use std::path::PathBuf;

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..")
}

/// Directories holding the `<stem>.elf` / `<stem>.bin` / `<stem>.text` triples written by the
/// `dump_bin.sh` scripts.
fn artifact_dirs() -> Vec<PathBuf> {
    let root = repo_root();
    let mut dirs = vec![root.join("tools/gkr_verifier")];
    for base in [
        root.join("examples"),
        root.join("riscv_transpiler/examples"),
    ] {
        for entry in std::fs::read_dir(&base).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                dirs.push(path);
            }
        }
    }
    dirs
}

/// Every committed `.elf` under the artifact directories.
fn elf_files() -> Vec<PathBuf> {
    let mut files = Vec::new();
    for dir in artifact_dirs() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries {
            let path = entry.unwrap().path();
            if path.extension().and_then(|ext| ext.to_str()) == Some("elf") {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

/// Every committed ELF next to its `objcopy -O binary` and `--only-section=.text` dumps
/// (programs committed as pre-built dumps; their ELFs may lack `.text`).
fn dump_triples() -> Vec<(PathBuf, PathBuf, PathBuf)> {
    elf_files()
        .into_iter()
        .filter_map(|elf| {
            let bin = elf.with_extension("bin");
            let text = elf.with_extension("text");
            (bin.is_file() && text.is_file()).then_some((elf, bin, text))
        })
        .collect()
}

fn is_stripped_text(err: &ElfReadError) -> bool {
    matches!(err, ElfReadError::Layout(msg) if msg.starts_with("no .text section"))
}

/// Committed ELFs that still carry `.text` (the `tools/gkr_verifier` set), parsed in `mode`.
/// ELFs produced by the old `objcopy -R .text` recipe are skipped.
fn full_elf_images(mode: ElfReadMode) -> Vec<(PathBuf, ElfImage)> {
    let mut images = Vec::new();
    for path in elf_files() {
        let bytes = std::fs::read(&path).unwrap();
        match read_elf(&bytes, mode) {
            Ok(image) => images.push((path, image)),
            Err(err) if is_stripped_text(&err) => println!(
                "skipped (no .text, built with `objcopy -R .text`): {}",
                path.display()
            ),
            Err(err) => panic!("{}: {err}", path.display()),
        }
    }
    images
}

/// `llvm-objcopy` from the active toolchain's `llvm-tools` component, if installed.
fn llvm_objcopy() -> Option<PathBuf> {
    let sysroot = std::process::Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .ok()
        .filter(|out| out.status.success())?;
    let sysroot = PathBuf::from(String::from_utf8(sysroot.stdout).ok()?.trim());
    for target in std::fs::read_dir(sysroot.join("lib/rustlib")).ok()? {
        let candidate = target.ok()?.path().join("bin/llvm-objcopy");
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

fn run_objcopy(objcopy: &Path, elf: &Path, out: &Path, extra: &[&str]) -> Vec<u8> {
    let status = std::process::Command::new(objcopy)
        .args(["-O", "binary"])
        .args(extra)
        .arg(elf)
        .arg(out)
        .status()
        .expect("spawn llvm-objcopy");
    assert!(status.success(), "llvm-objcopy failed on {}", elf.display());
    std::fs::read(out).unwrap()
}

/// Legacy mode must reproduce, byte for byte, the flat ROM images (`objcopy -O binary`) and
/// text section dumps (`objcopy -O binary --only-section=.text`) committed next to ELF files.
///
/// Today every committed dump pair sits next to an ELF produced by the old `objcopy -R .text`
/// recipe (no text), so those are reported as skipped; regenerating such an ELF with its
/// `dump_bin.sh` puts it under this check. The ELF-only verifier set is covered by
/// `legacy_mode_matches_llvm_objcopy` instead.
#[test]
fn legacy_mode_reproduces_committed_objcopy_dumps() {
    let mut checked = Vec::new();
    let mut stripped = Vec::new();
    for (elf_path, bin_path, text_path) in dump_triples() {
        let bytes = std::fs::read(&elf_path).unwrap();
        let image = match read_elf(&bytes, ElfReadMode::Legacy) {
            Ok(image) => image,
            Err(err) if is_stripped_text(&err) => {
                stripped.push(elf_path);
                continue;
            }
            Err(err) => panic!("{}: {err}", elf_path.display()),
        };
        let expected_bin = std::fs::read(&bin_path).unwrap();
        let expected_text = std::fs::read(&text_path).unwrap();

        assert!(
            image.text_bytes() == expected_text,
            "{}: .text differs from {}",
            elf_path.display(),
            text_path.display()
        );
        assert_eq!(
            image.flattened_binary_used_bytes,
            expected_bin.len(),
            "{}: flat image length differs from {}",
            elf_path.display(),
            bin_path.display()
        );
        assert!(
            image.objcopy_binary().unwrap() == expected_bin,
            "{}: flat image differs from {}",
            elf_path.display(),
            bin_path.display()
        );
        let flattened = image.flattened_binary.as_ref().unwrap();
        assert_eq!(flattened.len(), ROM_WORD_SIZE);
        assert!(flattened[image.flattened_binary_used_bytes / 4..]
            .iter()
            .all(|word| *word == 0));

        // Word views agree with what the raw readers (+ `pad_bytecode_for_proving`) produced.
        assert_eq!(image.text, bytes_to_words(&expected_text));
        let mut padded_text_words = bytes_to_words(&expected_text);
        padded_text_words.resize(ROM_WORD_SIZE, 0);
        assert_eq!(image.padded_text_words(), padded_text_words);
        let mut padded_bin_words = bytes_to_words(&expected_bin);
        padded_bin_words.resize(ROM_WORD_SIZE, 0);
        assert_eq!(*flattened, padded_bin_words);
        assert_eq!(
            image.objcopy_binary_words().unwrap(),
            &padded_bin_words[..expected_bin.len() / 4]
        );
        assert_eq!(
            load_legacy_program(&elf_path),
            (padded_bin_words, padded_text_words)
        );

        checked.push(elf_path);
    }

    for path in stripped.iter() {
        println!(
            "skipped (no .text, built with `objcopy -R .text`): {}",
            path.display()
        );
    }
    for path in checked.iter() {
        println!("matches committed dumps: {}", path.display());
    }
}

/// Legacy mode must produce exactly what `llvm-objcopy -O binary` (flat ROM image) and
/// `llvm-objcopy -O binary --only-section=.text` (text section) emit for every committed ELF
/// that carries its text. This replaces the committed dumps the verifier set used to ship.
/// Runs only when the toolchain's `llvm-tools` component is installed.
#[test]
fn legacy_mode_matches_llvm_objcopy() {
    let Some(objcopy) = llvm_objcopy() else {
        println!("llvm-objcopy not found (rustup component add llvm-tools); skipping");
        return;
    };
    let dir = std::env::temp_dir().join(format!("airbender_objcopy_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let mut checked = 0;
    for (elf_path, image) in full_elf_images(ElfReadMode::Legacy) {
        let bin = run_objcopy(&objcopy, &elf_path, &dir.join("app.bin"), &[]);
        let text = run_objcopy(
            &objcopy,
            &elf_path,
            &dir.join("app.text"),
            &["--only-section=.text"],
        );
        assert!(
            image.objcopy_binary().unwrap() == bin,
            "{}: flat image differs from llvm-objcopy",
            elf_path.display()
        );
        assert!(
            image.text_bytes() == text,
            "{}: .text differs from llvm-objcopy",
            elf_path.display()
        );
        println!("matches llvm-objcopy: {}", elf_path.display());
        checked += 1;
    }
    std::fs::remove_dir_all(&dir).unwrap();
    assert!(
        checked > 0,
        "no ELF with a .text section found under the artifact directories"
    );
}

/// Strict mode on the relocating layout (`riscv_common/src/lds`): no ROM image, `.rodata` /
/// `.data` reported as virtual init data equal to what the legacy ROM image holds at their LMA,
/// and the materialization code fills RAM with exactly that content.
#[test]
fn strict_mode_reports_virtual_init_data() {
    let mut checked = 0;
    for (elf_path, legacy) in full_elf_images(ElfReadMode::Legacy) {
        let bytes = std::fs::read(&elf_path).unwrap();
        let strict = match read_elf(&bytes, ElfReadMode::Strict) {
            Ok(image) => image,
            Err(ElfReadError::Layout(msg)) => {
                // Layouts that keep .rodata inside ROM (examples/scripts/lds) are legacy-only.
                assert!(
                    msg.contains("inside the ROM"),
                    "{}: {msg}",
                    elf_path.display()
                );
                assert!(legacy
                    .init_sections
                    .iter()
                    .any(|section| !section.is_relocated() && section.size() > 0));
                continue;
            }
            Err(err) => panic!("{}: {err}", elf_path.display()),
        };
        assert!(strict.flattened_binary.is_none());
        assert_eq!(strict.text, legacy.text);
        assert_eq!(strict.init_sections, legacy.init_sections);
        assert_eq!(
            strict.flattened_binary_used_bytes,
            legacy.flattened_binary_used_bytes
        );

        let flat = legacy.objcopy_binary().unwrap();
        for section in strict.init_sections.iter() {
            if section.size() == 0 {
                // Empty sections have no image in the ROM (their LMA may even lie past its end).
                continue;
            }
            assert!(section.is_relocated());
            assert!(section.virtual_address as usize >= ROM_BYTE_SIZE);
            let lma = section.load_address as usize;
            assert_eq!(
                &flat[lma..lma + section.data.len()],
                &section.data[..],
                "{}: {} init image differs from the ROM image",
                elf_path.display(),
                section.name
            );
        }

        let code = strict.init_data_materialization_code();
        assert_init_code_fills_ram(&code, &strict.init_sections);
        checked += 1;
    }
    println!("strict mode checked on {checked} ELF files");
    assert!(
        checked > 0,
        "no ELF with a .text section found under the artifact directories"
    );
}

/// Run `code` (RV32I words at address 0) on the VM for exactly `code.len()` cycles and check
/// that every init section is in RAM afterwards and nothing else changed.
fn assert_init_code_fills_ram(code: &[u32], init_sections: &[InitDataSection]) {
    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(code);
    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<ROM_SECOND_WORD_BITS>::from_rom_content(code, 1 << 30);
    let mut state = State::initial_with_counters(DelegationsCounters::default());
    let finished = VM::<DelegationsCounters>::run_basic_unrolled::<_, _, _, Mersenne31Field>(
        &mut state,
        &mut ram,
        &mut (),
        &tape,
        code.len(),
        &mut (),
    );
    assert!(!finished);
    assert_eq!(state.pc as usize, code.len() * 4);

    for section in init_sections {
        for (i, word) in section.words().iter().enumerate() {
            let address = section.virtual_address + 4 * i as u32;
            assert_eq!(
                ram.peek_word(address),
                *word,
                "{} word at {address:#x}",
                section.name
            );
        }
        // Guard words around the section stay zero.
        if section.virtual_address >= ROM_BYTE_SIZE as u32 + 4 {
            assert_eq!(ram.peek_word(section.virtual_address - 4), 0);
        }
        assert_eq!(ram.peek_word(section.end_address()), 0);
    }
    // Only t0/t1 were used.
    for (i, register) in state.registers.iter().enumerate() {
        if i != REG_BASE as usize && i != REG_VALUE as usize {
            assert_eq!(register.value, 0, "register x{i} clobbered");
        }
    }
}

#[test]
fn materialization_code_covers_immediate_edge_cases() {
    // Values exercising every `lui`/`addi` split: small positive/negative immediates, values
    // with zero low bits, values whose low 12 bits are >= 0x800 (negative `addi` carry), the
    // extremes, and zero words that must be skipped. Spans several 4 KiB store windows and
    // starts off a window boundary.
    let mut words = vec![
        0,
        1,
        0x7ff,
        0x800,
        0xfff,
        0x1000,
        0x1800,
        0xffff_ffff,
        0xffff_f800,
        0xffff_f7ff,
        0x8000_0000,
        0x7fff_ffff,
        0x1234_5fff,
        0xdead_beef,
        0,
    ];
    let mut state = 0x9e37_79b9u32;
    for _ in 0..1500 {
        state ^= state << 13;
        state ^= state >> 17;
        state ^= state << 5;
        words.push(if state.is_multiple_of(7) { 0 } else { state });
    }
    let data: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    let section = InitDataSection {
        name: ".rodata".to_string(),
        virtual_address: 0x0140_0ff8, // 8 bytes before a window boundary, inside RAM
        load_address: 0x1000,
        data,
    };
    let image = ElfImage {
        mode: ElfReadMode::Strict,
        entry_point: 0,
        text_address: 0,
        text: vec![],
        flattened_binary: None,
        flattened_binary_used_bytes: 0,
        init_sections: vec![section.clone()],
        sections: vec![],
        symbols: BTreeMap::new(),
    };
    let code = image.init_data_materialization_code();
    // At most lui+addi for the value plus the store per non-zero word, plus two per window.
    let non_zero = words.iter().filter(|w| **w != 0).count();
    let windows = (section.data.len() / 4096) + 2;
    assert!(code.len() <= 3 * non_zero + 2 * windows);
    assert_init_code_fills_ram(&code, &[section]);
}

#[test]
fn split_hi_lo_roundtrips() {
    for value in [
        0u32,
        1,
        0x7ff,
        0x800,
        0xfff,
        0x1000,
        0x1800,
        0xffff_ffff,
        0xffff_f800,
        0xffff_f7ff,
        0x8000_0000,
        0x7fff_ffff,
        0x1234_5fff,
    ] {
        let (hi, lo) = split_hi_lo(value);
        assert!((-2048..=2047).contains(&lo));
        assert!(hi < (1 << 20));
        assert_eq!((hi << 12).wrapping_add(lo as u32), value);
    }
}

#[test]
fn rejects_non_elf_input() {
    assert!(matches!(
        read_elf(b"definitely not an elf", ElfReadMode::Legacy),
        Err(ElfReadError::Parse(_))
    ));
    assert!(matches!(
        read_elf(&[], ElfReadMode::Strict),
        Err(ElfReadError::Parse(_))
    ));
}

/// Committed ELFs produced by `objcopy -R .text` are rejected with a message naming the cause
/// instead of yielding an empty program.
#[test]
fn rejects_elf_without_text() {
    for elf_path in elf_files() {
        let bytes = std::fs::read(&elf_path).unwrap();
        if let Err(err) = read_elf(&bytes, ElfReadMode::Legacy) {
            assert!(is_stripped_text(&err), "{}: {err}", elf_path.display());
        }
    }
}

/// `read_legacy_binaries` must accept every committed dump pair and agree with `read_elf` on
/// the ELFs that still carry their `.text`.
#[test]
fn legacy_binaries_match_dumps_and_elf() {
    let mut checked = 0;
    for (elf_path, bin_path, text_path) in dump_triples() {
        let dumps = read_legacy_binaries(&bin_path, &text_path)
            .unwrap_or_else(|err| panic!("{}: {err}", bin_path.display()));
        let expected_bin = std::fs::read(&bin_path).unwrap();
        let expected_text = std::fs::read(&text_path).unwrap();
        assert_eq!(dumps.mode, ElfReadMode::Legacy);
        assert_eq!(dumps.objcopy_binary().unwrap(), expected_bin);
        assert_eq!(dumps.text_bytes(), expected_text);
        assert_eq!(
            dumps.flattened_binary.as_ref().unwrap().len(),
            ROM_WORD_SIZE
        );
        assert!(dumps.init_sections.is_empty() && dumps.sections.is_empty());
        assert_eq!(
            ProgramSource::legacy_binaries_from_bin(&bin_path),
            ProgramSource::legacy_binaries(&bin_path, &text_path)
        );
        assert_eq!(
            ProgramSource::legacy_binaries(&bin_path, &text_path).load(),
            (
                dumps.flattened_binary.clone().unwrap(),
                dumps.padded_text_words()
            )
        );

        let bytes = std::fs::read(&elf_path).unwrap();
        let elf = match read_elf(&bytes, ElfReadMode::Legacy) {
            Ok(image) => image,
            Err(err) if is_stripped_text(&err) => continue,
            Err(err) => panic!("{}: {err}", elf_path.display()),
        };
        assert_eq!(elf.text, dumps.text);
        assert_eq!(elf.flattened_binary, dumps.flattened_binary);
        assert_eq!(
            elf.flattened_binary_used_bytes,
            dumps.flattened_binary_used_bytes
        );
        assert_eq!(
            ProgramSource::elf(&elf_path).load(),
            ProgramSource::legacy_binaries(&bin_path, &text_path).load()
        );
        assert_eq!(
            ProgramSource::elf(&elf_path).load_unpadded(),
            ProgramSource::legacy_binaries(&bin_path, &text_path).load_unpadded()
        );
        checked += 1;
    }
    println!("legacy binaries cross-checked against {checked} full ELF files");
}

#[test]
fn legacy_binaries_reject_text_that_is_not_a_prefix() {
    let dir = std::env::temp_dir().join(format!("airbender_elf_test_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let bin = dir.join("app.bin");
    let text = dir.join("app.text");
    std::fs::write(
        &bin,
        [1u32, 2, 3, 4]
            .iter()
            .flat_map(|w| w.to_le_bytes())
            .collect::<Vec<u8>>(),
    )
    .unwrap();
    std::fs::write(
        &text,
        [1u32, 9]
            .iter()
            .flat_map(|w| w.to_le_bytes())
            .collect::<Vec<u8>>(),
    )
    .unwrap();
    assert!(matches!(
        read_legacy_binaries(&bin, &text),
        Err(ElfReadError::Layout(msg)) if msg.contains("not a prefix")
    ));
    std::fs::write(
        &text,
        [1u32, 2]
            .iter()
            .flat_map(|w| w.to_le_bytes())
            .collect::<Vec<u8>>(),
    )
    .unwrap();
    let image = read_legacy_binaries(&bin, &text).unwrap();
    assert_eq!(image.text, vec![1, 2]);
    assert_eq!(image.objcopy_binary_words().unwrap(), &[1, 2, 3, 4]);
    std::fs::write(&text, []).unwrap();
    assert!(matches!(
        read_legacy_binaries(&bin, &text),
        Err(ElfReadError::Layout(_))
    ));
    std::fs::remove_dir_all(&dir).unwrap();
}
