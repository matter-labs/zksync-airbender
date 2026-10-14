//! Reading RISC-V guest programs straight from their ELF files.
//!
//! This replaces the `objcopy -O binary` (flat ROM image) and
//! `objcopy -O binary --only-section=.text` (text section) dumps that used to be read as raw
//! byte files. [`read_elf`] parses an ELF32 executable with the `object` crate, validates it
//! against the memory layout the linker scripts describe (`riscv_common/src/lds/*` and
//! `examples/scripts/lds`: a ROM of [`ROM_BYTE_SIZE`] bytes at address 0 holding `.text`, RAM
//! above it) and hands out the pieces the VM, the prover and the verifiers consume.
//!
//! Two read modes exist, see [`ElfReadMode`]:
//!
//! * **Legacy**: the ROM region is readable. `.text` is followed in ROM by the initial images
//!   (LMAs) of `.rodata`/`.data`; the guest boot sequence copies them to their relocated VMAs in
//!   RAM (`riscv_common::boot_sequence::init`), or the program reads them in place when a
//!   VMA == LMA layout is used. `.text` itself may be readable (today's linker scripts) or
//!   execute-only (a script that gives the init images their own read-only segment); either is
//!   accepted. The flattened ROM image is produced and its used prefix is byte-for-byte what
//!   `objcopy -O binary` emits.
//! * **Strict**: ROM holds code only. Only `.text` may be mapped into ROM, every other loaded
//!   section must be relocated into RAM and its initial content is *virtual*: it is reported
//!   through [`ElfImage::init_sections`] and is meant to be materialized by code (see
//!   [`ElfImage::init_data_materialization_code`]) instead of being read from ROM. No flattened
//!   image is produced.
//!
//! Programs that are not built from this repository and are committed as pre-built `objcopy`
//! dumps (`app.bin` + `app.text`) go through [`read_legacy_binaries`], which validates the pair
//! and yields the same legacy-mode [`ElfImage`] (minus section and symbol details).
//! [`ProgramSource`] names either form so callers load programs one way.

use std::collections::BTreeMap;
use std::fmt;
use std::path::{Path, PathBuf};

use common_constants::{INITIAL_PC, ROM_BYTE_SIZE, ROM_WORD_SIZE};
use object::elf;
use object::read::elf::{ElfFile32, FileHeader, ProgramHeader, SectionHeader};
use object::{Endianness, Object, ObjectSection, ObjectSymbol};

#[cfg(test)]
mod tests;

/// How much of the ROM the program is allowed to *read*.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ElfReadMode {
    /// The initial `.rodata`/`.data` images follow `.text` in ROM and are read from there at
    /// run time (whether `.text` itself is readable is not required); the flattened ROM image is
    /// produced.
    Legacy,
    /// Only `.text` lives in ROM, every other loaded section is relocated into RAM and its
    /// initial content is virtual (materialized by code, never read from ROM).
    Strict,
}

#[derive(Debug)]
pub enum ElfReadError {
    /// The file could not be read from disk.
    Io(std::io::Error),
    /// The bytes are not a well-formed ELF file.
    Parse(object::read::Error),
    /// The ELF is well-formed but not a RISC-V guest program we can run.
    Unsupported(String),
    /// The program layout contradicts the linker-script contract for the requested mode.
    Layout(String),
}

impl fmt::Display for ElfReadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(err) => write!(f, "failed to read ELF file: {err}"),
            Self::Parse(err) => write!(f, "malformed ELF file: {err}"),
            Self::Unsupported(msg) => write!(f, "unsupported ELF file: {msg}"),
            Self::Layout(msg) => write!(f, "unexpected program layout: {msg}"),
        }
    }
}

impl std::error::Error for ElfReadError {}

/// Every `SHF_ALLOC` section of the ELF, i.e. everything that occupies the guest address space.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoadedSection {
    pub name: String,
    /// Where the section lives at run time (VMA).
    pub virtual_address: u32,
    /// Where its initial content is stored (LMA). Equals `virtual_address` for sections that
    /// are not relocated and for sections without file content (`.bss`, `.stack`, `.heap`).
    pub load_address: u32,
    pub size: u32,
    pub writable: bool,
    pub executable: bool,
    /// `true` for sections with content in the file (`PROGBITS`, notes), `false` for `NOBITS`.
    pub file_backed: bool,
}

/// Initial content of a `.rodata` / `.data` section.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InitDataSection {
    pub name: String,
    /// Relocated address the section occupies at run time (`_srodata` / `_sdata`).
    pub virtual_address: u32,
    /// Address of the initial image in ROM for legacy layouts (`_sirodata` / `_sidata`).
    /// Meaningless (virtual) in strict mode.
    pub load_address: u32,
    /// Initial content, `size` bytes, little-endian words.
    pub data: Vec<u8>,
}

impl InitDataSection {
    pub fn size(&self) -> u32 {
        self.data.len() as u32
    }

    pub fn end_address(&self) -> u32 {
        self.virtual_address + self.size()
    }

    /// Whether the section is copied from its ROM image to another place at run time.
    pub fn is_relocated(&self) -> bool {
        self.virtual_address != self.load_address
    }

    pub fn words(&self) -> Vec<u32> {
        bytes_to_words(&self.data)
    }
}

/// Result of [`read_elf`].
#[derive(Clone, Debug)]
pub struct ElfImage {
    pub mode: ElfReadMode,
    /// `e_entry`; validated to be [`INITIAL_PC`] and the start of `.text`.
    pub entry_point: u32,
    /// VMA (== LMA) of `.text`.
    pub text_address: u32,
    /// Content of `.text` as little-endian words, not padded.
    pub text: Vec<u32>,
    /// Legacy mode only: the full ROM image as little-endian words, exactly [`ROM_WORD_SIZE`]
    /// of them. Every loaded section is placed at its LMA, the rest is zero. Its first
    /// [`flattened_binary_used_bytes`](Self::flattened_binary_used_bytes) bytes are what
    /// `objcopy -O binary` produces. `None` in strict mode.
    pub flattened_binary: Option<Vec<u32>>,
    /// End of the last loaded byte in ROM (LMA based), i.e. the length of the `objcopy -O binary`
    /// output; validated to be a multiple of 4. Reported in both modes.
    pub flattened_binary_used_bytes: usize,
    /// Initial content of `.rodata` and `.data` (in that order, only the ones present).
    pub init_sections: Vec<InitDataSection>,
    /// Every section occupying the address space, in file order.
    pub sections: Vec<LoadedSection>,
    /// Linker-script boundary symbols (`_stext`, `_sirodata`, `_srodata`, `_erodata`, `_sidata`,
    /// `_sdata`, `_edata`, `_sbss`, `_ebss`, `_sstack`, `_estack`, `_sheap`, `_eheap`,
    /// `_rom_size`, `__global_pointer$`) when the ELF carries a symbol table.
    pub symbols: BTreeMap<String, u32>,
}

impl ElfImage {
    /// `.text` as raw little-endian bytes (what `objcopy --only-section=.text` dumps).
    pub fn text_bytes(&self) -> Vec<u8> {
        words_to_bytes(&self.text)
    }

    /// `.text` zero-padded to the ROM size ([`ROM_WORD_SIZE`] words). This is the conventional
    /// shape the prover setups and instruction tapes are built from, and the only padding the
    /// host side applies to a program.
    pub fn padded_text_words(&self) -> Vec<u32> {
        let mut words = self.text.clone();
        assert!(words.len() <= ROM_WORD_SIZE);
        words.resize(ROM_WORD_SIZE, 0u32);
        words
    }

    /// The prefix of the flattened image that `objcopy -O binary` would emit (no ROM padding),
    /// as words. Legacy mode only.
    pub fn objcopy_binary_words(&self) -> Option<&[u32]> {
        self.flattened_binary
            .as_deref()
            .map(|image| &image[..self.flattened_binary_used_bytes / 4])
    }

    /// The prefix of the flattened image that `objcopy -O binary` would emit (no ROM padding),
    /// as raw bytes. Legacy mode only.
    pub fn objcopy_binary(&self) -> Option<Vec<u8>> {
        self.objcopy_binary_words().map(words_to_bytes)
    }

    pub fn rodata(&self) -> Option<&InitDataSection> {
        self.init_section(".rodata")
    }

    pub fn data(&self) -> Option<&InitDataSection> {
        self.init_section(".data")
    }

    pub fn init_section(&self, name: &str) -> Option<&InitDataSection> {
        self.init_sections
            .iter()
            .find(|section| section.name == name)
    }

    /// RV32I code that fills every init section (`.rodata`, `.data`) at its relocated address
    /// with its initial content without touching ROM: for every non-zero word the value is
    /// materialized in a register (`lui`/`addi`) and stored with `sw`. Zero words are skipped
    /// because the guest RAM starts zero-initialized. Uses `t0` (x5) as the address base
    /// (re-materialized once per 4 KiB window so every store fits a 12-bit offset) and `t1` (x6)
    /// for values; no other register or memory is touched.
    ///
    /// This is the "virtual init data" path of [`ElfReadMode::Strict`]: the code can be run in
    /// front of the program instead of the ROM-reading copy loop of the legacy boot sequence.
    pub fn init_data_materialization_code(&self) -> Vec<u32> {
        let mut code = Vec::new();
        for section in self.init_sections.iter() {
            emit_init_data_materialization(section, &mut code);
        }
        code
    }
}

/// Parse and validate a RISC-V guest ELF in the given mode.
pub fn read_elf(bytes: &[u8], mode: ElfReadMode) -> Result<ElfImage, ElfReadError> {
    let file = ElfFile32::<Endianness>::parse(bytes).map_err(ElfReadError::Parse)?;
    let endian = file.endian();
    let header = file.elf_header();

    if !file.is_little_endian() {
        return Err(ElfReadError::Unsupported(
            "big-endian ELF, expected little-endian RV32".to_string(),
        ));
    }
    let machine = header.e_machine(endian);
    if machine != elf::EM_RISCV {
        return Err(ElfReadError::Unsupported(format!(
            "e_machine = {machine}, expected EM_RISCV ({})",
            elf::EM_RISCV
        )));
    }
    let elf_type = header.e_type(endian);
    if elf_type != elf::ET_EXEC {
        return Err(ElfReadError::Unsupported(format!(
            "e_type = {elf_type}, expected a statically linked executable (ET_EXEC = {})",
            elf::ET_EXEC
        )));
    }
    let flags = header.e_flags(endian);
    if flags & elf::EF_RISCV_RVC != 0 {
        return Err(ElfReadError::Unsupported(
            "built with compressed instructions (EF_RISCV_RVC); the VM executes 32-bit instructions only"
                .to_string(),
        ));
    }
    if flags & elf::EF_RISCV_FLOAT_ABI != 0 {
        return Err(ElfReadError::Unsupported(
            "built with a hard-float ABI; the VM is soft-float only".to_string(),
        ));
    }
    let entry_point = header.e_entry(endian);

    let segments: Vec<Segment> = file
        .elf_program_headers()
        .iter()
        .filter(|ph| ph.p_type(endian) == elf::PT_LOAD)
        .map(|ph| Segment {
            vaddr: ph.p_vaddr(endian),
            paddr: ph.p_paddr(endian),
            filesz: ph.p_filesz(endian),
            memsz: ph.p_memsz(endian),
            flags: ph.p_flags(endian),
        })
        .collect();

    let mut sections = Vec::new();
    let mut text: Option<(LoadedSection, &[u8], u32)> = None;
    let mut init_candidates: Vec<(LoadedSection, &[u8])> = Vec::new();
    let mut loaded_content: Vec<(LoadedSection, &[u8])> = Vec::new();

    for section in file.sections() {
        let sh = section.elf_section_header();
        let sh_flags = sh.sh_flags(endian);
        let sh_type = sh.sh_type(endian);
        if sh_flags & elf::SHF_ALLOC == 0 || sh_type == elf::SHT_NULL {
            continue;
        }
        let name = section.name().map_err(ElfReadError::Parse)?.to_string();
        let virtual_address = sh.sh_addr(endian);
        let size = sh.sh_size(endian);
        let file_backed = sh_type != elf::SHT_NOBITS;
        if virtual_address.checked_add(size).is_none() {
            return Err(ElfReadError::Layout(format!(
                "section {name} at {virtual_address:#x} with size {size:#x} wraps the address space"
            )));
        }

        let (load_address, segment_flags) = if file_backed && size > 0 {
            let segment = segments
                .iter()
                .find(|segment| segment.covers(virtual_address, size))
                .ok_or_else(|| {
                    ElfReadError::Layout(format!(
                        "section {name} ({virtual_address:#x}, {size:#x} bytes) is not covered by any PT_LOAD segment"
                    ))
                })?;
            (
                segment.paddr + (virtual_address - segment.vaddr),
                Some(segment.flags),
            )
        } else {
            (virtual_address, None)
        };

        let loaded = LoadedSection {
            name: name.clone(),
            virtual_address,
            load_address,
            size,
            writable: sh_flags & elf::SHF_WRITE != 0,
            executable: sh_flags & elf::SHF_EXECINSTR != 0,
            file_backed,
        };

        if file_backed {
            let data = section.data().map_err(ElfReadError::Parse)?;
            if data.len() != size as usize {
                return Err(ElfReadError::Layout(format!(
                    "section {name} declares {size:#x} bytes but the file holds {:#x}",
                    data.len()
                )));
            }
            if size > 0 {
                loaded_content.push((loaded.clone(), data));
            }
            if name == ".text" {
                text = Some((loaded.clone(), data, segment_flags.unwrap_or(0)));
            } else if name == ".rodata" || name == ".data" {
                init_candidates.push((loaded.clone(), data));
            }
        }

        if loaded.executable && loaded.size > 0 && name != ".text" {
            return Err(ElfReadError::Layout(format!(
                "executable section {name} outside .text; the linker script merges all code into .text"
            )));
        }

        sections.push(loaded);
    }

    // --- .text ---
    let Some((text_section, text_data, text_segment_flags)) = text else {
        return Err(ElfReadError::Layout(
            "no .text section (an ELF produced with `objcopy -R .text` has only symbols)"
                .to_string(),
        ));
    };
    if text_section.size == 0 {
        return Err(ElfReadError::Layout(".text is empty".to_string()));
    }
    if !text_section.executable {
        return Err(ElfReadError::Layout(".text is not executable".to_string()));
    }
    if text_section.virtual_address != text_section.load_address {
        return Err(ElfReadError::Layout(format!(
            ".text must not be relocated (VMA {:#x} != LMA {:#x})",
            text_section.virtual_address, text_section.load_address
        )));
    }
    if text_section.virtual_address % 4 != 0 || text_section.size % 4 != 0 {
        return Err(ElfReadError::Layout(format!(
            ".text must be word-aligned (address {:#x}, size {:#x})",
            text_section.virtual_address, text_section.size
        )));
    }
    let text_end = text_section.virtual_address + text_section.size;
    if text_end as usize > ROM_BYTE_SIZE {
        return Err(ElfReadError::Layout(format!(
            ".text ends at {text_end:#x}, beyond the {ROM_BYTE_SIZE:#x}-byte ROM"
        )));
    }
    if entry_point != INITIAL_PC {
        return Err(ElfReadError::Layout(format!(
            "entry point {entry_point:#x} != {INITIAL_PC:#x}, the VM always starts at INITIAL_PC"
        )));
    }
    if entry_point != text_section.virtual_address {
        return Err(ElfReadError::Layout(format!(
            "entry point {entry_point:#x} is not the start of .text ({:#x})",
            text_section.virtual_address
        )));
    }
    if text_segment_flags & elf::PF_X == 0 {
        return Err(ElfReadError::Layout(
            "the segment holding .text is not executable".to_string(),
        ));
    }
    if text_segment_flags & elf::PF_W != 0 {
        return Err(ElfReadError::Layout(
            "the segment holding .text is writable".to_string(),
        ));
    }

    // --- everything else ---
    for section in sections.iter() {
        if section.size == 0 {
            continue;
        }
        if section.writable && (section.virtual_address as usize) < ROM_BYTE_SIZE {
            return Err(ElfReadError::Layout(format!(
                "writable section {} at {:#x} lies inside the ROM",
                section.name, section.virtual_address
            )));
        }
    }
    for (section, _) in loaded_content.iter() {
        if section.name == ".text" {
            continue;
        }
        match mode {
            ElfReadMode::Legacy => {
                let lma_end = section.load_address as u64 + section.size as u64;
                if lma_end > ROM_BYTE_SIZE as u64 {
                    return Err(ElfReadError::Layout(format!(
                        "legacy mode loads initial content from ROM only, but section {} is stored at {:#x}..{:#x}",
                        section.name, section.load_address, lma_end
                    )));
                }
                if section.load_address < text_end {
                    return Err(ElfReadError::Layout(format!(
                        "legacy mode expects initial content to follow .text in ROM, but section {} is stored at {:#x} (.text ends at {text_end:#x})",
                        section.name, section.load_address
                    )));
                }
            }
            ElfReadMode::Strict => {
                if (section.virtual_address as usize) < ROM_BYTE_SIZE {
                    return Err(ElfReadError::Layout(format!(
                        "strict mode keeps ROM execute-only, but section {} is placed at {:#x} inside the ROM; it must be relocated into RAM",
                        section.name, section.virtual_address
                    )));
                }
            }
        }
    }

    // --- flattened ROM image (what `objcopy -O binary` produces, padded to the ROM) ---
    let mut placed: Vec<&(LoadedSection, &[u8])> = loaded_content.iter().collect();
    placed.sort_by_key(|(section, _)| section.load_address);
    let mut flattened_binary_used_bytes = 0usize;
    let mut previous_end = 0u64;
    let mut flattened = (mode == ElfReadMode::Legacy).then(|| vec![0u8; ROM_BYTE_SIZE]);
    for (section, data) in placed.iter() {
        let start = section.load_address as u64;
        let end = start + section.size as u64;
        if start < previous_end {
            return Err(ElfReadError::Layout(format!(
                "section {} overlaps the preceding section in ROM at {start:#x}",
                section.name
            )));
        }
        previous_end = end;
        if end as usize > ROM_BYTE_SIZE {
            // Strict mode allows LMAs outside the ROM (they are virtual); such a section does
            // not contribute to the ROM image.
            continue;
        }
        if let Some(image) = flattened.as_mut() {
            image[start as usize..end as usize].copy_from_slice(data);
        }
        flattened_binary_used_bytes = flattened_binary_used_bytes.max(end as usize);
    }
    if !flattened_binary_used_bytes.is_multiple_of(4) {
        return Err(ElfReadError::Layout(format!(
            "loaded ROM content ends at {flattened_binary_used_bytes:#x}, not on a word boundary"
        )));
    }

    // --- init data ---
    let mut init_sections = Vec::new();
    for name in [".rodata", ".data"] {
        let Some((section, data)) = init_candidates.iter().find(|(s, _)| s.name == name) else {
            continue;
        };
        if section.virtual_address % 4 != 0
            || section.load_address % 4 != 0
            || section.size % 4 != 0
        {
            return Err(ElfReadError::Layout(format!(
                "{name} must be word-aligned (VMA {:#x}, LMA {:#x}, size {:#x})",
                section.virtual_address, section.load_address, section.size
            )));
        }
        init_sections.push(InitDataSection {
            name: name.to_string(),
            virtual_address: section.virtual_address,
            load_address: section.load_address,
            data: data.to_vec(),
        });
    }

    // --- linker-script symbols, cross-checked against the section table when present ---
    let mut symbols = BTreeMap::new();
    for symbol in file.symbols() {
        let Ok(name) = symbol.name() else { continue };
        if LINKER_SYMBOLS.contains(&name) {
            symbols.insert(name.to_string(), symbol.address() as u32);
        }
    }
    let check_symbol = |name: &str, expected: u32| -> Result<(), ElfReadError> {
        match symbols.get(name) {
            Some(&actual) if actual != expected => Err(ElfReadError::Layout(format!(
                "linker symbol {name} = {actual:#x} disagrees with the section table ({expected:#x})"
            ))),
            _ => Ok(()),
        }
    };
    check_symbol("_stext", text_section.virtual_address)?;
    for section in init_sections.iter_mut() {
        let (start, end, load) = match section.name.as_str() {
            ".rodata" => ("_srodata", "_erodata", "_sirodata"),
            ".data" => ("_sdata", "_edata", "_sidata"),
            _ => unreachable!(),
        };
        check_symbol(start, section.virtual_address)?;
        check_symbol(end, section.end_address())?;
        if section.size() == 0 {
            // An empty section is not backed by any segment, so the section table carries no
            // usable LMA for it; the linker script's `LOADADDR` symbol is the only source.
            if let Some(&load_address) = symbols.get(load) {
                section.load_address = load_address;
            }
        } else {
            check_symbol(load, section.load_address)?;
        }
    }
    if let Some(&rom_size) = symbols.get("_rom_size") {
        if rom_size as usize != ROM_BYTE_SIZE {
            return Err(ElfReadError::Layout(format!(
                "linker script ROM size {rom_size:#x} != common_constants::ROM_BYTE_SIZE ({ROM_BYTE_SIZE:#x})"
            )));
        }
    }

    Ok(ElfImage {
        mode,
        entry_point,
        text_address: text_section.virtual_address,
        text: bytes_to_words(text_data),
        flattened_binary: flattened.as_deref().map(bytes_to_words),
        flattened_binary_used_bytes,
        init_sections,
        sections,
        symbols,
    })
}

/// [`read_elf`] on a file.
pub fn read_elf_from_path(path: &Path, mode: ElfReadMode) -> Result<ElfImage, ElfReadError> {
    let bytes = std::fs::read(path).map_err(ElfReadError::Io)?;
    read_elf(&bytes, mode)
}

/// Load a guest program from its ELF for the VM and the prover (legacy read mode): returns
/// `(flattened ROM image words, text section words)`, both [`ROM_WORD_SIZE`] words long,
/// zero-padded. Panics with the parse/validation error on failure. See [`ProgramSource`].
pub fn load_legacy_program(path: &Path) -> (Vec<u32>, Vec<u32>) {
    ProgramSource::elf(path).load()
}

/// Read a program committed as pre-built `objcopy` dumps: `bin_path` is the flat ROM image
/// (`objcopy -O binary`), `text_path` the text section (`--only-section=.text`). The text must
/// be a non-empty, word-aligned prefix of the image and the image must fit the ROM. The result
/// is the legacy-mode [`ElfImage`] with the flattened image and `.text` filled in; section,
/// init-data and symbol details are empty because the dumps do not carry them.
pub fn read_legacy_binaries(bin_path: &Path, text_path: &Path) -> Result<ElfImage, ElfReadError> {
    let bin = std::fs::read(bin_path).map_err(ElfReadError::Io)?;
    let text = std::fs::read(text_path).map_err(ElfReadError::Io)?;
    if !bin.len().is_multiple_of(4) || !text.len().is_multiple_of(4) {
        return Err(ElfReadError::Layout(format!(
            "dumps must be word-aligned ({} is {} bytes, {} is {} bytes)",
            bin_path.display(),
            bin.len(),
            text_path.display(),
            text.len()
        )));
    }
    if text.is_empty() {
        return Err(ElfReadError::Layout(format!(
            "text section dump {} is empty",
            text_path.display()
        )));
    }
    if bin.len() > ROM_BYTE_SIZE {
        return Err(ElfReadError::Layout(format!(
            "flat image {} is {} bytes, beyond the {ROM_BYTE_SIZE:#x}-byte ROM",
            bin_path.display(),
            bin.len()
        )));
    }
    if text.len() > bin.len() || bin[..text.len()] != text[..] {
        return Err(ElfReadError::Layout(format!(
            "text section {} is not a prefix of the flat image {}",
            text_path.display(),
            bin_path.display()
        )));
    }
    let mut flattened = bytes_to_words(&bin);
    flattened.resize(ROM_WORD_SIZE, 0u32);
    Ok(ElfImage {
        mode: ElfReadMode::Legacy,
        entry_point: INITIAL_PC,
        text_address: INITIAL_PC,
        text: bytes_to_words(&text),
        flattened_binary: Some(flattened),
        flattened_binary_used_bytes: bin.len(),
        init_sections: Vec::new(),
        sections: Vec::new(),
        symbols: BTreeMap::new(),
    })
}

/// [`read_legacy_binaries`] followed by the conventional padding, like [`load_legacy_program`].
pub fn load_legacy_binaries(bin_path: &Path, text_path: &Path) -> (Vec<u32>, Vec<u32>) {
    ProgramSource::legacy_binaries(bin_path, text_path).load()
}

/// Where a guest program comes from. Every host-side consumer loads programs through this type
/// so reading and padding happen in exactly one place.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ProgramSource {
    /// The linked ELF, read with [`read_elf`] in [`ElfReadMode::Legacy`].
    Elf(PathBuf),
    /// Pre-built `objcopy` dumps committed as-is (programs not built from this repository),
    /// read with [`read_legacy_binaries`].
    LegacyBinaries { bin: PathBuf, text: PathBuf },
}

impl ProgramSource {
    pub fn elf(path: impl Into<PathBuf>) -> Self {
        Self::Elf(path.into())
    }

    pub fn legacy_binaries(bin: impl Into<PathBuf>, text: impl Into<PathBuf>) -> Self {
        Self::LegacyBinaries {
            bin: bin.into(),
            text: text.into(),
        }
    }

    /// Dumps named by convention: `<stem>.bin` next to `<stem>.text`.
    pub fn legacy_binaries_from_bin(bin: impl Into<PathBuf>) -> Self {
        let bin: PathBuf = bin.into();
        let text = match bin.to_str().and_then(|s| s.strip_suffix(".bin")) {
            Some(stem) => PathBuf::from(format!("{stem}.text")),
            None => bin.with_extension("text"),
        };
        Self::LegacyBinaries { bin, text }
    }

    pub fn read(&self) -> Result<ElfImage, ElfReadError> {
        match self {
            Self::Elf(path) => read_elf_from_path(path, ElfReadMode::Legacy),
            Self::LegacyBinaries { bin, text } => read_legacy_binaries(bin, text),
        }
    }

    /// `(flattened ROM image words, text section words)`, both zero-padded to [`ROM_WORD_SIZE`]
    /// words: the conventional shape for prover setups and instruction tapes. Panics on failure.
    pub fn load(&self) -> (Vec<u32>, Vec<u32>) {
        let image = self.read_or_panic();
        let flattened = image
            .flattened_binary
            .clone()
            .expect("legacy mode always produces the flattened image");
        (flattened, image.padded_text_words())
    }

    /// `(objcopy-equivalent ROM image words, text section words)` without any padding, the
    /// shape the raw dumps have on disk. Panics on failure.
    pub fn load_unpadded(&self) -> (Vec<u32>, Vec<u32>) {
        let image = self.read_or_panic();
        let flattened = image
            .objcopy_binary_words()
            .expect("legacy mode always produces the flattened image")
            .to_vec();
        (flattened, image.text)
    }

    fn read_or_panic(&self) -> ElfImage {
        self.read()
            .unwrap_or_else(|err| panic!("failed to load program {self}: {err}"))
    }
}

impl fmt::Display for ProgramSource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Elf(path) => write!(f, "{}", path.display()),
            Self::LegacyBinaries { bin, text } => {
                write!(f, "{} + {}", bin.display(), text.display())
            }
        }
    }
}

const LINKER_SYMBOLS: [&str; 15] = [
    "_stext",
    "_sirodata",
    "_srodata",
    "_erodata",
    "_sidata",
    "_sdata",
    "_edata",
    "_sbss",
    "_ebss",
    "_sstack",
    "_estack",
    "_sheap",
    "_eheap",
    "_rom_size",
    "__global_pointer$",
];

struct Segment {
    vaddr: u32,
    paddr: u32,
    #[allow(dead_code)]
    filesz: u32,
    memsz: u32,
    flags: u32,
}

impl Segment {
    fn covers(&self, address: u32, size: u32) -> bool {
        let start = address as u64;
        let end = start + size as u64;
        let seg_start = self.vaddr as u64;
        let seg_end = seg_start + self.memsz as u64;
        start >= seg_start && end <= seg_end
    }
}

pub fn words_to_bytes(words: &[u32]) -> Vec<u8> {
    words.iter().flat_map(|word| word.to_le_bytes()).collect()
}

pub fn bytes_to_words(bytes: &[u8]) -> Vec<u32> {
    let (chunks, rest) = bytes.as_chunks::<4>();
    assert!(
        rest.is_empty(),
        "byte length {} is not a multiple of 4",
        bytes.len()
    );
    chunks
        .iter()
        .map(|chunk| u32::from_le_bytes(*chunk))
        .collect()
}

// --- RV32I encoding helpers for the init-data materialization code ---

const REG_ZERO: u32 = 0;
const REG_BASE: u32 = 5; // t0
const REG_VALUE: u32 = 6; // t1

/// Window (in bytes) that a single base register covers with signed 12-bit store offsets.
const STORE_WINDOW_BYTES: u32 = 1 << 12;

const fn encode_lui(rd: u32, imm20: u32) -> u32 {
    (imm20 << 12) | (rd << 7) | 0b0110111
}

const fn encode_addi(rd: u32, rs1: u32, imm12: i32) -> u32 {
    (((imm12 as u32) & 0xfff) << 20) | (rs1 << 15) | (rd << 7) | 0b0010011
}

const fn encode_sw(rs2: u32, rs1: u32, imm12: i32) -> u32 {
    let imm = (imm12 as u32) & 0xfff;
    ((imm >> 5) << 25) | (rs2 << 20) | (rs1 << 15) | (0b010 << 12) | ((imm & 0x1f) << 7) | 0b0100011
}

/// Split `value` into `(imm20, imm12)` such that `lui(imm20) + sext(imm12) == value` mod 2^32.
const fn split_hi_lo(value: u32) -> (u32, i32) {
    let lo = (((value & 0xfff) as i32) << 20) >> 20;
    let hi = value.wrapping_sub(lo as u32) >> 12;
    (hi, lo)
}

/// Emit the shortest `lui`/`addi` sequence that puts `value` into `rd` (`value != 0`).
fn emit_materialize_constant(rd: u32, value: u32, code: &mut Vec<u32>) {
    let (hi, lo) = split_hi_lo(value);
    if hi == 0 {
        code.push(encode_addi(rd, REG_ZERO, lo));
    } else if lo == 0 {
        code.push(encode_lui(rd, hi));
    } else {
        code.push(encode_lui(rd, hi));
        code.push(encode_addi(rd, rd, lo));
    }
}

fn emit_init_data_materialization(section: &InitDataSection, code: &mut Vec<u32>) {
    let words = section.words();
    let start = section.virtual_address;
    let mut window_start = start & !(STORE_WINDOW_BYTES - 1);
    let end = section.end_address();
    while window_start < end {
        // Base in the middle of the window so [-2048, 2047] offsets cover all of it.
        let base = window_start.wrapping_add(STORE_WINDOW_BYTES / 2);
        let mut base_materialized = false;
        let first = window_start.max(start);
        let last = window_start.saturating_add(STORE_WINDOW_BYTES).min(end);
        let mut address = first;
        while address < last {
            let word = words[((address - start) / 4) as usize];
            if word != 0 {
                if !base_materialized {
                    emit_materialize_constant(REG_BASE, base, code);
                    base_materialized = true;
                }
                let offset = address.wrapping_sub(base) as i32;
                debug_assert!((-2048..=2047).contains(&offset));
                emit_materialize_constant(REG_VALUE, word, code);
                code.push(encode_sw(REG_VALUE, REG_BASE, offset));
            }
            address += 4;
        }
        window_start = window_start.saturating_add(STORE_WINDOW_BYTES);
        if window_start == u32::MAX {
            break;
        }
    }
}
