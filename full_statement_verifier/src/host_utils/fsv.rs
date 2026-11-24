//! Loading and decoded-ROM identity of full-statement verifier guests.

use riscv_transpiler::elf::{read_elf_with_rom, ElfReadMode};
use sha3::{Digest, Keccak256};
use std::fmt;
use std::path::{Path, PathBuf};
use verifier_common::fsv_binaries::FsvDescriptor;

/// Identity of a decoded guest program.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct FsvDigest(pub [u8; 32]);

impl fmt::Display for FsvDigest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.iter().try_for_each(|byte| write!(f, "{byte:02x}"))
    }
}

/// Keccak256 of `le_u64(bin.len()) || le_u64(text.len()) || bin words || text words` (lengths
/// in words, words little-endian): the identity of a program as the prover consumes it. Host
/// identity only; no proof or transcript depends on it.
#[must_use]
pub fn fsv_digest(bin: &[u32], text: &[u32]) -> FsvDigest {
    let mut hasher = Keccak256::new();
    hasher.update((bin.len() as u64).to_le_bytes());
    hasher.update((text.len() as u64).to_le_bytes());
    for word in bin.iter().chain(text.iter()) {
        hasher.update(word.to_le_bytes());
    }
    FsvDigest(hasher.finalize().into())
}

/// The tracked FSV root, `tools/gkr_verifier/full_statement_verifiers`.
#[must_use]
pub fn canonical_fsv_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../tools/gkr_verifier/full_statement_verifiers")
}

/// A decoded guest loaded from its exact registry path.
#[derive(Clone, Debug)]
pub struct VerifiedFsvProgram {
    descriptor: FsvDescriptor,
    digest: FsvDigest,
    bin: Vec<u32>,
    text: Vec<u32>,
    rom_bytes: usize,
    text_bytes: usize,
}

impl VerifiedFsvProgram {
    #[must_use]
    pub fn descriptor(&self) -> &FsvDescriptor {
        &self.descriptor
    }

    #[must_use]
    pub fn digest(&self) -> FsvDigest {
        self.digest
    }

    /// The ROM image, padded to the ROM size.
    #[must_use]
    pub fn bin(&self) -> &[u32] {
        &self.bin
    }

    /// The text section, padded to the ROM size.
    #[must_use]
    pub fn text(&self) -> &[u32] {
        &self.text
    }

    #[must_use]
    pub fn unpadded_bin(&self) -> &[u32] {
        &self.bin[..self.rom_bytes / 4]
    }

    #[must_use]
    pub fn unpadded_text(&self) -> &[u32] {
        &self.text[..self.text_bytes / 4]
    }

    #[must_use]
    pub fn into_words(self) -> (Vec<u32>, Vec<u32>) {
        (self.bin, self.text)
    }
}

struct DecodedGuest {
    bin: Vec<u32>,
    text: Vec<u32>,
    rom_bytes: usize,
    text_bytes: usize,
}

const REBUILD: &str = "run `tools/gkr_verifier/dump_recursive_verifiers.sh`";

fn decode_guest(descriptor: &FsvDescriptor, path: &Path) -> DecodedGuest {
    let bytes = std::fs::read(path).unwrap_or_else(|error| {
        if error.kind() == std::io::ErrorKind::NotFound {
            panic!(
                "missing full-statement verifier {descriptor:?} at {}; {REBUILD}",
                path.display()
            )
        }
        panic!(
            "cannot read full-statement verifier {descriptor:?} at {}: {error}",
            path.display()
        )
    });
    let image = read_elf_with_rom(&bytes, ElfReadMode::Legacy, descriptor.profile.rom())
        .unwrap_or_else(|error| {
            panic!(
                "full-statement verifier {descriptor:?} at {} is not a loadable guest: \
             {error}",
                path.display()
            )
        });
    let text = image.padded_text_words();
    DecodedGuest {
        bin: image
            .flattened_binary
            .expect("legacy mode always produces the flattened image"),
        text,
        rom_bytes: image.flattened_binary_used_bytes,
        text_bytes: image.text.len() * 4,
    }
}

/// Decode the ELF at the descriptor's registry path under `dir`.
pub fn load_fsv_exact(dir: impl AsRef<Path>, descriptor: &FsvDescriptor) -> VerifiedFsvProgram {
    let path = dir.as_ref().join(descriptor.relative_path());
    let guest = decode_guest(descriptor, &path);
    VerifiedFsvProgram {
        descriptor: *descriptor,
        digest: fsv_digest(&guest.bin, &guest.text),
        bin: guest.bin,
        text: guest.text,
        rom_bytes: guest.rom_bytes,
        text_bytes: guest.text_bytes,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compression_guests_decode_at_their_rom() {
        use verifier_common::fsv_binaries::{FsvProfile, FSV_REGISTRY};
        for entry in FSV_REGISTRY
            .iter()
            .filter(|entry| entry.descriptor.profile != FsvProfile::Standard)
        {
            let descriptor = entry.descriptor;
            let guest = load_fsv_exact(canonical_fsv_dir(), &descriptor);
            let words = descriptor.profile.rom().word_size();
            assert_eq!((guest.bin().len(), guest.text().len()), (words, words));
            assert!(guest.unpadded_bin().len() <= words);
            assert!(guest.unpadded_text().len() <= words);
        }
        let wrap = FsvDescriptor::compression(FsvProfile::CompressionFinalWrap);
        let bytes = std::fs::read(canonical_fsv_dir().join(wrap.relative_path())).unwrap();
        assert!(matches!(
            read_elf_with_rom(
                &bytes,
                ElfReadMode::Legacy,
                common_constants::rom::REGULAR_ROM
            ),
            Err(riscv_transpiler::elf::ElfReadError::Layout(_))
        ));
    }

    #[test]
    fn digest_keeps_the_bin_text_boundary() {
        assert_ne!(fsv_digest(&[1, 2], &[3]), fsv_digest(&[1], &[2, 3]));
    }
}
