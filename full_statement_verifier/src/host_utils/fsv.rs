//! Exact, digest-bound loading of the full-statement verifier guests.
//!
//! [`FSV_REGISTRY`] says which guest exists for a descriptor and where it lives under the FSV
//! root; the tracked manifest (`tools/gkr_verifier/full_statement_verifiers/fsv_manifest.txt`,
//! compiled in here and never read from disk at run time) pins each guest's decoded ROM image.
//! [`load_fsv_exact`] accepts a file only if it decodes to that image, so an `FSV_DIR` may
//! relocate the binaries but never re-identify them.

use riscv_transpiler::elf::{read_elf, ElfReadError, ElfReadMode};
use sha3::{Digest, Keccak256};
use std::fmt;
use std::path::{Path, PathBuf};
use verifier_common::fsv_binaries::{
    BlakeMode, FsvDescriptor, FsvProgram, SecurityLevel, SoundnessMode, UnsupportedFsvVariant,
    FSV_REGISTRY,
};

/// Name of the digest recipe of [`fsv_digest`], recorded in the manifest header.
pub const FSV_DIGEST_RECIPE: &str = "fsv-rom-digest-v1";

/// The manifest's file name under the FSV root.
pub const FSV_MANIFEST_FILE: &str = "fsv_manifest.txt";

const MANIFEST: &str =
    include_str!("../../../tools/gkr_verifier/full_statement_verifiers/fsv_manifest.txt");

/// Identity of a decoded guest program, [`FSV_DIGEST_RECIPE`].
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct FsvDigest(pub [u8; 32]);

impl fmt::Display for FsvDigest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.iter().try_for_each(|byte| write!(f, "{byte:02x}"))
    }
}

impl FsvDigest {
    fn parse(hex: &str) -> Option<Self> {
        if hex.len() != 64 || !hex.bytes().all(|c| matches!(c, b'0'..=b'9' | b'a'..=b'f')) {
            return None;
        }
        let mut digest = [0u8; 32];
        for (byte, pair) in digest.iter_mut().zip(hex.as_bytes().chunks(2)) {
            *byte = u8::from_str_radix(std::str::from_utf8(pair).ok()?, 16).ok()?;
        }
        Some(Self(digest))
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

/// A pinned manifest row.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct FsvManifestEntry {
    pub descriptor: FsvDescriptor,
    pub relative_path: &'static str,
    /// Decoded ROM image size (`objcopy -O binary` length).
    pub rom_bytes: usize,
    /// `.text` size.
    pub text_bytes: usize,
    pub digest: FsvDigest,
}

/// The compiled-in manifest, in [`FSV_REGISTRY`] order.
pub fn fsv_manifest() -> &'static [FsvManifestEntry] {
    static ENTRIES: std::sync::OnceLock<Vec<FsvManifestEntry>> = std::sync::OnceLock::new();
    ENTRIES.get_or_init(|| {
        parse_manifest(MANIFEST).unwrap_or_else(|err| panic!("{FSV_MANIFEST_FILE}: {err}"))
    })
}

/// The pinned manifest row of `descriptor`.
pub fn fsv_manifest_entry(
    descriptor: &FsvDescriptor,
) -> Result<&'static FsvManifestEntry, FsvLoadError> {
    descriptor
        .registry_entry()
        .map_err(FsvLoadError::Unsupported)?;
    fsv_manifest()
        .iter()
        .find(|entry| entry.descriptor == *descriptor)
        .ok_or(FsvLoadError::MissingManifestEntry {
            descriptor: *descriptor,
        })
}

/// The tracked FSV root, `tools/gkr_verifier/full_statement_verifiers`.
#[must_use]
pub fn canonical_fsv_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../tools/gkr_verifier/full_statement_verifiers")
}

/// A guest whose decoded image matched its pinned digest. Only [`load_fsv_exact`] builds one.
#[derive(Clone, Debug)]
pub struct VerifiedFsvProgram {
    descriptor: FsvDescriptor,
    digest: FsvDigest,
    bin: Vec<u32>,
    text: Vec<u32>,
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
    pub fn into_words(self) -> (Vec<u32>, Vec<u32>) {
        (self.bin, self.text)
    }
}

#[derive(Debug)]
pub enum FsvLoadError {
    /// No guest is built for the descriptor.
    Unsupported(UnsupportedFsvVariant),
    /// The descriptor is registered but the compiled-in manifest has no row for it.
    MissingManifestEntry { descriptor: FsvDescriptor },
    /// The guest file does not exist.
    MissingArtifact {
        descriptor: FsvDescriptor,
        path: PathBuf,
    },
    /// The guest file could not be read.
    Io {
        descriptor: FsvDescriptor,
        path: PathBuf,
        error: std::io::Error,
    },
    /// The guest file is not a loadable guest ELF.
    InvalidElf {
        descriptor: FsvDescriptor,
        path: PathBuf,
        error: ElfReadError,
    },
    /// The file is the pinned image of another registered guest.
    WrongArtifact {
        descriptor: FsvDescriptor,
        path: PathBuf,
        found: FsvDescriptor,
    },
    /// The file decodes to an image no registered guest has.
    DigestMismatch {
        descriptor: FsvDescriptor,
        path: PathBuf,
        expected: FsvDigest,
        actual: FsvDigest,
    },
}

impl fmt::Display for FsvLoadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        const REBUILD: &str = "run `tools/gkr_verifier/dump_recursive_verifiers.sh`";
        match self {
            Self::Unsupported(err) => write!(f, "{err}"),
            Self::MissingManifestEntry { descriptor } => write!(
                f,
                "the compiled-in {FSV_MANIFEST_FILE} has no row for {descriptor}; {REBUILD}"
            ),
            Self::MissingArtifact { descriptor, path } => write!(
                f,
                "missing full-statement verifier {descriptor} at {}; {REBUILD}",
                path.display()
            ),
            Self::Io {
                descriptor,
                path,
                error,
            } => write!(
                f,
                "cannot read full-statement verifier {descriptor} at {}: {error}",
                path.display()
            ),
            Self::InvalidElf {
                descriptor,
                path,
                error,
            } => write!(
                f,
                "full-statement verifier {descriptor} at {} is not a loadable guest: {error}",
                path.display()
            ),
            Self::WrongArtifact {
                descriptor,
                path,
                found,
            } => write!(
                f,
                "{} holds the full-statement verifier {found}, not the requested {descriptor}",
                path.display()
            ),
            Self::DigestMismatch {
                descriptor,
                path,
                expected,
                actual,
            } => write!(
                f,
                "full-statement verifier {descriptor} at {} has ROM digest {actual}, \
                 pinned {expected} ({FSV_DIGEST_RECIPE}); the file is modified or stale, {REBUILD}",
                path.display()
            ),
        }
    }
}

impl std::error::Error for FsvLoadError {}

/// A guest file decoded the way the prover consumes it.
struct DecodedGuest {
    bin: Vec<u32>,
    text: Vec<u32>,
    rom_bytes: usize,
    text_bytes: usize,
}

fn decode_guest(descriptor: &FsvDescriptor, path: &Path) -> Result<DecodedGuest, FsvLoadError> {
    let bytes = std::fs::read(path).map_err(|error| {
        if error.kind() == std::io::ErrorKind::NotFound {
            FsvLoadError::MissingArtifact {
                descriptor: *descriptor,
                path: path.to_path_buf(),
            }
        } else {
            FsvLoadError::Io {
                descriptor: *descriptor,
                path: path.to_path_buf(),
                error,
            }
        }
    })?;
    let image =
        read_elf(&bytes, ElfReadMode::Legacy).map_err(|error| FsvLoadError::InvalidElf {
            descriptor: *descriptor,
            path: path.to_path_buf(),
            error,
        })?;
    let text = image.padded_text_words();
    Ok(DecodedGuest {
        bin: image
            .flattened_binary
            .expect("legacy mode always produces the flattened image"),
        text,
        rom_bytes: image.flattened_binary_used_bytes,
        text_bytes: image.text.len() * 4,
    })
}

/// Load the guest of `descriptor` from `dir` (the FSV root or a relocated copy of it) and check
/// it against its pinned digest. No fallback: a missing or different file is an error.
pub fn load_fsv_exact(
    dir: impl AsRef<Path>,
    descriptor: &FsvDescriptor,
) -> Result<VerifiedFsvProgram, FsvLoadError> {
    let entry = descriptor
        .registry_entry()
        .map_err(FsvLoadError::Unsupported)?;
    let pinned = fsv_manifest_entry(descriptor)?;
    let path = dir.as_ref().join(entry.relative_path);
    let guest = decode_guest(descriptor, &path)?;
    let digest = fsv_digest(&guest.bin, &guest.text);
    if digest != pinned.digest {
        return Err(
            match fsv_manifest().iter().find(|other| other.digest == digest) {
                Some(other) => FsvLoadError::WrongArtifact {
                    descriptor: *descriptor,
                    path,
                    found: other.descriptor,
                },
                None => FsvLoadError::DigestMismatch {
                    descriptor: *descriptor,
                    path,
                    expected: pinned.digest,
                    actual: digest,
                },
            },
        );
    }
    Ok(VerifiedFsvProgram {
        descriptor: *descriptor,
        digest,
        bin: guest.bin,
        text: guest.text,
    })
}

/// [`load_fsv_exact`] of the Sec100 pessimistic-conjecture guest, for callers that predate
/// soundness-mode selection; panics on any [`FsvLoadError`].
#[must_use]
pub fn load_fsv_program(
    dir: impl AsRef<Path>,
    program: FsvProgram,
    blake: BlakeMode,
) -> (Vec<u32>, Vec<u32>) {
    let descriptor = FsvDescriptor::new(
        SecurityLevel::Sec100,
        SoundnessMode::PessimisticConjecture,
        program,
        blake,
    );
    load_fsv_exact(dir, &descriptor)
        .unwrap_or_else(|err| panic!("{err}"))
        .into_words()
}

const MANIFEST_HEADER: &str = "\
# Pinned identity of every full-statement verifier guest in
# verifier_common::fsv_binaries::FSV_REGISTRY. Compiled into
# full_statement_verifier::host_utils, which loads a guest only if it matches its row.
# Generated; regenerate with tools/gkr_verifier/dump_recursive_verifiers.sh.
#
# rom_bytes: decoded ROM image size (objcopy -O binary length); the ROM is 4194304 bytes.
# text_bytes: .text size.
";

/// The manifest of the guests under `dir`, as tracked: one row per [`FSV_REGISTRY`] entry, in
/// registry order. Fails if any guest is missing or not loadable.
pub fn render_fsv_manifest(dir: impl AsRef<Path>) -> Result<String, FsvLoadError> {
    let mut out = String::from(MANIFEST_HEADER);
    out.push_str(&format!(
        "# digest: {FSV_DIGEST_RECIPE} = keccak256(le_u64(bin words) || le_u64(text words) || \
         bin words || text words),\n\
         #   little-endian words of the ROM-padded image and .text, as the legacy ELF loader returns them.\n\
         #\n\
         # security soundness_mode program profile blake path rom_bytes text_bytes digest\n"
    ));
    for entry in FSV_REGISTRY {
        let guest = decode_guest(&entry.descriptor, &dir.as_ref().join(entry.relative_path))?;
        let [security, mode, program, profile, blake] = entry.descriptor.tokens();
        out.push_str(&format!(
            "{security} {mode} {program} {profile} {blake} {} {} {} {}\n",
            entry.relative_path,
            guest.rom_bytes,
            guest.text_bytes,
            fsv_digest(&guest.bin, &guest.text),
        ));
    }
    Ok(out)
}

fn parse_manifest(text: &str) -> Result<Vec<FsvManifestEntry>, String> {
    let recipe = format!("# digest: {FSV_DIGEST_RECIPE} ");
    if !text.lines().any(|line| line.starts_with(&recipe)) {
        return Err(format!("does not declare the {FSV_DIGEST_RECIPE} digest"));
    }
    let mut entries: Vec<FsvManifestEntry> = Vec::new();
    for line in text.lines().filter(|line| !line.starts_with('#')) {
        let fields: Vec<&str> = line.split(' ').collect();
        let [security, mode, program, profile, blake, path, rom_bytes, text_bytes, digest] =
            fields[..]
        else {
            return Err(format!("malformed row {line:?}"));
        };
        let registered = FSV_REGISTRY
            .iter()
            .find(|entry| entry.descriptor.tokens() == [security, mode, program, profile, blake])
            .ok_or_else(|| format!("row {line:?} names no registered guest"))?;
        if registered.relative_path != path {
            return Err(format!(
                "row {line:?}: the registry places {} at {}",
                registered.descriptor, registered.relative_path
            ));
        }
        if entries
            .iter()
            .any(|entry| entry.descriptor == registered.descriptor)
        {
            return Err(format!("duplicate row for {}", registered.descriptor));
        }
        entries.push(FsvManifestEntry {
            descriptor: registered.descriptor,
            relative_path: registered.relative_path,
            rom_bytes: rom_bytes
                .parse()
                .map_err(|_| format!("row {line:?}: bad rom_bytes"))?,
            text_bytes: text_bytes
                .parse()
                .map_err(|_| format!("row {line:?}: bad text_bytes"))?,
            digest: FsvDigest::parse(digest).ok_or_else(|| format!("row {line:?}: bad digest"))?,
        });
    }
    Ok(entries)
}

#[cfg(test)]
mod tests {
    use super::*;
    use verifier_common::fsv_binaries::FsvProfile;

    const PESSIMISTIC: SoundnessMode = SoundnessMode::PessimisticConjecture;
    const ETHPROOFS: SoundnessMode = SoundnessMode::EthproofsSoundnessCalc;

    fn descriptor(mode: SoundnessMode, program: FsvProgram, blake: BlakeMode) -> FsvDescriptor {
        FsvDescriptor::new(SecurityLevel::Sec100, mode, program, blake)
    }

    fn path_of(descriptor: &FsvDescriptor) -> &'static str {
        descriptor.registry_entry().unwrap().relative_path
    }

    /// A scratch FSV root holding the given canonical guests at the given registry paths.
    struct ScratchDir(PathBuf);

    impl ScratchDir {
        fn new(name: &str, files: &[(&FsvDescriptor, &FsvDescriptor)]) -> Self {
            let dir = std::env::temp_dir().join(format!(
                "fsv-registry-{name}-{}-{:?}",
                std::process::id(),
                std::thread::current().id()
            ));
            let _ = std::fs::remove_dir_all(&dir);
            for (source, destination) in files {
                let to = dir.join(path_of(destination));
                std::fs::create_dir_all(to.parent().unwrap()).unwrap();
                std::fs::copy(canonical_fsv_dir().join(path_of(source)), &to).unwrap();
            }
            std::fs::create_dir_all(&dir).unwrap();
            Self(dir)
        }
    }

    impl Drop for ScratchDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    /// Rewrites the tracked manifest from the guests on disk (dump_recursive_verifiers.sh).
    #[test]
    #[ignore = "generator: rewrites tools/gkr_verifier/full_statement_verifiers/fsv_manifest.txt"]
    fn regenerate_fsv_manifest() {
        let manifest =
            render_fsv_manifest(canonical_fsv_dir()).unwrap_or_else(|err| panic!("{err}"));
        std::fs::write(canonical_fsv_dir().join(FSV_MANIFEST_FILE), manifest).unwrap();
    }

    /// The tracked manifest is what the tracked guests regenerate to, so every pinned digest,
    /// ROM size and text size is recomputed from the binaries, and the compiled-in copy equals it.
    #[test]
    fn manifest_matches_the_tracked_guests() {
        let tracked = std::fs::read_to_string(canonical_fsv_dir().join(FSV_MANIFEST_FILE)).unwrap();
        let rendered =
            render_fsv_manifest(canonical_fsv_dir()).unwrap_or_else(|err| panic!("{err}"));
        assert!(
            tracked == rendered,
            "{FSV_MANIFEST_FILE} is stale; run tools/gkr_verifier/dump_recursive_verifiers.sh"
        );
        assert!(
            MANIFEST == tracked,
            "the compiled-in {FSV_MANIFEST_FILE} is stale"
        );
        for entry in fsv_manifest() {
            assert!(
                entry.rom_bytes <= common_constants::ROM_BYTE_SIZE,
                "{} does not fit the ROM",
                entry.descriptor
            );
        }
    }

    /// Every guest binary under the FSV root is a registry row, so no file is loadable only by
    /// a name the registry does not know.
    #[test]
    fn no_unregistered_guest_binaries() {
        fn elves(dir: &Path, out: &mut Vec<PathBuf>) {
            for entry in std::fs::read_dir(dir).unwrap() {
                let path = entry.unwrap().path();
                if path.is_dir() {
                    elves(&path, out);
                } else if path.extension().is_some_and(|ext| ext == "elf") {
                    out.push(path);
                }
            }
        }
        let root = canonical_fsv_dir();
        let mut found = Vec::new();
        elves(&root, &mut found);
        for path in found {
            let relative = path.strip_prefix(&root).unwrap().to_str().unwrap();
            assert!(
                FSV_REGISTRY
                    .iter()
                    .any(|entry| entry.relative_path == relative),
                "{relative} is not in FSV_REGISTRY"
            );
        }
    }

    #[test]
    fn digest_keeps_the_bin_text_boundary() {
        assert_ne!(fsv_digest(&[1, 2], &[3]), fsv_digest(&[1], &[2, 3]));
    }

    #[test]
    fn manifest_has_one_row_per_registry_entry() {
        let manifest = fsv_manifest();
        assert_eq!(manifest.len(), FSV_REGISTRY.len());
        for (row, entry) in manifest.iter().zip(FSV_REGISTRY) {
            assert_eq!(row.descriptor, entry.descriptor);
            assert_eq!(row.relative_path, entry.relative_path);
        }
        for (i, a) in manifest.iter().enumerate() {
            for b in &manifest[i + 1..] {
                assert_ne!(a.digest, b.digest, "{} and {}", a.descriptor, b.descriptor);
            }
        }
    }

    #[test]
    fn every_registered_guest_loads_from_the_canonical_dir() {
        for entry in FSV_REGISTRY {
            let program = load_fsv_exact(canonical_fsv_dir(), &entry.descriptor)
                .unwrap_or_else(|err| panic!("{err}"));
            assert_eq!(*program.descriptor(), entry.descriptor);
        }
    }

    #[test]
    fn relocated_copy_loads() {
        let unified = descriptor(
            PESSIMISTIC,
            FsvProgram::UnifiedRecursionLayer,
            BlakeMode::Compression,
        );
        let dir = ScratchDir::new("relocated", &[(&unified, &unified)]);
        let program = load_fsv_exact(&dir.0, &unified).unwrap();
        assert_eq!(
            program.digest(),
            fsv_manifest_entry(&unified).unwrap().digest
        );
    }

    #[test]
    fn pessimistic_guest_at_the_ethproofs_path_is_rejected() {
        let pessimistic = descriptor(
            PESSIMISTIC,
            FsvProgram::UnrolledBaseLayer,
            BlakeMode::Compression,
        );
        let ethproofs = FsvDescriptor {
            soundness_mode: ETHPROOFS,
            ..pessimistic
        };
        let dir = ScratchDir::new("pessimistic-at-ethproofs", &[(&pessimistic, &ethproofs)]);
        match load_fsv_exact(&dir.0, &ethproofs) {
            Err(FsvLoadError::WrongArtifact { found, .. }) => assert_eq!(found, pessimistic),
            other => panic!("expected WrongArtifact, got {other:?}"),
        }
    }

    #[test]
    fn ethproofs_guest_at_the_pessimistic_path_is_rejected() {
        let ethproofs = descriptor(
            ETHPROOFS,
            FsvProgram::UnrolledRecursionLayer,
            BlakeMode::Compression,
        );
        let pessimistic = FsvDescriptor {
            soundness_mode: PESSIMISTIC,
            ..ethproofs
        };
        let dir = ScratchDir::new("ethproofs-at-pessimistic", &[(&ethproofs, &pessimistic)]);
        match load_fsv_exact(&dir.0, &pessimistic) {
            Err(FsvLoadError::WrongArtifact { found, .. }) => assert_eq!(found, ethproofs),
            other => panic!("expected WrongArtifact, got {other:?}"),
        }
    }

    #[test]
    fn swapped_blake_variant_is_rejected() {
        for mode in SoundnessMode::ALL {
            let compression = descriptor(
                *mode,
                FsvProgram::UnifiedRecursionLayer,
                BlakeMode::Compression,
            );
            let special = FsvDescriptor {
                blake: BlakeMode::BlakeSpecialOpcodes,
                ..compression
            };
            let dir = ScratchDir::new("swapped-blake", &[(&compression, &special)]);
            match load_fsv_exact(&dir.0, &special) {
                Err(FsvLoadError::WrongArtifact { found, .. }) => assert_eq!(found, compression),
                other => panic!("expected WrongArtifact, got {other:?}"),
            }
        }
    }

    #[test]
    fn tampered_rom_byte_is_rejected() {
        let target = descriptor(
            ETHPROOFS,
            FsvProgram::UnrolledBaseLayer,
            BlakeMode::Compression,
        );
        let dir = ScratchDir::new("tampered", &[(&target, &target)]);
        let path = dir.0.join(path_of(&target));
        let mut elf = std::fs::read(&path).unwrap();
        // ELF32: e_phoff at 0x1c; the first program header's p_offset/p_filesz at +4/+16. Flip a
        // byte in the middle of the first loaded segment, which lands in the ROM image.
        let word = |at: usize| u32::from_le_bytes(elf[at..at + 4].try_into().unwrap()) as usize;
        let phoff = word(0x1c);
        let (offset, size) = (word(phoff + 4), word(phoff + 16));
        assert!(size > 0);
        elf[offset + size / 2] ^= 0x01;
        std::fs::write(&path, elf).unwrap();
        match load_fsv_exact(&dir.0, &target) {
            Err(FsvLoadError::DigestMismatch {
                expected, actual, ..
            }) => assert_ne!(expected, actual),
            other => panic!("expected DigestMismatch, got {other:?}"),
        }
    }

    #[test]
    fn missing_file_is_reported() {
        let target = descriptor(
            ETHPROOFS,
            FsvProgram::UnifiedRecursionLayer,
            BlakeMode::BlakeSpecialOpcodes,
        );
        let dir = ScratchDir::new("missing", &[]);
        match load_fsv_exact(&dir.0, &target) {
            Err(FsvLoadError::MissingArtifact { path, .. }) => {
                assert_eq!(path, dir.0.join(path_of(&target)));
            }
            other => panic!("expected MissingArtifact, got {other:?}"),
        }
    }

    #[test]
    fn unbuilt_variants_are_unsupported() {
        let unified_base = descriptor(
            ETHPROOFS,
            FsvProgram::UnifiedBaseLayer,
            BlakeMode::Compression,
        );
        let feeder = FsvDescriptor {
            profile: FsvProfile::L1Feeder,
            ..descriptor(
                ETHPROOFS,
                FsvProgram::UnifiedRecursionLayer,
                BlakeMode::BlakeSpecialOpcodes,
            )
        };
        let g_function = descriptor(
            PESSIMISTIC,
            FsvProgram::UnrolledBaseLayer,
            BlakeMode::GFunction,
        );
        for target in [unified_base, feeder, g_function] {
            match load_fsv_exact(canonical_fsv_dir(), &target) {
                Err(FsvLoadError::Unsupported(err)) => assert_eq!(err.descriptor, target),
                other => panic!("expected Unsupported for {target}, got {other:?}"),
            }
        }
    }

    #[test]
    fn legacy_wrapper_loads_the_unsuffixed_unified_base() {
        let (bin, text) = load_fsv_program(
            canonical_fsv_dir(),
            FsvProgram::UnifiedBaseLayer,
            BlakeMode::Compression,
        );
        let pinned = fsv_manifest_entry(&descriptor(
            PESSIMISTIC,
            FsvProgram::UnifiedBaseLayer,
            BlakeMode::Compression,
        ))
        .unwrap();
        assert_eq!(fsv_digest(&bin, &text), pinned.digest);
        assert_eq!(pinned.relative_path, "fsv_unified_base_layer_sec_100.elf");
    }

    #[test]
    fn manifest_parser_rejects_inconsistent_rows() {
        let header = format!("# digest: {FSV_DIGEST_RECIPE} = ...\n");
        let row = |path: &str| {
            format!(
                "sec_100 ethproofs_soundcalc unified_base_layer standard blake2_with_compression \
                 {path} 4 4 {}\n",
                "00".repeat(32)
            )
        };
        let err = parse_manifest(&format!("{header}{}", row("x.elf"))).unwrap_err();
        assert!(err.contains("names no registered guest"), "{err}");

        let wrong_path = format!(
            "{header}sec_100 pessimistic_conjecture unified_base_layer standard \
             blake2_with_compression other.elf 4 4 {}\n",
            "00".repeat(32)
        );
        let err = parse_manifest(&wrong_path).unwrap_err();
        assert!(err.contains("the registry places"), "{err}");

        let err = parse_manifest("sec_100\n").unwrap_err();
        assert!(err.contains("does not declare"), "{err}");
    }
}
