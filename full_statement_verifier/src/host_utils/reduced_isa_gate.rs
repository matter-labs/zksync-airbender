//! Static reduced-machine ISA gate over every registered full-statement verifier guest.
//!
//! The reduced machine decodes no byte or halfword memory access, so such an instruction in a
//! guest fails only when it executes. The gate decodes each registered guest's raw `.text` with the
//! reduced decoder, without delegation-run protection (classification only), and accepts an
//! `Illegal` word only if it is
//! - the exact `unimp` trap [`TRAP`], which refuses when it is reached, or
//! - a reviewed byte/halfword site of `memcpy` or `memset`, by exact offset and word, inside that
//!   function's body: the unique FUNC symbol of that name, whose complete bytes match the pinned
//!   size and Keccak-256.
//!
//! Any other `Illegal` word, a changed body, size or site, or a missing or ambiguous body symbol
//! fails. The pinned sites are the inherited `memcpy`/`memset` fallbacks for misaligned pointers
//! and lengths that are not a multiple of 4; they stay in the guests, and the gate pins them
//! instead of removing them. Recorded verifier runs reached none of them, which covers those
//! inputs only: the gate does not prove that no input reaches a fallback.

use super::fsv::{canonical_fsv_dir, fsv_manifest_entry, load_fsv_exact, FsvManifestEntry};
use object::{Object, ObjectSection, ObjectSymbol, SymbolKind};
use riscv_transpiler::ir::simple_instruction_set::{preprocess_bytecode, InstructionName};
use riscv_transpiler::ir::ReducedMachineDecoderConfig;
use sha3::{Digest, Keccak256};
use verifier_common::fsv_binaries::FSV_REGISTRY;

/// `unimp` (`csrrw x0, cycle, x0`), the deliberate refusing trap.
const TRAP: u32 = 0xc000_1073;

struct PinnedBody {
    name: &'static str,
    size: u64,
    keccak256: &'static str,
    /// Reviewed `Illegal` words: (byte offset in the body, word).
    sites: &'static [(u32, u32)],
}

/// The reviewed bodies. `memcpy`: SHA-256 5681170d2c307e2842a68b0435ef53589eb4e96d085208d4e26a88dba1e0b043; `memset`: SHA-256
/// 0cd1f9f06b83600a8d30e8f43df35ee75d4993fad70cf6f7f97d24cfbb7cf072. The Keccak-256 pins are of the same bytes.
const BODIES: [PinnedBody; 2] = [
    PinnedBody {
        name: "memcpy",
        size: 6704,
        keccak256: "2f04529be5adf0e82688f732c50fd426ac15663a00af4f200a59033cf551da0a",
        sites: &MEMCPY_SITES,
    },
    PinnedBody {
        name: "memset",
        size: 392,
        keccak256: "383fca952851fd872b7b1fad6e23b225ff8905ea2f590aa8a2b062c08bf60895",
        sites: &MEMSET_SITES,
    },
];

const MEMCPY_SITES: [(u32, u32); 154] = [
    (0x00fc, 0x0005c703),
    (0x0100, 0x00e50023),
    (0x0104, 0x0015c703),
    (0x0108, 0x00e500a3),
    (0x0118, 0x0005c583),
    (0x0120, 0x00b68023),
    (0x0150, 0x0005c703),
    (0x0154, 0x00e50023),
    (0x0194, 0x0005c683),
    (0x0198, 0x00d50023),
    (0x019c, 0x0015c683),
    (0x01a0, 0x00d500a3),
    (0x01a4, 0x0025c683),
    (0x01a8, 0x00d50123),
    (0x01ac, 0x0035c683),
    (0x01b0, 0x00d501a3),
    (0x01b4, 0x0045c683),
    (0x01b8, 0x00d50223),
    (0x01bc, 0x0055c683),
    (0x01c0, 0x00d502a3),
    (0x01c4, 0x0065c683),
    (0x01c8, 0x00d50323),
    (0x01cc, 0x0075c683),
    (0x01d0, 0x00d503a3),
    (0x01d4, 0x0085c683),
    (0x01d8, 0x00d50423),
    (0x01dc, 0x0095c683),
    (0x01e0, 0x00d504a3),
    (0x01e4, 0x00a5c683),
    (0x01e8, 0x00d50523),
    (0x01ec, 0x00b5c683),
    (0x01f0, 0x00d505a3),
    (0x01f4, 0x00c5c683),
    (0x01f8, 0x00d50623),
    (0x01fc, 0x00d5c683),
    (0x0200, 0x00d506a3),
    (0x0204, 0x00e5c683),
    (0x0208, 0x00d50723),
    (0x020c, 0x00f5c683),
    (0x0210, 0x00d507a3),
    (0x0224, 0x0005c703),
    (0x0228, 0x00e68023),
    (0x022c, 0x0015c703),
    (0x0230, 0x00e680a3),
    (0x0234, 0x0025c703),
    (0x0238, 0x00e68123),
    (0x023c, 0x0035c703),
    (0x0240, 0x00e681a3),
    (0x0244, 0x0045c703),
    (0x0248, 0x00e68223),
    (0x024c, 0x0055c703),
    (0x0250, 0x00e682a3),
    (0x0254, 0x0065c703),
    (0x0258, 0x00e68323),
    (0x025c, 0x0075c703),
    (0x0264, 0x00e683a3),
    (0x0280, 0x0005c703),
    (0x0284, 0x00e68023),
    (0x0288, 0x0015c703),
    (0x028c, 0x00e680a3),
    (0x0290, 0x0025c703),
    (0x0294, 0x00e68123),
    (0x0298, 0x0035c703),
    (0x02a0, 0x00e681a3),
    (0x02b0, 0x0005c703),
    (0x02b4, 0x00e68023),
    (0x02b8, 0x0015c703),
    (0x02c0, 0x00e680a3),
    (0x02dc, 0x00f50023),
    (0x02f0, 0x00e500a3),
    (0x0498, 0x00059603),
    (0x04b0, 0x0025c583),
    (0x04b4, 0x00b68223),
    (0x04d0, 0x0005c703),
    (0x04d4, 0x00e50023),
    (0x04d8, 0x0015c703),
    (0x04dc, 0x00e500a3),
    (0x0500, 0x0007d703),
    (0x0694, 0x00061683),
    (0x06ac, 0x00264603),
    (0x06b0, 0x00c58223),
    (0x06c4, 0x0005c683),
    (0x06cc, 0x00d50023),
    (0x06e0, 0x00059703),
    (0x06e8, 0x00e69023),
    (0x0888, 0x00059703),
    (0x0890, 0x00e69023),
    (0x08a0, 0x0005c583),
    (0x08a4, 0x00b68023),
    (0x08b8, 0x0007c703),
    (0x0a4c, 0x00065683),
    (0x0a50, 0x00264603),
    (0x0a78, 0x0005c703),
    (0x0a7c, 0x00e50023),
    (0x0a80, 0x0015c703),
    (0x0a84, 0x00e500a3),
    (0x0a88, 0x0025c703),
    (0x0a8c, 0x00e50123),
    (0x0aa8, 0x0017d683),
    (0x0aac, 0x0007c703),
    (0x0c44, 0x00064783),
    (0x0c68, 0x00164603),
    (0x0c6c, 0x00c58223),
    (0x0c88, 0x00e500a3),
    (0x0c8c, 0x00d50123),
    (0x0e1c, 0x0005d603),
    (0x0e20, 0x0025c583),
    (0x0fd0, 0x0005c783),
    (0x0ff4, 0x0015c583),
    (0x0ff8, 0x00b68223),
    (0x117c, 0xffe64703),
    (0x1180, 0x00e58023),
    (0x1184, 0xfff64703),
    (0x118c, 0x00e580a3),
    (0x1194, 0x00064603),
    (0x1198, 0x00c58123),
    (0x1318, 0xffd64683),
    (0x131c, 0x00d58023),
    (0x1320, 0xffe64683),
    (0x1324, 0x00d580a3),
    (0x1328, 0xfff64603),
    (0x132c, 0x00c58123),
    (0x14bc, 0xfff64783),
    (0x14c0, 0x00f58023),
    (0x14c4, 0x00064783),
    (0x14c8, 0x00f580a3),
    (0x14d8, 0xfff64603),
    (0x14e0, 0x00c58023),
    (0x14f4, 0x00164683),
    (0x14f8, 0x00d58223),
    (0x14fc, 0x00264603),
    (0x1500, 0x00c582a3),
    (0x1694, 0xffe5c703),
    (0x1698, 0x00e68023),
    (0x169c, 0xfff5c703),
    (0x16a4, 0x00e680a3),
    (0x16ac, 0x0005c583),
    (0x16b0, 0x00b68123),
    (0x1840, 0xfff5c783),
    (0x1844, 0x00f68023),
    (0x1848, 0x0005c783),
    (0x184c, 0x00f680a3),
    (0x1860, 0xfff5c583),
    (0x1868, 0x00b68023),
    (0x19e8, 0xffd5c603),
    (0x19ec, 0x00c68023),
    (0x19f0, 0xffe5c603),
    (0x19f4, 0x00c680a3),
    (0x19f8, 0xfff5c583),
    (0x19fc, 0x00b68123),
    (0x1a10, 0x0015c603),
    (0x1a14, 0x00c68223),
    (0x1a18, 0x0025c583),
    (0x1a1c, 0x00b682a3),
];

const MEMSET_SITES: [(u32, u32); 2] = [(0x003c, 0x00b68023), (0x0070, 0x00b80023)];

/// A guest's raw `.text` at `address` and its FUNC symbols as (name, address, size).
struct GuestText {
    address: u64,
    words: Vec<u32>,
    functions: Vec<(String, u64, u64)>,
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn check_reduced_isa(text: &GuestText, bodies: &[PinnedBody]) -> Result<(), String> {
    let end = text.address + 4 * text.words.len() as u64;
    let mut pinned = Vec::with_capacity(bodies.len());
    for body in bodies {
        let matches: Vec<_> = text
            .functions
            .iter()
            .filter(|(name, ..)| name == body.name)
            .collect();
        let &(_, start, size) = match matches.as_slice() {
            [] => return Err(format!("MissingBody: no FUNC symbol {}", body.name)),
            [function] => *function,
            _ => {
                return Err(format!(
                    "AmbiguousBody: {} FUNC symbols named {}",
                    matches.len(),
                    body.name
                ))
            }
        };
        if size != body.size || start < text.address || start + size > end || start % 4 != 0 {
            return Err(format!(
                "ChangedBody: {} at {start:#x} has {size} bytes, pinned {}",
                body.name, body.size
            ));
        }
        let first = ((start - text.address) / 4) as usize;
        let mut hasher = Keccak256::new();
        for word in &text.words[first..first + (size / 4) as usize] {
            hasher.update(word.to_le_bytes());
        }
        let digest = hex(&hasher.finalize());
        if digest != body.keccak256 {
            return Err(format!(
                "ChangedBody: {} Keccak-256 {digest}, pinned {}",
                body.name, body.keccak256
            ));
        }
        pinned.push((body, first));
    }
    let decoded = preprocess_bytecode::<ReducedMachineDecoderConfig, false>(&text.words);
    for (index, instruction) in decoded.iter().enumerate() {
        if instruction.name != InstructionName::Illegal || text.words[index] == TRAP {
            continue;
        }
        let word = text.words[index];
        let address = text.address + 4 * index as u64;
        let owner = pinned
            .iter()
            .find(|(body, first)| (*first..*first + (body.size / 4) as usize).contains(&index));
        match owner {
            Some((body, first)) => {
                let offset = (4 * (index - first)) as u32;
                if !body.sites.contains(&(offset, word)) {
                    return Err(format!(
                        "UnreviewedSite: {}+{offset:#x} {word:#010x}",
                        body.name
                    ));
                }
            }
            None => {
                return Err(format!(
                    "IllegalOutsidePinnedBodies: {address:#x} {word:#010x}"
                ))
            }
        }
    }
    for (body, first) in &pinned {
        for &(offset, word) in body.sites {
            let index = first + (offset / 4) as usize;
            if decoded[index].name != InstructionName::Illegal || text.words[index] != word {
                return Err(format!(
                    "StaleSite: {}+{offset:#x} is not the reviewed Illegal word {word:#010x}",
                    body.name
                ));
            }
        }
    }
    Ok(())
}

/// The raw `.text` of a registered guest, bound to the digest-verified guest the loader accepts.
fn guest_text(entry: &FsvManifestEntry) -> GuestText {
    let verified = load_fsv_exact(canonical_fsv_dir(), &entry.descriptor);
    let bytes = std::fs::read(canonical_fsv_dir().join(entry.relative_path)).unwrap();
    let file = object::File::parse(&*bytes).unwrap();
    let section = file
        .section_by_name(".text")
        .expect("guest has a .text section");
    let data = section.data().unwrap();
    assert_eq!(
        data.len(),
        entry.text_bytes,
        "{}: raw .text length differs from the manifest",
        entry.descriptor
    );
    let words: Vec<u32> = data
        .chunks_exact(4)
        .map(|chunk| u32::from_le_bytes(chunk.try_into().unwrap()))
        .collect();
    assert_eq!(
        &verified.text()[..words.len()],
        &words[..],
        "{}: raw .text differs from the verified guest",
        entry.descriptor
    );
    let functions = file
        .symbols()
        .filter(|symbol| symbol.kind() == SymbolKind::Text)
        .map(|symbol| {
            (
                symbol.name().unwrap().to_owned(),
                symbol.address(),
                symbol.size(),
            )
        })
        .collect();
    GuestText {
        address: section.address(),
        words,
        functions,
    }
}

#[test]
fn every_registered_guest_passes_the_reduced_isa_gate() {
    for registered in FSV_REGISTRY {
        let entry = fsv_manifest_entry(&registered.descriptor);
        check_reduced_isa(&guest_text(entry), &BODIES)
            .unwrap_or_else(|error| panic!("{}: {error}", registered.descriptor));
    }
}

fn fixture() -> GuestText {
    guest_text(fsv_manifest_entry(&FSV_REGISTRY[0].descriptor))
}

fn decodes_illegal(word: u32) -> bool {
    preprocess_bytecode::<ReducedMachineDecoderConfig, false>(&[word])[0].name
        == InstructionName::Illegal
}

/// The first word of the text, which lies before both pinned bodies and is a legal instruction.
fn outside_index(text: &GuestText) -> usize {
    let index = 0;
    assert!(!decodes_illegal(text.words[index]));
    for (name, start, _) in &text.functions {
        if BODIES.iter().any(|body| body.name == name) {
            assert!(text.address + 4 * (index as u64) < *start);
        }
    }
    index
}

/// `body` with another reviewed site list.
fn with_sites(body: &PinnedBody, sites: &'static [(u32, u32)]) -> PinnedBody {
    PinnedBody {
        name: body.name,
        size: body.size,
        keccak256: body.keccak256,
        sites,
    }
}

fn refusal(text: &GuestText, bodies: &[PinnedBody]) -> String {
    check_reduced_isa(text, bodies).expect_err("the gate must refuse")
}

#[test]
fn exact_trap_outside_the_bodies_is_accepted() {
    let mut text = fixture();
    let index = outside_index(&text);
    assert!(decodes_illegal(TRAP));
    text.words[index] = TRAP;
    check_reduced_isa(&text, &BODIES).unwrap();
}

#[test]
fn subword_access_outside_the_bodies_is_refused() {
    let mut text = fixture();
    let index = outside_index(&text);
    let lbu = MEMCPY_SITES[0].1;
    assert!(decodes_illegal(lbu));
    text.words[index] = lbu;
    assert!(refusal(&text, &BODIES).starts_with("IllegalOutsidePinnedBodies: "));
}

#[test]
fn other_illegal_word_is_refused() {
    let mut text = fixture();
    let index = outside_index(&text);
    // `csrrs x0, time, x0`: an Illegal CSR access that is not the `unimp` trap.
    let word = 0xc010_2073;
    assert!(decodes_illegal(word) && word != TRAP);
    text.words[index] = word;
    assert!(refusal(&text, &BODIES).starts_with("IllegalOutsidePinnedBodies: "));
}

#[test]
fn changed_body_is_refused() {
    let mut text = fixture();
    let (_, start, _) = text
        .functions
        .iter()
        .find(|(name, ..)| name == "memset")
        .unwrap()
        .clone();
    let index = ((start - text.address) / 4) as usize;
    text.words[index] ^= 1 << 20;
    assert!(refusal(&text, &BODIES).starts_with("ChangedBody: memset Keccak-256 "));
    let mut resized = fixture();
    for function in resized.functions.iter_mut() {
        if function.0 == "memset" {
            function.2 += 4;
        }
    }
    assert!(refusal(&resized, &BODIES).starts_with("ChangedBody: memset at "));
}

#[test]
fn unreviewed_and_stale_sites_are_refused() {
    let text = fixture();
    let fewer = [
        with_sites(&BODIES[0], &MEMCPY_SITES[1..]),
        with_sites(&BODIES[1], &MEMSET_SITES),
    ];
    assert_eq!(
        refusal(&text, &fewer),
        format!(
            "UnreviewedSite: memcpy+{:#x} {:#010x}",
            MEMCPY_SITES[0].0, MEMCPY_SITES[0].1
        )
    );
    let extra: Vec<(u32, u32)> = MEMSET_SITES.iter().copied().chain([(0, 0)]).collect();
    let extra: &'static [(u32, u32)] = Box::leak(extra.into_boxed_slice());
    let more = [
        with_sites(&BODIES[0], &MEMCPY_SITES),
        with_sites(&BODIES[1], extra),
    ];
    assert!(refusal(&text, &more).starts_with("StaleSite: memset+0x0 "));
}

#[test]
fn missing_or_ambiguous_body_symbols_are_refused() {
    let mut missing = fixture();
    missing.functions.retain(|(name, ..)| name != "memcpy");
    assert_eq!(
        refusal(&missing, &BODIES),
        "MissingBody: no FUNC symbol memcpy"
    );
    let mut ambiguous = fixture();
    let memcpy = ambiguous
        .functions
        .iter()
        .find(|(name, ..)| name == "memcpy")
        .unwrap()
        .clone();
    ambiguous.functions.push(memcpy);
    assert_eq!(
        refusal(&ambiguous, &BODIES),
        "AmbiguousBody: 2 FUNC symbols named memcpy"
    );
}
