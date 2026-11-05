//! Reduced-VM oracle for the shipped `memcpy` and `memset` bodies of a registered, digest-verified
//! verifier guest: each runs from its entry with arguments in `a0`..`a2` and `ra` at the guest's
//! exit loop. Valid word arguments return with the expected memory, residues stop at the trap
//! word, and zero length touches nothing even for pointers outside RAM (the VM bounds-checks RAM
//! only in debug builds, so those cases rely on returning before any access). `memmove` is linked
//! by no verifier guest; the runtime's host tests cover it.

use super::fsv::{canonical_fsv_dir, fsv_manifest_entry, load_fsv_exact};
use common_constants::{INITIAL_TIMESTAMP, ROM_SECOND_WORD_BITS};
use object::{Object, ObjectSymbol, SymbolKind};
use riscv_transpiler::cycle::{MachineConfig, ReducedMachineWithDelegation};
use riscv_transpiler::ir::simple_instruction_set::{preprocess_bytecode, Instruction};
use riscv_transpiler::vm::{
    DelegationsAndUnifiedCounters, RamPeek, RamWithRomRegion, SimpleTape, State, RAM, VM,
};
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::fsv_binaries::FSV_REGISTRY;

const TRAP: u32 = 0xc000_1073;
const RAM_BOUND: usize = 1 << 30;
const SOURCE: u32 = 0x0100_0000;
const DESTINATION: u32 = 0x0110_0000;
const STACK_TOP: u32 = 0x0200_0000;
/// Words checked after a written range, which must keep their sentinel.
const GUARD_WORDS: u32 = 4;
const SENTINEL: u32 = 0xa5a5_a5a5;

struct Guest {
    bin: Vec<u32>,
    instructions: Vec<Instruction>,
    memcpy: u32,
    memset: u32,
    text: Vec<u32>,
    exit: u32,
}

fn guest() -> Guest {
    let entry = fsv_manifest_entry(&FSV_REGISTRY[0].descriptor);
    let verified = load_fsv_exact(canonical_fsv_dir(), &entry.descriptor);
    let bytes = std::fs::read(canonical_fsv_dir().join(entry.relative_path)).unwrap();
    let file = object::File::parse(&*bytes).unwrap();
    let function = |wanted: &dyn Fn(&str) -> bool| {
        let found: Vec<_> = file
            .symbols()
            .filter(|symbol| symbol.kind() == SymbolKind::Text && wanted(symbol.name().unwrap()))
            .map(|symbol| (symbol.address() as u32, symbol.size() as u32))
            .collect();
        assert_eq!(found.len(), 1, "exactly one matching FUNC symbol");
        found[0]
    };
    let (memcpy, _) = function(&|name| name == "memcpy");
    let (memset, _) = function(&|name| name == "memset");
    let text = verified.text();
    Guest {
        bin: verified.bin().to_vec(),
        instructions: preprocess_bytecode::<
            <ReducedMachineWithDelegation as MachineConfig>::DecodingOptions,
            true,
        >(text),
        memcpy,
        memset,
        text: text.to_vec(),
        exit: setups::program_setups::find_binary_exit_point(verified.bin()),
    }
}

/// Runs the routine at `entry` with arguments `args`, after writing `memory` (address, word).
/// Returns the final state and RAM, or the VM's panic message.
fn call(
    guest: &Guest,
    entry: u32,
    args: [u32; 3],
    memory: &[(u32, u32)],
) -> Result<
    (
        State<DelegationsAndUnifiedCounters>,
        RamWithRomRegion<{ ROM_SECOND_WORD_BITS }>,
    ),
    String,
> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let tape = SimpleTape::new(&guest.instructions);
        let mut ram =
            RamWithRomRegion::<{ ROM_SECOND_WORD_BITS }>::from_rom_content(&guest.bin, RAM_BOUND);
        for &(address, word) in memory {
            ram.write_word(address, word, 0);
        }
        let mut state = State::initial_with_counters(DelegationsAndUnifiedCounters::default());
        assert!(state.timestamp >= INITIAL_TIMESTAMP);
        state.pc = entry;
        state.registers[1].value = guest.exit;
        state.registers[2].value = STACK_TOP;
        state.registers[8].value = STACK_TOP;
        for (register, value) in (10..13).zip(args) {
            state.registers[register].value = value;
        }
        let finished = VM::<DelegationsAndUnifiedCounters>::run_basic_unrolled::<
            _,
            _,
            _,
            BabyBearField,
        >(&mut state, &mut ram, &mut (), &tape, 1 << 16, &mut ());
        assert!(
            finished,
            "the routine did not return within the cycle bound"
        );
        assert_eq!(
            state.pc, guest.exit,
            "the routine stopped outside its return address"
        );
        (state, ram)
    }))
    .map_err(|payload| {
        payload
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_owned()))
            .unwrap_or_default()
    })
}

fn word(index: u32) -> u32 {
    index.wrapping_mul(0x9e37_79b9) ^ 0x5bd1_e995
}

/// `words` source words at `SOURCE`, sentinels at and after `DESTINATION`.
fn copy_memory(words: u32) -> Vec<(u32, u32)> {
    (0..words)
        .map(|i| (SOURCE + 4 * i, word(i)))
        .chain((0..words + GUARD_WORDS).map(|i| (DESTINATION + 4 * i, SENTINEL)))
        .collect()
}

/// The call must stop at the VM's `Illegal` refusal of a PC holding exactly the trap word.
fn assert_trap(guest: &Guest, result: Result<impl Sized, String>, case: &str) {
    let message = result
        .err()
        .unwrap_or_else(|| panic!("{case}: the routine returned"));
    let pc = message
        .split("PC = 0x")
        .nth(1)
        .and_then(|rest| u32::from_str_radix(&rest[..8], 16).ok())
        .unwrap_or_else(|| panic!("{case}: not an Illegal-instruction refusal: {message}"));
    assert!(message.contains("Illegal instruction"), "{case}: {message}");
    assert_eq!(
        guest.text.get((pc / 4) as usize),
        Some(&TRAP),
        "{case}: refused at {pc:#010x}, which is not the trap"
    );
}

#[test]
fn shipped_memcpy_copies_word_ranges() {
    let guest = guest();
    for words in [1, 2, 15, 16, 17, 64, 65] {
        let (state, ram) = call(
            &guest,
            guest.memcpy,
            [DESTINATION, SOURCE, 4 * words],
            &copy_memory(words),
        )
        .unwrap_or_else(|message| panic!("{words} words: {message}"));
        assert_eq!(state.registers[10].value, DESTINATION);
        for i in 0..words {
            assert_eq!(
                ram.peek_word(DESTINATION + 4 * i),
                word(i),
                "{words} words, word {i}"
            );
        }
        for i in words..words + GUARD_WORDS {
            assert_eq!(
                ram.peek_word(DESTINATION + 4 * i),
                SENTINEL,
                "{words} words, guard {i}"
            );
        }
    }
    // Equal operands are allowed and leave memory unchanged.
    let memory = copy_memory(16);
    let (_, ram) = call(&guest, guest.memcpy, [SOURCE, SOURCE, 64], &memory).unwrap();
    for i in 0..16 {
        assert_eq!(ram.peek_word(SOURCE + 4 * i), word(i));
    }
}

#[test]
fn shipped_memset_fills_the_low_byte() {
    let guest = guest();
    for (value, fill) in [(0x1ab, 0xabab_abab), (u32::MAX, u32::MAX), (0, 0)] {
        for words in [1, 16, 17, 65] {
            let memory: Vec<_> = (0..words + GUARD_WORDS)
                .map(|i| (DESTINATION + 4 * i, SENTINEL))
                .collect();
            let (state, ram) = call(
                &guest,
                guest.memset,
                [DESTINATION, value, 4 * words],
                &memory,
            )
            .unwrap();
            assert_eq!(state.registers[10].value, DESTINATION);
            for i in 0..words {
                assert_eq!(
                    ram.peek_word(DESTINATION + 4 * i),
                    fill,
                    "value {value:#x} words {words}"
                );
            }
            for i in words..words + GUARD_WORDS {
                assert_eq!(ram.peek_word(DESTINATION + 4 * i), SENTINEL);
            }
        }
    }
}

#[test]
fn shipped_routines_trap_on_unsupported_arguments() {
    let guest = guest();
    let memory = copy_memory(16);
    for residue in 1..4 {
        assert_trap(
            &guest,
            call(
                &guest,
                guest.memcpy,
                [DESTINATION, SOURCE + residue, 64],
                &memory,
            ),
            "memcpy src residue",
        );
        assert_trap(
            &guest,
            call(
                &guest,
                guest.memcpy,
                [DESTINATION + residue, SOURCE, 64],
                &memory,
            ),
            "memcpy dst residue",
        );
        assert_trap(
            &guest,
            call(
                &guest,
                guest.memcpy,
                [DESTINATION, SOURCE, 64 - residue],
                &memory,
            ),
            "memcpy len residue",
        );
        assert_trap(
            &guest,
            call(
                &guest,
                guest.memset,
                [DESTINATION + residue, 0x5a, 64],
                &memory,
            ),
            "memset dst residue",
        );
        assert_trap(
            &guest,
            call(
                &guest,
                guest.memset,
                [DESTINATION, 0x5a, 64 - residue],
                &memory,
            ),
            "memset len residue",
        );
    }
}

#[test]
fn shipped_routines_touch_nothing_for_zero_length() {
    let guest = guest();
    // Misaligned pointers outside RAM: any access would fault the bounds-checked debug VM or be
    // out of range.
    for (destination, source) in [(0xffff_fff1, 0xffff_fff3), (0xffff_fffc, 3)] {
        let (state, _) = call(&guest, guest.memcpy, [destination, source, 0], &[]).unwrap();
        assert_eq!(state.registers[10].value, destination);
        let (state, _) = call(&guest, guest.memset, [destination, 0xff, 0], &[]).unwrap();
        assert_eq!(state.registers[10].value, destination);
    }
}
