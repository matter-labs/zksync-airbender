//! Check the authenticated startup program after the zero-decoder row poisons x0.
//! This covers the VM consequence; the separate PoC proof covers the forged row.

use field::baby_bear::base::BabyBearField;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::ir::simple_instruction_set::{preprocess_bytecode, InstructionName};
use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;
use riscv_transpiler::vm::{
    DelegationsAndFamiliesCounters, RamWithRomRegion, SimpleSnapshotter, SimpleTape, State, VM,
};

#[test]
fn add_sub_startup_vm_paths() {
    let read_words = |path| -> Vec<u32> {
        std::fs::read(path)
            .unwrap()
            .chunks_exact(4)
            .map(|b| u32::from_le_bytes(b.try_into().unwrap()))
            .collect()
    };
    let binary = read_words("../examples/add_sub_zero_decoder_poc/app.bin");
    let text = read_words("../examples/add_sub_zero_decoder_poc/app.text");
    assert_eq!(binary, text);
    let instructions = preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text);
    assert_eq!(instructions[0].name, InstructionName::Auipc);
    let tape = SimpleTape::new(&instructions);

    let run = |forged_x0: Option<u32>| {
        let mut ram =
            RamWithRomRegion::<{ common_constants::ROM_SECOND_WORD_BITS }>::from_rom_content(
                &binary,
                1 << 26,
            );
        let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());
        if let Some(value) = forged_x0 {
            // State immediately after the circuit-valid, forged PC-0 row.
            state.pc = 4;
            state.timestamp = 8;
            state.registers[0].timestamp = 6;
            state.registers[0].value = value;
        }
        let mut snapshotter = SimpleSnapshotter::<
            DelegationsAndFamiliesCounters,
            { common_constants::ROM_SECOND_WORD_BITS },
        >::new_with_cycle_limit(1 << 10, state);
        let mut nd = QuasiUARTSource::new_with_reads(vec![]);
        let finished =
            VM::<DelegationsAndFamiliesCounters>::run_basic_unrolled::<_, _, _, BabyBearField>(
                &mut state,
                &mut ram,
                &mut snapshotter,
                &tape,
                1 << 10,
                &mut nd,
            );
        (
            finished,
            state.pc,
            state.registers[0].value,
            state.registers[10].value,
        )
    };

    assert_eq!(run(None), (true, 24, 0, 1));
    assert_eq!(run(Some(8)), (true, 24, 0, 2));
}
