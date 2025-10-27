use crate::ir::*;
use crate::vm::*;
use std::collections::HashMap;

mod add;
mod addi;
// mod beq;
mod mul;
// mod mulh;
mod mulhu;
// mod rem;
mod slt;
mod sltu;
mod sra;

const INITIAL_PC: u32 = 0;

fn test_reg_reg_op(op_name: &str, expected: u32, op1: u32, op2: u32) {
    type CountersT = DelegationsAndFamiliesCounters;
    {
        let period = 1;
        let num_snapshots = 1;
        let cycles_bound = period * num_snapshots;

        let mut state = State::initial_with_counters(CountersT::default());
        state.registers[1].value = op1;
        state.registers[2].value = op2;

        let mut snapshotter: SimpleSnapshotter<CountersT, 5> =
            SimpleSnapshotter::new_with_cycle_limit(cycles_bound, period, state);

        let instr = format!("{} x3, x1, x2", op_name);
        let mut empty_hash: HashMap<String, u32> = HashMap::new();
        let encoding = lib_rv32_asm::assemble_ir(&instr, &mut empty_hash, INITIAL_PC)
            .unwrap()
            .unwrap();
        let text_section = vec![encoding];

        let instructions: Vec<Instruction> = text_section
            .iter()
            .copied()
            .map(|el| decode::<FullUnsignedMachineDecoderConfig>(el))
            .collect();
        let tape = SimpleTape::new(&instructions);
        let mut ram = RamWithRomRegion::<5>::from_rom_content(&text_section, 1 << 30);

        VM::<CountersT>::run_basic_unrolled::<
            SimpleSnapshotter<CountersT, 5>,
            RamWithRomRegion<5>,
            _,
        >(
            &mut state,
            num_snapshots,
            &mut ram,
            &mut snapshotter,
            &tape,
            period,
            &mut (),
        );

        assert!(state.registers[3].value == expected, "Unexpected output: expected 0x{:08x} for operation `{}` 0x{:08x}, 0x{:08x}, obtained 0x{:08x}", expected, op_name, op1, op2, state.registers[3].value);
    }
}

fn test_reg_imm_op(op_name: &str, expected: u32, op1: u32, imm: u16) {
    type CountersT = DelegationsAndFamiliesCounters;
    {
        let period = 1;
        let num_snapshots = 1;
        let cycles_bound = period * num_snapshots;

        let mut state = State::initial_with_counters(CountersT::default());
        state.registers[1].value = op1;

        let mut snapshotter: SimpleSnapshotter<CountersT, 5> =
            SimpleSnapshotter::new_with_cycle_limit(cycles_bound, period, state);

        let instr = format!("{} x3, x1, 0x{:x}", op_name, imm);
        let mut empty_hash: HashMap<String, u32> = HashMap::new();
        let encoding = lib_rv32_asm::assemble_ir(&instr, &mut empty_hash, INITIAL_PC)
            .unwrap()
            .unwrap();
        let text_section = vec![encoding];

        let instructions: Vec<Instruction> = text_section
            .iter()
            .copied()
            .map(|el| decode::<FullUnsignedMachineDecoderConfig>(el))
            .collect();
        let tape = SimpleTape::new(&instructions);
        let mut ram = RamWithRomRegion::<5>::from_rom_content(&text_section, 1 << 30);

        VM::<CountersT>::run_basic_unrolled::<
            SimpleSnapshotter<CountersT, 5>,
            RamWithRomRegion<5>,
            _,
        >(
            &mut state,
            num_snapshots,
            &mut ram,
            &mut snapshotter,
            &tape,
            period,
            &mut (),
        );

        assert!(state.registers[3].value == expected, "Unexpected output: expected 0x{:08x} for operation `{}` 0x{:08x}, 0x{:04x}, obtained 0x{:08x}", expected, op_name, op1, imm, state.registers[3].value);
    }
}

// fn test_branch_op<const TAKEN: bool>(op_name: &str, op1: u32, op2: u32) {
//     {
//         let mut state = RiscV32State::<IMStandardIsaConfig>::initial(INITIAL_PC);
//         state.observable.registers[1] = op1;
//         state.observable.registers[2] = op2;
//         let instr = format!("{} x1, x2, 0x08", op_name);
//         let mut empty_hash: HashMap<String, u32> = HashMap::new();
//         let encoding = lib_rv32_asm::assemble_ir(&instr, &mut empty_hash, INITIAL_PC)
//             .unwrap()
//             .unwrap();
//         let binary = vec![encoding, 0, 0, 0];
//         let mut memory = VectorMemoryImpl::new_for_byte_size(16); // use full RAM
//         for (idx, insn) in binary.iter().enumerate() {
//             memory.populate(
//                 INITIAL_PC + idx as u32 * (core::mem::size_of::<u32>() as u32),
//                 *insn,
//             );
//         }
//         let mut mmu = NoMMU::default();
//         state.cycle(&mut memory, &mut (), &mut mmu, &mut ZeroedSource);
//         assert!(state.observable.pc == 4 || state.observable.pc == 8);
//         if TAKEN {
//             assert!(
//                 state.observable.pc == 8,
//                 "Unexpected branching: expected to take a branch for operation `{}` 0x{:08x}, 0x{:08x}",
//                 op_name,
//                 op1,
//                 op2
//             );
//         } else {
//             assert!(state.observable.pc == 4, "Unexpected branching: expected to NOT take a branch for operation `{}` 0x{:08x}, 0x{:08x}", op_name, op1, op2);
//         }
//     }
// }

fn test_reg_reg_op_64(op_name: &str, expected: u64, op1: u64, op2: u64) {
    // truncate
    test_reg_reg_op(op_name, expected as u32, op1 as u32, op2 as u32)
}

fn test_reg_imm_op_64(op_name: &str, expected: u64, op1: u64, imm: u16) {
    // truncate
    test_reg_imm_op(op_name, expected as u32, op1 as u32, imm)
}
