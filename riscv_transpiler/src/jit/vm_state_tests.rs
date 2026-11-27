use super::*;
use crate::ir::simple_instruction_set::{Instruction, InstructionName as Op};

#[test]
fn packed_state_round_trip() {
    let base = 1 << 33;
    for phase in 0..4 {
        let mut state = State::initial_with_counters(MachineCounters::new());
        state.pc = 0x120;
        state.timestamp = base + 32 * TIMESTAMP_STEP;
        state.counters[CounterType::MemWord as usize] = 41 + phase;
        state.counters.bump_keccak_f1600(2);

        for (r, register) in state.registers.iter_mut().enumerate() {
            let residue = (r as u64 + phase) % TIMESTAMP_STEP;
            register.timestamp = if residue == 3 && !matches!(r, 10..=12) {
                0
            } else {
                base + r as u64 * TIMESTAMP_STEP + residue
            };
            if r != 0 && register.timestamp != 0 {
                register.value = 0xfeed_dc00 + r as u32;
            }
        }

        assert_eq!(State::from(MachineState::from(&state)), state);
    }
}

#[test]
fn machine_counters_match_replay_counters() {
    fn count<const FAMILY: u8>(counters: &mut MachineCounters, by: usize) {
        counters.log_circuit_family::<FAMILY>();
        counters.log_multiple_circuit_family_calls::<FAMILY>(by);
        assert_eq!(counters.get_calls_to_circuit_family::<FAMILY>(), 1 + by);
    }

    let mut counters = MachineCounters::new();
    count::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(&mut counters, 1);
    count::<JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX>(&mut counters, 2);
    count::<SHIFT_BINARY_CIRCUIT_FAMILY_IDX>(&mut counters, 3);
    count::<MUL_DIV_CIRCUIT_FAMILY_IDX>(&mut counters, 4);
    count::<LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX>(&mut counters, 5);
    count::<LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX>(&mut counters, 6);
    counters.bump_bigint(8);
    counters.bump_blake2_round_function(9);
    counters.bump_keccak_special5(10);
    counters.bump_keccak_f1600(11);
    counters.bump_blake2_g_function(12);

    assert_eq!(counters.values[..6].iter().sum::<u64>(), 27);
    assert_eq!(
        DelegationsAndFamiliesCounters::from(counters),
        DelegationsAndFamiliesCounters {
            add_sub_family: 2,
            slt_branch_family: 3,
            binary_shift_family: 4,
            mul_div_family: 5,
            word_size_mem_family: 6,
            subword_size_mem_family: 7,
            bigint_calls: 8,
            blake_calls: 9,
            keccak_calls: 10,
            keccak_f1600_calls: 11,
            blake_g_function_calls: 12,
        }
    );
    assert_eq!(
        DelegationsAndUnifiedCounters::from(counters),
        DelegationsAndUnifiedCounters {
            cycles: 27,
            bigint_calls: 8,
            blake_calls: 9,
            keccak_calls: 10,
            keccak_f1600_calls: 11,
            blake_g_function_calls: 12,
            ..Default::default()
        }
    );
}

#[test]
fn flat_words_allow_fresh_runs() {
    let words = [0x1234_5678, 0xfedc_ba98];
    let source = FlatResponsesSource::new_with_reads(words.to_vec());
    for _ in 0..2 {
        let read_words = [0, 1].map(|index| source.read_flattened_word(index));
        assert_eq!(read_words, words);
    }
}

#[test]
#[should_panic(expected = "VM flattened non-determinism exhausted at index 2 (length 2)")]
fn flat_words_fail_at_exact_exhaustion() {
    let source = FlatResponsesSource::new_with_reads(vec![0x1234_5678, 0xfedc_ba98]);
    assert_eq!(source.read_flattened_word(1), 0xfedc_ba98);
    source.read_flattened_word(2);
}

pub(super) fn word_group_programs() -> [(Vec<Instruction>, Vec<u8>); 5] {
    let base = Instruction::pure_from_imm(Op::Add, 0, 0, 5, 1 << 23);
    let halt = Instruction::from_imm(Op::Jal, 0, 0, 0, 0);
    let loads = [
        base,
        Instruction::from_imm(Op::Lw, 5, 0, 6, 0),
        Instruction::from_imm(Op::Lw, 5, 0, 7, 4),
        Instruction::from_imm(Op::Lw, 5, 0, 8, 8),
        Instruction::from_imm(Op::Lw, 5, 0, 9, 12),
        halt,
    ];
    let mut stores = vec![base];
    stores.extend(
        (-8i32..=16)
            .step_by(4)
            .map(|offset| Instruction::from_imm(Op::Sw, 5, 0, 0, offset as u32)),
    );
    stores.push(halt);

    let mut branch_target = loads.to_vec();
    branch_target.push(Instruction::from_imm(Op::Branch, 0, 0, 0, -12i32 as u32));
    let mut jal_target = loads.to_vec();
    jal_target.push(Instruction::from_imm(Op::Jal, 0, 0, 0, -16i32 as u32));

    let mut clobber = loads;
    clobber[2].rd = 5;
    [
        (loads.to_vec(), vec![1, 4, 1, 1, 1, 1]),
        (stores, vec![1, 4, 1, 1, 1, 2, 1, 1, 1]),
        (branch_target, vec![1, 2, 1, 2, 1, 1, 1]),
        (jal_target, vec![1, 1, 2, 1, 1, 1, 1]),
        (clobber.to_vec(), vec![1, 2, 1, 2, 1, 1]),
    ]
}

#[test]
fn word_group_widths_respect_heads_and_ram_policy() {
    for (program, expected) in word_group_programs() {
        let tape = SimpleTape::new(&program);
        for ram_config in [
            JitRunnerRam::Tiny,
            JitRunnerRam::Small,
            JitRunnerRam::Medium,
        ] {
            assert_eq!(tape.word_group_widths(ram_config), expected, "{program:?}");
        }
        assert_eq!(
            tape.word_group_widths(JitRunnerRam::Full),
            vec![1; program.len()]
        );
    }
}
