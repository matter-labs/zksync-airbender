use crate::ir::simple_instruction_set::InstructionName;
use crate::jit::JitRunnerRam;
use crate::vm::Instruction;
use crate::vm::InstructionTape;

pub struct SimpleTape {
    instructions: Box<[Instruction]>,
}

impl SimpleTape {
    pub fn new(instructions: &[Instruction]) -> Self {
        Self {
            instructions: instructions.to_vec().into_boxed_slice(),
        }
    }

    pub fn word_group_widths(&self, ram_config: JitRunnerRam) -> Vec<u8> {
        use InstructionName as Op;

        let mut widths = vec![1; self.instructions.len()];
        if self.instructions.is_empty() || ram_config as u64 > (1 << 30) {
            return widths;
        }

        let mut static_targets = vec![false; self.instructions.len()];
        static_targets[0] = true;
        for (i, instr) in self.instructions.iter().enumerate() {
            if matches!(instr.name, Op::Jal | Op::Branch) {
                let target = i as i64 * 4 + instr.imm as i32 as i64;
                if target >= 0 && target % 4 == 0 {
                    if let Some(is_target) = static_targets.get_mut((target / 4) as usize) {
                        *is_target = true;
                    }
                }
            }
        }

        let mut i = 0;
        while i < self.instructions.len() {
            let head = self.instructions[i];
            if !matches!(head.name, Op::Lw | Op::Sw) {
                i += 1;
                continue;
            }

            let mut run = 1;
            while run < 4 && i + run < self.instructions.len() {
                let prev = self.instructions[i + run - 1];
                let next = self.instructions[i + run];
                if (head.name == Op::Lw && prev.rd == head.rs1)
                    || static_targets[i + run]
                    || next.name != head.name
                    || next.rs1 != head.rs1
                    || next.imm.wrapping_sub(prev.imm) != 4
                {
                    break;
                }
                run += 1;
            }

            let width = match run {
                4 => 4,
                2 | 3 => 2,
                _ => 1,
            };
            widths[i] = width;
            i += usize::from(width);
        }

        widths
    }
}

impl InstructionTape for SimpleTape {
    #[inline(always)]
    fn read_instruction(&self, pc: u32) -> Instruction {
        unsafe {
            let word = (pc >> 2) as usize;
            debug_assert!(word < self.instructions.len());
            *self.instructions.get_unchecked(word)
        }
    }
}
