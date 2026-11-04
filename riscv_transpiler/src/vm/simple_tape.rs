use crate::{ir::Instruction, vm::InstructionTape};

pub struct SimpleTape {
    instructions: Box<[Instruction]>,
}

impl SimpleTape {
    pub fn new(instructions: &[Instruction]) -> Self {
        Self {
            instructions: instructions.to_vec().into_boxed_slice(),
        }
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
