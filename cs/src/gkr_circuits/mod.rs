use super::*;
use crate::definitions::*;
use riscv_transpiler::ir::simple_instruction_set::*;

pub(crate) mod utils;

pub mod add_sub_family;
pub mod binary_shifts_family;
pub mod decoder_trait;
pub mod delegation;
pub mod jump_branch_slt_family;
pub mod mem_subword_only;
pub mod mem_word_only;
pub mod mul_div;

pub use self::add_sub_family::*;
pub use self::binary_shifts_family::*;
pub use self::decoder_trait::*;
pub use self::delegation::*;
pub use self::jump_branch_slt_family::*;
pub use self::mem_subword_only::*;
pub use self::mem_word_only::*;
pub use self::mul_div::*;
