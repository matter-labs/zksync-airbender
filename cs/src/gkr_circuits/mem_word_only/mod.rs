use super::*;

mod circuit;
mod decoder;

pub use self::circuit::{
    create_mem_word_only_special_tables, mem_word_only_circuit_with_preprocessed_bytecode_for_gkr,
    mem_word_only_table_addition_fn, mem_word_only_table_driver_fn,
};
pub(crate) use self::circuit::apply_mem_word_only_inner;
pub use self::decoder::*;
