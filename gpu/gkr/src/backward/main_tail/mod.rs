mod binding;
mod program;

pub(crate) use binding::{
    bind_main_tail, launch_main_tail, MainTailLaunched, MainTailRuntimeState,
};

pub use program::MainTailProgram;
#[allow(unused_imports)] // Task 4 consumes the fixed blob metadata and typed error.
pub(crate) use program::{
    lower_main_tail_program, MainTailProgramError, MAIN_TAIL_BLOB_ALIGNMENT, MAIN_TAIL_BLOB_BYTES,
    MAIN_TAIL_IMMEDIATE_CAPACITY, MAIN_TAIL_IMMEDIATE_OFFSET, MAIN_TAIL_K, MAIN_TAIL_LIST_OFFSETS,
    MAIN_TAIL_LIST_OFFSETS_OFFSET, MAIN_TAIL_PROGRAM_OFFSET, MAIN_TAIL_PROGRAM_WORD_CAPACITY,
    MAIN_TAIL_SOURCE_CAPACITY,
};

#[cfg(test)]
mod tests;

#[cfg(test)]
mod reference;

#[cfg(test)]
#[path = "tests/gpu.rs"]
mod gpu_tests;
