mod binding;
mod program;

pub(crate) use binding::{
    bind_main_tail, launch_main_tail, MainTailLaunched, MainTailRuntimeState,
};

pub(crate) use program::lower_main_tail_program;
pub use program::MainTailProgram;
