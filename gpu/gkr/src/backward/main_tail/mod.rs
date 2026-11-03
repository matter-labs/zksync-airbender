mod abi;
mod binding;

pub(crate) use binding::{
    bind_main_tail, launch_main_tail, MainTailLaunched, MainTailRuntimeState,
};

pub use gpu_gkr_compiler::MainTailProgram;
