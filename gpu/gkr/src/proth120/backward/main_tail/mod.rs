mod binding;

#[cfg(test)]
pub(crate) use binding::PR_MAIN_TAIL_KERNEL_ARGUMENT_BYTES;
pub(crate) use binding::{bind_main_tail_pr, launch_main_tail_pr, MainTailRuntimePr};
