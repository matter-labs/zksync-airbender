mod binding;

pub(crate) use binding::{
    bind_main_tail_pr, launch_main_tail_pr, MainTailLaunchPr, MainTailLaunchedPr,
    MainTailRuntimePr, PR_MAIN_TAIL_KERNEL_ARGUMENT_BYTES,
};
