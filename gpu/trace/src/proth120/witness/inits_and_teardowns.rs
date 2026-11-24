crate::witness::memory_unrolled::define_inits_and_teardowns!(
    gpu_core::primitives::field::PR,
    generate_inits_and_teardowns,
    ab_pr_generate_inits_and_teardowns_kernel
);
