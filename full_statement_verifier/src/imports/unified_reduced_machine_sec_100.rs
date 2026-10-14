#[path = "../../../verifier/src/generated/unified_reduced_machine/sec_100/mod.rs"]
mod generated_gkr;

pub use generated_gkr::constants::{
    ConcreteVerifierOutput, CAP_SIZE, INIT_AND_TEARDOWN_SETS, NUM_MEMORY_COMMITS,
    NUM_SETUP_COMMITS, TRACE_LEN_LOG2,
};
pub use generated_gkr::verify;
