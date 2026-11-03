#[path = "../../../verifier/src/generated/inits_and_teardowns/sec_100/mod.rs"]
mod generated_gkr;

pub use generated_gkr::constants::{
    ConcreteVerifierOutput, INIT_AND_TEARDOWN_SETS, TRACE_LEN_LOG2,
};
pub use generated_gkr::verify;
