#[path = "../../../../verifier/src/generated/unified_reduced_machine/ethproofs_soundcalc/mod.rs"]
mod generated_gkr;

pub use generated_gkr::constants::{
    ConcreteVerifierOutput, INIT_AND_TEARDOWN_SETS, TRACE_LEN_LOG2,
};
pub use generated_gkr::verify;
