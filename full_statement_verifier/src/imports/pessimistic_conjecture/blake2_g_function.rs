#[path = "../../../../verifier/src/generated/blake2_g_function/pessimistic_conjecture/mod.rs"]
mod generated_gkr;

pub use generated_gkr::constants::{ConcreteVerifierOutput, INIT_AND_TEARDOWN_SETS, TRACE_LEN_LOG2};
pub use generated_gkr::verify;
