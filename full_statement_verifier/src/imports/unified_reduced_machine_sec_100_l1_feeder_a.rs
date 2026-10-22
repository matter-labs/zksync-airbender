#[path = "../../../verifier/src/generated/unified_reduced_machine/sec_100_l1_feeder_a/mod.rs"]
mod generated_gkr;

pub use generated_gkr::constants::{
    ConcreteVerifierOutput, BATCHED_PROXIMITY_POW_BITS, CAP_SIZE, INIT_AND_TEARDOWN_SETS,
    LOOKUP_CHALLENGES_POW_BITS, NUM_MEMORY_COMMITS, NUM_SETUP_COMMITS, TRACE_LEN_LOG2,
    WHIR_POW_BITS, WHIR_QUERIES,
};
pub use generated_gkr::verify;
