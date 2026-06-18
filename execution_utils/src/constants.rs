// These constants are a function of the configured FRI rate and folding strategy for it in the "prover"
// crate. All strategies for the same rate have the same CAP_SIZE and NUM_COSETS
pub const CAP_SIZE: usize = 64;
pub const NUM_COSETS: usize = 2;

use verifier_common::prover::definitions::MerkleTreeCap;

#[allow(dead_code)]
mod all_delegation_circuits_params {
    use super::MerkleTreeCap;

    include!("../../circuit_defs/setups/generated/all_delegation_circuits_params.rs");
}

#[allow(unused_imports)]
pub use all_delegation_circuits_params::*;
