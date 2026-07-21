// These constants are a function of the configured FRI rate and folding strategy for it in the "prover"
// crate. All strategies for the same rate have the same CAP_SIZE and NUM_COSETS
pub const CAP_SIZE: usize = 64;
pub const NUM_COSETS: usize = 2;
pub const NUM_DELEGATION_CHALLENGES: usize = 1;

use verifier_common::prover::definitions::MerkleTreeCap;
// Local copy of circuit_defs/setups/generated/all_delegation_circuits_params.rs so this
// crate is self-contained for publishing (it is no_std and cannot depend on the std `setups`
// crate). Keep in sync when regenerating verifier params.
include!("../generated/all_delegation_circuits_params.rs");
