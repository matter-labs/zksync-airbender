//! The generated per-circuit verifiers, one module per soundness mode
//! (`verifier/src/generated/<circuit>/<mode>/`, included by path).
//!
//! The circuit OUTPUT types are mode-independent (parameterised by the
//! circuit's geometry only), so the aliases below come from the default mode
//! and every other mode's are asserted to be the same types.

// These modules contain generated verifiers with shape-dependent unused inputs.
#[allow(unused_variables)]
pub mod ethproofs_soundcalc;
#[allow(unused_variables)]
pub mod pessimistic_conjecture;

pub type UnrolledCircuitOutput =
    pessimistic_conjecture::add_sub_lui_auipc_mop::ConcreteVerifierOutput;
pub type InitsAndTeardownsCircuitOutput =
    pessimistic_conjecture::inits_and_teardowns::ConcreteVerifierOutput;
pub type DelegationCircuitOutput =
    pessimistic_conjecture::blake2_with_extended_control::ConcreteVerifierOutput;
pub type UnifiedCircuitOutput =
    pessimistic_conjecture::unified_reduced_machine::ConcreteVerifierOutput;

const _: fn(
    ethproofs_soundcalc::add_sub_lui_auipc_mop::ConcreteVerifierOutput,
) -> UnrolledCircuitOutput = |o| o;
const _: fn(
    ethproofs_soundcalc::inits_and_teardowns::ConcreteVerifierOutput,
) -> InitsAndTeardownsCircuitOutput = |o| o;
const _: fn(
    ethproofs_soundcalc::blake2_with_extended_control::ConcreteVerifierOutput,
) -> DelegationCircuitOutput = |o| o;
const _: fn(
    ethproofs_soundcalc::unified_reduced_machine::ConcreteVerifierOutput,
) -> UnifiedCircuitOutput = |o| o;

pub mod unified_reduced_machine_sec_100_l1_feeder;
pub mod unified_reduced_machine_sec_100_l1_feeder_a;

/// The unified verifier output at setup cap `CAP`: the standard verifier's
/// shape (`UnifiedCircuitOutput` at [`prover::definitions::DEFAULT_CAP_SIZE`])
/// and the L1 feeder verifier's at its generated `CAP_SIZE`.
pub type UnifiedCircuitOutputWithCap<const CAP: usize> = verifier_common::VerifierOutput<
    verifier_common::field::baby_bear::ext4::BabyBearExt4,
    { pessimistic_conjecture::unified_reduced_machine::INIT_AND_TEARDOWN_SETS },
    CAP,
    { pessimistic_conjecture::unified_reduced_machine::NUM_MEMORY_COMMITS },
    { pessimistic_conjecture::unified_reduced_machine::NUM_SETUP_COMMITS },
>;
const _: () = assert!(
    unified_reduced_machine_sec_100_l1_feeder::INIT_AND_TEARDOWN_SETS
        == pessimistic_conjecture::unified_reduced_machine::INIT_AND_TEARDOWN_SETS
);
const _: () = assert!(
    unified_reduced_machine_sec_100_l1_feeder::NUM_MEMORY_COMMITS
        == pessimistic_conjecture::unified_reduced_machine::NUM_MEMORY_COMMITS
);
const _: () = assert!(
    unified_reduced_machine_sec_100_l1_feeder::NUM_SETUP_COMMITS
        == pessimistic_conjecture::unified_reduced_machine::NUM_SETUP_COMMITS
);
