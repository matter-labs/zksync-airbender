//! The generated per-circuit verifiers, one module per soundness mode
//! (`verifier/src/generated/<circuit>/<mode>/`, included by path).
//!
//! The circuit OUTPUT types are mode-independent (parameterised by the
//! circuit's geometry only), so the aliases below come from the default mode
//! and every other mode's are asserted to be the same types.

pub mod ethproofs_soundcalc;
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
