#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![feature(allocator_api)]

//! GKR wiring for the unified reduced-machine circuit.
//!
//! The unified circuit folds every executor family (and its inline
//! inits-and-teardowns) into a single GKR circuit. This crate mirrors the
//! per-family GKR circuit crates (e.g. `add_sub_lui_auipc_mop`): it exposes
//! the compiled GKR artifact, the table driver, and the witness-eval fn so the
//! `setups` crate can build a `CircuitSetup` for it.

use prover::cs;
use prover::cs::tables::TableDriver;
use prover::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
use prover::field::baby_bear::base::BabyBearField;
use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use prover::gkr::witness_gen::oracles::UnifiedRiscvCircuitOracle;

pub use common_constants::circuit_families::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as FAMILY_IDX;

/// The unified circuit is compiled with a `1 << 24` row domain (see
/// `compile_family_circuit_with_inline_inits_and_teardowns` in `cs`).
pub const TRACE_LEN_LOG2: u32 = 24;
pub const DOMAIN_SIZE: usize = 1 << TRACE_LEN_LOG2;
pub const NUM_CYCLES: usize = DOMAIN_SIZE;
pub const LDE_FACTOR: usize = 2;
pub const MAX_ROM_SIZE: usize = common_constants::rom::ROM_BYTE_SIZE;
pub const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize = common_constants::rom::ROM_SECOND_WORD_BITS;

pub const ALLOWED_DELEGATION_CSRS: &[u32] = &[
    common_constants::NON_DETERMINISM_CSR,
    common_constants::BLAKE2S_DELEGATION_CSR_REGISTER,
];
pub const ALLOWED_DELEGATION_CSRS_U16: &[u16] = &[
    common_constants::NON_DETERMINISM_CSR as u16,
    common_constants::BLAKE2S_DELEGATION_CSR_REGISTER as u16,
];

/// Compile (or load from cache) the unified GKR circuit artifact. The artifact
/// shape is bytecode-independent (special-table *content* is supplied at
/// table-driver/setup time), so this takes no bytecode.
pub fn get_circuit(
    use_caches: bool,
) -> cs::gkr_compiler::GKRCircuitArtifact<BabyBearField> {
    cs::gkr_circuits::unified_reduced_machine::build_unified_artifact::<BabyBearField>(use_caches)
}

/// Build the table driver for the unified circuit. Base tables plus the
/// bytecode-dependent mem-word special tables, matching the prover-side
/// `build_unified_table_driver` used during witness generation.
pub fn get_table_driver(binary: &[u32]) -> TableDriver<BabyBearField> {
    prover::gkr::witness_gen::family_circuits::build_unified_table_driver::<BabyBearField>(binary)
}

mod sealed {
    use super::*;
    use prover::cs::oracle::Placeholder;
    use prover::cs::witness_placer::*;
    use prover::gkr::witness_gen::witness_proxy::*;

    include!("../generated/witness_generation_fn.rs");
}

/// Witness-eval fn for the unified circuit, specialized to the GKR
/// `ColumnMajorWitnessProxy` / `UnifiedRiscvCircuitOracle` over `BabyBearField`.
pub fn witness_eval_fn(
    proxy: &'_ mut ColumnMajorWitnessProxy<'_, UnifiedRiscvCircuitOracle<'_>, BabyBearField>,
) {
    let fn_ptr = sealed::evaluate_witness_fn::<
        ScalarWitnessTypeSet<BabyBearField, true>,
        ColumnMajorWitnessProxy<'_, UnifiedRiscvCircuitOracle<'_>, BabyBearField>,
    >;
    (fn_ptr)(proxy);
}
