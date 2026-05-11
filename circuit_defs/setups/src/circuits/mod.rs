use super::*;

mod bigint_ops_with_control_circuit;
mod blake2_g_function_circuit;
mod blake2_with_compression_circuit;
mod keccak_special5_circuit;

pub use self::bigint_ops_with_control_circuit::get_bigint_with_control_circuit_setup;
pub use self::blake2_g_function_circuit::get_blake2_g_function_circuit_setup;
pub use self::blake2_with_compression_circuit::get_blake2_with_compression_circuit_setup;
pub use self::keccak_special5_circuit::get_keccak_special5_circuit_setup;

#[cfg(feature = "witness_eval_fn")]
pub use ::bigint_with_control::witness_eval_fn as bigint_witness_eval_fn;
#[cfg(feature = "witness_eval_fn")]
pub use ::blake2_g_function::witness_eval_fn as blake2_g_function_witness_eval_fn;
#[cfg(feature = "witness_eval_fn")]
pub use ::blake2_with_compression::witness_eval_fn as blake2_with_compression_witness_eval_fn;
#[cfg(feature = "witness_eval_fn")]
pub use ::keccak_special5::witness_eval_fn as keccak_special5_witness_eval_fn;

pub struct DelegationCircuitSetup {
    pub delegation_type: u16,
    pub trace_len: usize,
    pub compiled_circuit: GKRCircuitArtifact<BabyBearField>,
    pub table_driver: TableDriver<BabyBearField>,
    pub setup: GKRSetup<BabyBearField>,
    // pub witness_eval_fn: Option<
    //     fn(&'_ mut ColumnMajorWitnessProxy<'_, M, BabyBearField>)
    // >,
}

pub fn make_setup_for_delegation_circuit<C: circuit_common::DelegationCircuit<BabyBearField>>(
    use_caches: bool,
) -> DelegationCircuitSetup {
    let circuit = C::get_circuit(use_caches);
    let table_driver = C::get_table_driver();
    let setup = GKRSetup::construct(&table_driver, &[], 1 << C::DOMAIN_SIZE_LOG2, &circuit);

    DelegationCircuitSetup {
        delegation_type: C::DELEGATION_TYPE_ID,
        trace_len: 1 << C::DOMAIN_SIZE_LOG2,
        compiled_circuit: circuit,
        table_driver,
        setup,
    }
}
