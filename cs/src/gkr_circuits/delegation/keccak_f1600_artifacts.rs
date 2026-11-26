use super::keccak_chi5::*;
use super::keccak_column_parity::*;
use super::keccak_theta_rho::*;
use crate::gkr_compiler::compile_delegation_circuit_into_gkr_without_caches;
use crate::utils::serialize_to_file;
use ::field::baby_bear::base::BabyBearField;
use test_utils::skip_if_ci;

type F = BabyBearField;

macro_rules! write_no_cache_layout {
    ($stem:literal, $tables:path, $circuit:path) => {{
        let layout = compile_delegation_circuit_into_gkr_without_caches::<F>(
            &|cs| $tables(cs),
            &|cs| $circuit(cs),
            22,
        );
        serialize_to_file(
            &layout,
            concat!("compiled_circuits/", $stem, "_layout_no_caches_gkr.json"),
        );
    }};
}

#[test]
fn compile_keccak_column_parity_into_no_caches_gkr() {
    skip_if_ci!();
    write_no_cache_layout!(
        "keccak_column_parity",
        keccak_column_parity_delegation_circuit_table_addition_fn,
        define_keccak_column_parity_delegation_circuit
    );
}

#[test]
fn compile_keccak_theta_rho_into_no_caches_gkr() {
    skip_if_ci!();
    write_no_cache_layout!(
        "keccak_theta_rho",
        keccak_theta_rho_delegation_circuit_table_addition_fn,
        define_keccak_theta_rho_delegation_circuit
    );
}

#[test]
fn compile_keccak_chi5_into_no_caches_gkr() {
    skip_if_ci!();
    write_no_cache_layout!(
        "keccak_chi5",
        keccak_chi5_delegation_circuit_table_addition_fn,
        define_keccak_chi5_delegation_circuit
    );
}
