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
use prover::definitions::SecurityLevel;

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

pub fn produce_verifier_setup_for_all_delegations(
    use_caches: bool,
    security_level: SecurityLevel,
) -> Vec<verifier_common::DelegationCircuitSetupData<{ prover::definitions::DEFAULT_CAP_SIZE }>> {
    let worker = Worker::new();
    let mut result = vec![];
    {
        let setup = make_setup_for_delegation_circuit::<Blake2sWithCompressionDelegationCircuit>(
            use_caches,
        );
        let setup_data = produce_verifier_setup_for_circuit(&setup, security_level, &worker);
        result.push(setup_data);
    }
    {
        let setup = make_setup_for_delegation_circuit::<BigIntDelegationCircuit>(use_caches);
        let setup_data = produce_verifier_setup_for_circuit(&setup, security_level, &worker);
        result.push(setup_data);
    }
    {
        let setup =
            make_setup_for_delegation_circuit::<KeccakSpecial5DelegationCircuit>(use_caches);
        let setup_data = produce_verifier_setup_for_circuit(&setup, security_level, &worker);
        result.push(setup_data);
    }
    {
        let setup =
            make_setup_for_delegation_circuit::<Blake2sGFunctionDelegationCircuit>(use_caches);
        let setup_data = produce_verifier_setup_for_circuit(&setup, security_level, &worker);
        result.push(setup_data);
    }

    result
}

fn produce_verifier_setup_for_circuit(
    circuit: &DelegationCircuitSetup,
    security_level: SecurityLevel,
    worker: &Worker,
) -> verifier_common::DelegationCircuitSetupData<{ prover::definitions::DEFAULT_CAP_SIZE }> {
    use prover::merkle_trees::ColumnMajorMerkleTreeConstructor;

    let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(circuit.trace_len.trailing_zeros() as usize, security_level);
    let twiddles: Twiddles<BabyBearField, Global> = Twiddles::new(circuit.trace_len, worker);
    let setup_commitment = circuit.setup.commit::<DefaultTreeConstructor>(
        &twiddles,
        prover_config.lde_factor,
        prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
        prover_config.cap_size,
        circuit.trace_len.trailing_zeros() as usize,
        worker,
    );

    let cap = <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BabyBearField>>::get_cap(
        &setup_commitment.tree,
    );
    let mut num_permutation_terms_per_cycle = 1; // delegation itself
    num_permutation_terms_per_cycle += circuit.compiled_circuit.memory_layout.ram_access_sets.len();

    verifier_common::DelegationCircuitSetupData {
        delegation_type: circuit.delegation_type as u32,
        num_permutation_terms_per_circuit: (num_permutation_terms_per_cycle * circuit.trace_len)
            as u32,
        setup_cap: MerkleTreeCap {
            cap: cap.cap.try_into().unwrap(),
        },
    }
}

pub fn dump_delegation_setups_for_verifier(use_caches: bool, security_level: SecurityLevel) {
    use quote::quote;
    use quote::TokenStreamExt;

    let all_params = produce_verifier_setup_for_all_delegations(use_caches, security_level);
    let mut streams = Vec::with_capacity(all_params.len());
    let num_circuits = all_params.len();

    for el in all_params.into_iter() {
        let t = quote! {
            #el
        };
        streams.push(t);
    }

    let mut full_stream = proc_macro2::TokenStream::new();
    full_stream.append_separated(
        streams.into_iter().map(|el| {
            quote! { #el }
        }),
        quote! {,},
    );

    let cap_size = prover::definitions::DEFAULT_CAP_SIZE;
    let description = quote! {
        pub const DELEGATION_CIRCUITS_SETUP_PARAMS: [::verifier_common::DelegationCircuitSetupData<#cap_size>; #num_circuits] = [#full_stream];
    };

    let suffix = match security_level {
        SecurityLevel::Sec80 => "80",
        SecurityLevel::Sec100 => "100",
    };

    write_and_fmt(
        &format!("generated/delegation_parameters_{}.rs", suffix),
        &description,
    );
}

fn write_and_fmt(path: &str, content: &proc_macro2::TokenStream) {
    use std::io::Write;
    let mut dst = std::fs::File::create(path).unwrap();
    dst.write_all(content.to_string().as_bytes()).unwrap();
    drop(dst);
    std::process::Command::new("rustfmt")
        .arg(path)
        .status()
        .ok();
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn generate_delegation_circuits_artifacts() {
        dump_delegation_setups_for_verifier(true, SecurityLevel::Sec80);
    }
}
