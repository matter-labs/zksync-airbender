use std::{
    io::Write,
    path::Path,
    process::{Command, Stdio},
};

use proc_macro2::TokenStream;
use quote::{ToTokens, TokenStreamExt, quote};

fn main() {
    println!("Running PoW Config Generator");

    let challenge_field_size = verifier_common::MERSENNE31QUARTIC_SIZE_LOG2;
    let max_number_of_cycles =
        verifier_common::cs::one_row_compiler::MAX_NUMBER_OF_CYCLES.leading_zeros() as usize;

    let pow_bits_for_queries_for_80 = verifier_common::POW_BITS_FOR_80_SECURITY_BITS;
    let pow_bits_for_queries_for_100 = verifier_common::POW_BITS_FOR_100_SECURITY_BITS;

    let max_trace_len_log2 = *[
        risc_v_cycles_verifier::concrete::size_constants::TRACE_LEN_LOG2,
        reduced_risc_v_machine_verifier::concrete::size_constants::TRACE_LEN_LOG2,
        reduced_risc_v_log_23_machine_verifier::concrete::size_constants::TRACE_LEN_LOG2,
        blake2_with_compression_verifier::concrete::size_constants::TRACE_LEN_LOG2,
        bigint_with_control_verifier::concrete::size_constants::TRACE_LEN_LOG2,
        keccak_special5_verifier::concrete::size_constants::TRACE_LEN_LOG2,
        add_sub_lui_auipc_mop_verifier::concrete::size_constants::TRACE_LEN_LOG2,
        jump_branch_slt_verifier::concrete::size_constants::TRACE_LEN_LOG2,
        load_store_subword_only_verifier::concrete::size_constants::TRACE_LEN_LOG2,
        load_store_word_only_verifier::concrete::size_constants::TRACE_LEN_LOG2,
        mul_div_verifier::concrete::size_constants::TRACE_LEN_LOG2,
        mul_div_unsigned_verifier::concrete::size_constants::TRACE_LEN_LOG2,
        shift_binary_csr_verifier::concrete::size_constants::TRACE_LEN_LOG2,
        inits_and_teardowns_verifier::concrete::size_constants::TRACE_LEN_LOG2,
        unified_reduced_machine_verifier::concrete::size_constants::TRACE_LEN_LOG2,
    ]
    .iter()
    .max()
    .unwrap();

    let max_fri_factor_log2 = *[
        risc_v_cycles_verifier::concrete::size_constants::FRI_FACTOR_LOG2,
        reduced_risc_v_machine_verifier::concrete::size_constants::FRI_FACTOR_LOG2,
        reduced_risc_v_log_23_machine_verifier::concrete::size_constants::FRI_FACTOR_LOG2,
        blake2_with_compression_verifier::concrete::size_constants::FRI_FACTOR_LOG2,
        bigint_with_control_verifier::concrete::size_constants::FRI_FACTOR_LOG2,
        keccak_special5_verifier::concrete::size_constants::FRI_FACTOR_LOG2,
        add_sub_lui_auipc_mop_verifier::concrete::size_constants::FRI_FACTOR_LOG2,
        jump_branch_slt_verifier::concrete::size_constants::FRI_FACTOR_LOG2,
        load_store_subword_only_verifier::concrete::size_constants::FRI_FACTOR_LOG2,
        load_store_word_only_verifier::concrete::size_constants::FRI_FACTOR_LOG2,
        mul_div_verifier::concrete::size_constants::FRI_FACTOR_LOG2,
        mul_div_unsigned_verifier::concrete::size_constants::FRI_FACTOR_LOG2,
        shift_binary_csr_verifier::concrete::size_constants::FRI_FACTOR_LOG2,
        inits_and_teardowns_verifier::concrete::size_constants::FRI_FACTOR_LOG2,
        unified_reduced_machine_verifier::concrete::size_constants::FRI_FACTOR_LOG2,
    ]
    .iter()
    .max()
    .unwrap();

    let max_number_of_columns = *[
        risc_v_cycles_verifier::concrete::size_constants::NUM_WITNESS_OPENINGS
            + risc_v_cycles_verifier::concrete::size_constants::NUM_MEMORY_OPENINGS
            + risc_v_cycles_verifier::concrete::size_constants::NUM_SETUP_OPENINGS
            + risc_v_cycles_verifier::concrete::size_constants::NUM_STAGE2_OPENINGS,
        reduced_risc_v_machine_verifier::concrete::size_constants::NUM_WITNESS_OPENINGS
            + reduced_risc_v_machine_verifier::concrete::size_constants::NUM_MEMORY_OPENINGS
            + reduced_risc_v_machine_verifier::concrete::size_constants::NUM_SETUP_OPENINGS
            + reduced_risc_v_machine_verifier::concrete::size_constants::NUM_STAGE2_OPENINGS,
        reduced_risc_v_log_23_machine_verifier::concrete::size_constants::NUM_WITNESS_OPENINGS
            + reduced_risc_v_log_23_machine_verifier::concrete::size_constants::NUM_MEMORY_OPENINGS
            + reduced_risc_v_log_23_machine_verifier::concrete::size_constants::NUM_SETUP_OPENINGS
            + reduced_risc_v_log_23_machine_verifier::concrete::size_constants::NUM_STAGE2_OPENINGS,
        blake2_with_compression_verifier::concrete::size_constants::NUM_WITNESS_OPENINGS
            + blake2_with_compression_verifier::concrete::size_constants::NUM_MEMORY_OPENINGS
            + blake2_with_compression_verifier::concrete::size_constants::NUM_SETUP_OPENINGS
            + blake2_with_compression_verifier::concrete::size_constants::NUM_STAGE2_OPENINGS,
        bigint_with_control_verifier::concrete::size_constants::NUM_WITNESS_OPENINGS
            + bigint_with_control_verifier::concrete::size_constants::NUM_MEMORY_OPENINGS
            + bigint_with_control_verifier::concrete::size_constants::NUM_SETUP_OPENINGS
            + bigint_with_control_verifier::concrete::size_constants::NUM_STAGE2_OPENINGS,
        keccak_special5_verifier::concrete::size_constants::NUM_WITNESS_OPENINGS
            + keccak_special5_verifier::concrete::size_constants::NUM_MEMORY_OPENINGS
            + keccak_special5_verifier::concrete::size_constants::NUM_SETUP_OPENINGS
            + keccak_special5_verifier::concrete::size_constants::NUM_STAGE2_OPENINGS,
        add_sub_lui_auipc_mop_verifier::concrete::size_constants::NUM_WITNESS_OPENINGS
            + add_sub_lui_auipc_mop_verifier::concrete::size_constants::NUM_MEMORY_OPENINGS
            + add_sub_lui_auipc_mop_verifier::concrete::size_constants::NUM_SETUP_OPENINGS
            + add_sub_lui_auipc_mop_verifier::concrete::size_constants::NUM_STAGE2_OPENINGS,
        jump_branch_slt_verifier::concrete::size_constants::NUM_WITNESS_OPENINGS
            + jump_branch_slt_verifier::concrete::size_constants::NUM_MEMORY_OPENINGS
            + jump_branch_slt_verifier::concrete::size_constants::NUM_SETUP_OPENINGS
            + jump_branch_slt_verifier::concrete::size_constants::NUM_STAGE2_OPENINGS,
        load_store_subword_only_verifier::concrete::size_constants::NUM_WITNESS_OPENINGS
            + load_store_subword_only_verifier::concrete::size_constants::NUM_MEMORY_OPENINGS
            + load_store_subword_only_verifier::concrete::size_constants::NUM_SETUP_OPENINGS
            + load_store_subword_only_verifier::concrete::size_constants::NUM_STAGE2_OPENINGS,
        load_store_word_only_verifier::concrete::size_constants::NUM_WITNESS_OPENINGS
            + load_store_word_only_verifier::concrete::size_constants::NUM_MEMORY_OPENINGS
            + load_store_word_only_verifier::concrete::size_constants::NUM_SETUP_OPENINGS
            + load_store_word_only_verifier::concrete::size_constants::NUM_STAGE2_OPENINGS,
        mul_div_verifier::concrete::size_constants::NUM_WITNESS_OPENINGS
            + mul_div_verifier::concrete::size_constants::NUM_MEMORY_OPENINGS
            + mul_div_verifier::concrete::size_constants::NUM_SETUP_OPENINGS
            + mul_div_verifier::concrete::size_constants::NUM_STAGE2_OPENINGS,
        mul_div_unsigned_verifier::concrete::size_constants::NUM_WITNESS_OPENINGS
            + mul_div_unsigned_verifier::concrete::size_constants::NUM_MEMORY_OPENINGS
            + mul_div_unsigned_verifier::concrete::size_constants::NUM_SETUP_OPENINGS
            + mul_div_unsigned_verifier::concrete::size_constants::NUM_STAGE2_OPENINGS,
        shift_binary_csr_verifier::concrete::size_constants::NUM_WITNESS_OPENINGS
            + shift_binary_csr_verifier::concrete::size_constants::NUM_MEMORY_OPENINGS
            + shift_binary_csr_verifier::concrete::size_constants::NUM_SETUP_OPENINGS
            + shift_binary_csr_verifier::concrete::size_constants::NUM_STAGE2_OPENINGS,
        inits_and_teardowns_verifier::concrete::size_constants::NUM_WITNESS_OPENINGS
            + inits_and_teardowns_verifier::concrete::size_constants::NUM_MEMORY_OPENINGS
            + inits_and_teardowns_verifier::concrete::size_constants::NUM_SETUP_OPENINGS
            + inits_and_teardowns_verifier::concrete::size_constants::NUM_STAGE2_OPENINGS,
        unified_reduced_machine_verifier::concrete::size_constants::NUM_WITNESS_OPENINGS
            + unified_reduced_machine_verifier::concrete::size_constants::NUM_MEMORY_OPENINGS
            + unified_reduced_machine_verifier::concrete::size_constants::NUM_SETUP_OPENINGS
            + unified_reduced_machine_verifier::concrete::size_constants::NUM_STAGE2_OPENINGS,
    ]
    .iter()
    .max()
    .unwrap();

    let max_num_quotient_terms = *[
        risc_v_cycles_verifier::concrete::size_constants::NUM_QUOTIENT_TERMS,
        reduced_risc_v_machine_verifier::concrete::size_constants::NUM_QUOTIENT_TERMS,
        reduced_risc_v_log_23_machine_verifier::concrete::size_constants::NUM_QUOTIENT_TERMS,
        blake2_with_compression_verifier::concrete::size_constants::NUM_QUOTIENT_TERMS,
        bigint_with_control_verifier::concrete::size_constants::NUM_QUOTIENT_TERMS,
        keccak_special5_verifier::concrete::size_constants::NUM_QUOTIENT_TERMS,
        add_sub_lui_auipc_mop_verifier::concrete::size_constants::NUM_QUOTIENT_TERMS,
        jump_branch_slt_verifier::concrete::size_constants::NUM_QUOTIENT_TERMS,
        load_store_subword_only_verifier::concrete::size_constants::NUM_QUOTIENT_TERMS,
        load_store_word_only_verifier::concrete::size_constants::NUM_QUOTIENT_TERMS,
        mul_div_verifier::concrete::size_constants::NUM_QUOTIENT_TERMS,
        mul_div_unsigned_verifier::concrete::size_constants::NUM_QUOTIENT_TERMS,
        shift_binary_csr_verifier::concrete::size_constants::NUM_QUOTIENT_TERMS,
        inits_and_teardowns_verifier::concrete::size_constants::NUM_QUOTIENT_TERMS,
        unified_reduced_machine_verifier::concrete::size_constants::NUM_QUOTIENT_TERMS,
    ]
    .iter()
    .max()
    .unwrap();

    let max_num_openings_at_z = *[
        risc_v_cycles_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z,
        reduced_risc_v_machine_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z,
        reduced_risc_v_log_23_machine_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z,
        blake2_with_compression_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z,
        bigint_with_control_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z,
        keccak_special5_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z,
        add_sub_lui_auipc_mop_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z,
        jump_branch_slt_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z,
        load_store_subword_only_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z,
        load_store_word_only_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z,
        mul_div_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z,
        mul_div_unsigned_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z,
        shift_binary_csr_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z,
        inits_and_teardowns_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z,
        unified_reduced_machine_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z,
    ]
    .iter()
    .max()
    .unwrap();

    let max_num_openings_at_z_omega = *[
        risc_v_cycles_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z_OMEGA,
        reduced_risc_v_machine_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z_OMEGA,
        reduced_risc_v_log_23_machine_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z_OMEGA,
        blake2_with_compression_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z_OMEGA,
        bigint_with_control_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z_OMEGA,
        keccak_special5_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z_OMEGA,
        add_sub_lui_auipc_mop_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z_OMEGA,
        jump_branch_slt_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z_OMEGA,
        load_store_subword_only_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z_OMEGA,
        load_store_word_only_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z_OMEGA,
        mul_div_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z_OMEGA,
        mul_div_unsigned_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z_OMEGA,
        shift_binary_csr_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z_OMEGA,
        inits_and_teardowns_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z_OMEGA,
        unified_reduced_machine_verifier::concrete::size_constants::NUM_OPENINGS_AT_Z_OMEGA,
    ]
    .iter()
    .max()
    .unwrap();

    let max_fri_folding_factors_log2 = **[
        risc_v_cycles_verifier::concrete::size_constants::FRI_FOLDING_SCHEDULE
            .iter()
            .max()
            .unwrap(),
        reduced_risc_v_machine_verifier::concrete::size_constants::FRI_FOLDING_SCHEDULE
            .iter()
            .max()
            .unwrap(),
        reduced_risc_v_log_23_machine_verifier::concrete::size_constants::FRI_FOLDING_SCHEDULE
            .iter()
            .max()
            .unwrap(),
        blake2_with_compression_verifier::concrete::size_constants::FRI_FOLDING_SCHEDULE
            .iter()
            .max()
            .unwrap(),
        bigint_with_control_verifier::concrete::size_constants::FRI_FOLDING_SCHEDULE
            .iter()
            .max()
            .unwrap(),
        keccak_special5_verifier::concrete::size_constants::FRI_FOLDING_SCHEDULE
            .iter()
            .max()
            .unwrap(),
        add_sub_lui_auipc_mop_verifier::concrete::size_constants::FRI_FOLDING_SCHEDULE
            .iter()
            .max()
            .unwrap(),
        jump_branch_slt_verifier::concrete::size_constants::FRI_FOLDING_SCHEDULE
            .iter()
            .max()
            .unwrap(),
        load_store_subword_only_verifier::concrete::size_constants::FRI_FOLDING_SCHEDULE
            .iter()
            .max()
            .unwrap(),
        load_store_word_only_verifier::concrete::size_constants::FRI_FOLDING_SCHEDULE
            .iter()
            .max()
            .unwrap(),
        mul_div_verifier::concrete::size_constants::FRI_FOLDING_SCHEDULE
            .iter()
            .max()
            .unwrap(),
        mul_div_unsigned_verifier::concrete::size_constants::FRI_FOLDING_SCHEDULE
            .iter()
            .max()
            .unwrap(),
        shift_binary_csr_verifier::concrete::size_constants::FRI_FOLDING_SCHEDULE
            .iter()
            .max()
            .unwrap(),
        inits_and_teardowns_verifier::concrete::size_constants::FRI_FOLDING_SCHEDULE
            .iter()
            .max()
            .unwrap(),
        unified_reduced_machine_verifier::concrete::size_constants::FRI_FOLDING_SCHEDULE
            .iter()
            .max()
            .unwrap(),
    ]
    .iter()
    .max()
    .unwrap();

    let [
        pow_bits_for_memory_and_delegation_for_80,
        pow_bits_for_memory_and_delegation_for_100,
    ] = [80, 100].map(|security_bits| {
        pow_bits_for_memory_and_delegation(
            security_bits,
            max_number_of_cycles,
            challenge_field_size,
        )
    });

    let [lookup_pow_bits_for_80, lookup_pow_bits_for_100] = [80, 100].map(|security_bits| {
        pow_bits_for_cq_lookup(security_bits, max_trace_len_log2, challenge_field_size)
    });

    let [
        quotient_alpha_pow_bits_for_80,
        quotient_alpha_pow_bits_for_100,
    ] = [80, 100].map(|security_bits| {
        pow_bits_for_quotient(
            security_bits,
            challenge_field_size,
            max_num_quotient_terms,
            max_fri_factor_log2,
        )
    });

    let [quotient_z_pow_bits_for_80, quotient_z_pow_bits_for_100] =
        [80, 100].map(|security_bits| {
            pow_bits_for_deep_z(
                security_bits,
                challenge_field_size,
                max_trace_len_log2 + max_fri_factor_log2,
            )
        });

    let [
        deep_poly_alpha_pow_bits_for_80,
        deep_poly_alpha_pow_bits_for_100,
    ] = [80, 100].map(|security_bits| {
        pow_bits_for_deep_poly_alpha(
            security_bits,
            challenge_field_size,
            max_trace_len_log2,
            max_num_openings_at_z + max_num_openings_at_z_omega,
        )
    });

    let [max_foldings_pow_bits_for_80, max_foldings_pow_bits_for_100] =
        [80, 100].map(|security_bits| {
            pow_bits_for_folding_round(
                security_bits,
                challenge_field_size,
                max_trace_len_log2,
                max_fri_folding_factors_log2,
            )
        });

    let num_queries_for_80 =
        num_queries_for_security_params(80, pow_bits_for_queries_for_80, max_fri_factor_log2);

    let num_queries_for_100 =
        num_queries_for_security_params(100, pow_bits_for_queries_for_100, max_fri_factor_log2);

    let result_token_stream = quote! {
        const MAX_TRACE_LEN_LOG2: usize = #max_trace_len_log2;
        const MAX_FRI_FACTOR_LOG2: usize = #max_fri_factor_log2;
        const MAX_CHALLENGE_FIELD_SIZE_LOG2: usize = #challenge_field_size;
        const MAX_NUMBER_OF_COLUMNS: usize = #max_number_of_columns;
        const MAX_NUM_QUOTIENT_TERMS: usize = #max_num_quotient_terms;
        const MAX_NUM_OPENINGS_AT_Z: usize = #max_num_openings_at_z;
        const MAX_NUM_OPENINGS_AT_Z_OMEGA: usize = #max_num_openings_at_z_omega;
        const MAX_FRI_FOLDING_FACTOR_LOG2: usize = #max_fri_folding_factors_log2;

        const POW_BITS_FOR_MEMORY_AND_DELEGATION_FOR_80_SECURITY_BITS: usize = #pow_bits_for_memory_and_delegation_for_80;
        const POW_BITS_FOR_MEMORY_AND_DELEGATION_FOR_100_SECURITY_BITS: usize = #pow_bits_for_memory_and_delegation_for_100;

        const LOOKUP_POW_BITS_FOR_80_SECURITY_BITS: usize = #lookup_pow_bits_for_80;
        const LOOKUP_POW_BITS_FOR_100_SECURITY_BITS: usize = #lookup_pow_bits_for_100;
        const QUOTIENT_ALPHA_POW_BITS_FOR_80_SECURITY_BITS: usize = #quotient_alpha_pow_bits_for_80;
        const QUOTIENT_ALPHA_POW_BITS_FOR_100_SECURITY_BITS: usize = #quotient_alpha_pow_bits_for_100;
        const QUOTIENT_Z_POW_BITS_FOR_80_SECURITY_BITS: usize = #quotient_z_pow_bits_for_80;
        const QUOTIENT_Z_POW_BITS_FOR_100_SECURITY_BITS: usize = #quotient_z_pow_bits_for_100;
        const DEEP_POLY_ALPHA_POW_BITS_FOR_80_SECURITY_BITS: usize = #deep_poly_alpha_pow_bits_for_80;
        const DEEP_POLY_ALPHA_POW_BITS_FOR_100_SECURITY_BITS: usize = #deep_poly_alpha_pow_bits_for_100;
        const MAX_FOLDINGS_POW_BITS_FOR_80_SECURITY_BITS: usize = #max_foldings_pow_bits_for_80;
        const MAX_FOLDINGS_POW_BITS_FOR_100_SECURITY_BITS: usize = #max_foldings_pow_bits_for_100;
        const FRI_QUERIES_POW_BITS_FOR_80_SECURITY_BITS: usize = #pow_bits_for_queries_for_80;
        const FRI_QUERIES_POW_BITS_FOR_100_SECURITY_BITS: usize = #pow_bits_for_queries_for_100;
        const NUM_QUERIES_FOR_80_SECURITY_BITS: usize = #num_queries_for_80;
        const NUM_QUERIES_FOR_100_SECURITY_BITS: usize = #num_queries_for_100;

        impl<const NUM_FOLDINGS: usize> SizedProofSecurityConfig<NUM_FOLDINGS> {
            pub const fn worst_case_config() -> Self {
                if cfg!(feature = "security_80") {
                    SizedProofSecurityConfig {
                        lookup_pow_bits: LOOKUP_POW_BITS_FOR_80_SECURITY_BITS as u32,
                        quotient_alpha_pow_bits: QUOTIENT_ALPHA_POW_BITS_FOR_80_SECURITY_BITS as u32,
                        quotient_z_pow_bits: QUOTIENT_Z_POW_BITS_FOR_80_SECURITY_BITS as u32,
                        deep_poly_alpha_pow_bits: DEEP_POLY_ALPHA_POW_BITS_FOR_80_SECURITY_BITS as u32,
                        foldings_pow_bits: [MAX_FOLDINGS_POW_BITS_FOR_80_SECURITY_BITS as u32;
                            NUM_FOLDINGS],
                        fri_queries_pow_bits: FRI_QUERIES_POW_BITS_FOR_80_SECURITY_BITS as u32,
                        num_queries: NUM_QUERIES_FOR_80_SECURITY_BITS,
                    }
                } else if cfg!(feature = "security_100") {
                    SizedProofSecurityConfig {
                        lookup_pow_bits: LOOKUP_POW_BITS_FOR_100_SECURITY_BITS as u32,
                        quotient_alpha_pow_bits: QUOTIENT_ALPHA_POW_BITS_FOR_100_SECURITY_BITS as u32,
                        quotient_z_pow_bits: QUOTIENT_Z_POW_BITS_FOR_100_SECURITY_BITS as u32,
                        deep_poly_alpha_pow_bits: DEEP_POLY_ALPHA_POW_BITS_FOR_100_SECURITY_BITS as u32,
                        foldings_pow_bits: [MAX_FOLDINGS_POW_BITS_FOR_100_SECURITY_BITS as u32;
                            NUM_FOLDINGS],
                        fri_queries_pow_bits: FRI_QUERIES_POW_BITS_FOR_100_SECURITY_BITS as u32,
                        num_queries: NUM_QUERIES_FOR_100_SECURITY_BITS,
                    }
                } else {
                    panic!("No security level selected");
                }
            }
        }
    };

    let result_string = format_rust_code(&result_token_stream.to_string())
        .expect("Failed to format generated Rust code");

    let prover_path = "../../prover/src/prover_stages";
    let verifier_common_path = "../../verifier_common/src";

    std::fs::write(
        Path::new(&prover_path).join("pow_config_worst_constants.rs"),
        result_string.clone(),
    )
    .expect(&format!("Failed to write to {}", prover_path));
    std::fs::write(
        Path::new(&verifier_common_path).join("pow_config_worst_constants.rs"),
        result_string,
    )
    .expect(&format!("Failed to write to {}", verifier_common_path));
}

/// PoW before getting challenges for
/// - memory (linearization + gamma)
/// - delegation (linearization + gamma)
/// - state_permutation (linearization + gamma)
fn pow_bits_for_memory_and_delegation(
    security_bits: usize,
    // These challenges are shared between all circuits in one layer, so we need to use the max number of cycles
    max_cycles_log2: usize,
    field_size_log2: usize,
) -> usize {
    let lookup_pow = pow_bits_for_cq_lookup(security_bits, max_cycles_log2, field_size_log2);
    let memory_pow = pow_bits_for_memory_argument(security_bits, max_cycles_log2, field_size_log2);

    if lookup_pow > memory_pow {
        lookup_pow
    } else {
        memory_pow
    }
}

/// PoW before getting challenges for
/// - FRI queries
fn num_queries_for_security_params(
    security_bits: usize,
    pow_bits: usize,
    lde_factor_log2: usize,
) -> usize {
    let bits = security_bits - pow_bits;
    let init_res = bits.div_ceil(lde_factor_log2);

    // We should add extra 20% of queries
    init_res + init_res.div_ceil(5)
}

fn pow_bits_for_cq_lookup(
    security_bits: usize,
    domain_size_log2: usize,
    field_size_log2: usize,
) -> usize {
    let no_pow_security_bits = field_size_log2 - domain_size_log2 - 5;
    if security_bits > no_pow_security_bits {
        security_bits - no_pow_security_bits
    } else {
        0
    }
}

fn pow_bits_for_memory_argument(
    security_bits: usize,
    domain_size_log2: usize,
    field_size_log2: usize,
) -> usize {
    let no_pow_security_bits = field_size_log2 - domain_size_log2 - 2;
    if security_bits > no_pow_security_bits {
        security_bits - no_pow_security_bits
    } else {
        0
    }
}

// https://eprint.iacr.org/2022/1216.pdf
// We can bound L^+ as 4
fn pow_bits_for_quotient(
    security_bits: usize,
    challenge_field_size_log2: usize,
    powers_of_alpha: usize,
    lde_factor_log2: usize,
) -> usize {
    let powers_of_alpha_log2 = powers_of_alpha.next_power_of_two().trailing_zeros() as usize;
    let no_pow_security_bits =
        challenge_field_size_log2 - powers_of_alpha_log2 - 4 - lde_factor_log2.div_ceil(2);
    if security_bits > no_pow_security_bits {
        security_bits - no_pow_security_bits
    } else {
        0
    }
}

// https://eprint.iacr.org/2022/1216.pdf
// We can bound L^+ as 4
fn pow_bits_for_deep_z(
    security_bits: usize,
    challenge_field_size_log2: usize,
    lde_domain_size_log2: usize,
) -> usize {
    let no_pow_security_bits = challenge_field_size_log2 - lde_domain_size_log2 - 5;
    if security_bits > no_pow_security_bits {
        security_bits - no_pow_security_bits
    } else {
        0
    }
}

// https://hackmd.io/@pgaf/HkKs_1ytT
fn pow_bits_for_deep_poly_alpha(
    security_bits: usize,
    challenge_field_size_log2: usize,
    domain_size_log2: usize,
    powers_of_alpha: usize,
) -> usize {
    let powers_of_alpha_log2 = powers_of_alpha.next_power_of_two().trailing_zeros() as usize;
    let no_pow_security_bits = challenge_field_size_log2 - powers_of_alpha_log2 - domain_size_log2;
    if security_bits > no_pow_security_bits {
        security_bits - no_pow_security_bits
    } else {
        0
    }
}

// https://hackmd.io/@pgaf/HkKs_1ytT
fn pow_bits_for_folding_round(
    security_bits: usize,
    challenge_field_size_log2: usize,
    domain_size_log2: usize,
    folding_factor_log2: usize,
) -> usize {
    let no_pow_security_bits = challenge_field_size_log2 - folding_factor_log2 - domain_size_log2;
    if security_bits > no_pow_security_bits {
        security_bits - no_pow_security_bits
    } else {
        0
    }
}

fn pow_bits_for_queries(security_bits: usize, num_queries: usize, lde_factor_log2: usize) -> usize {
    // We should add extra 20% of queries
    let queries_contribution = 5 * num_queries / 6;
    let no_pow_security_bits = queries_contribution * lde_factor_log2;
    if security_bits > no_pow_security_bits {
        security_bits - no_pow_security_bits
    } else {
        0
    }
}

/// Runs rustfmt to format the code.
fn format_rust_code(code: &str) -> Result<String, String> {
    // Spawn the `rustfmt` process
    let mut rustfmt = Command::new("rustfmt")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|e| format!("Failed to spawn rustfmt: {}", e))?;

    // Write the Rust code to `rustfmt`'s stdin
    if let Some(mut stdin) = rustfmt.stdin.take() {
        stdin
            .write_all(code.as_bytes())
            .map_err(|e| format!("Failed to write to rustfmt stdin: {}", e))?;
    }

    // Wait for `rustfmt` to complete and collect the formatted code
    let output = rustfmt
        .wait_with_output()
        .map_err(|e| format!("Failed to read rustfmt output: {}", e))?;

    if !output.status.success() {
        return Err(format!(
            "rustfmt failed with status {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        ));
    }

    // Convert the output to a String
    String::from_utf8(output.stdout).map_err(|e| format!("Invalid UTF-8 in rustfmt output: {}", e))
}
