pub mod add_sub_lui_auipc_mop_sec_100;
pub mod bigint_with_extended_control_sec_100;
pub mod blake2_g_function_sec_100;
pub mod blake2_with_extended_control_sec_100;
pub mod inits_and_teardowns_sec_100;
pub mod jump_branch_slt_sec_100;
pub mod keccak_chi5_sec_100;
pub mod keccak_column_parity_sec_100;
pub mod keccak_special5_sec_100;
pub mod keccak_theta_rho_sec_100;
pub mod mem_subword_only_sec_100;
pub mod mem_word_only_sec_100;
pub mod shift_binop_sec_100;
pub mod unified_reduced_machine_sec_100;
pub mod unified_reduced_machine_sec_100_l1_feeder;
pub mod unsigned_mul_div_sec_100;

pub type UnrolledCircuitOutput = add_sub_lui_auipc_mop_sec_100::ConcreteVerifierOutput;
pub type InitsAndTeardownsCircuitOutput = inits_and_teardowns_sec_100::ConcreteVerifierOutput;
pub type DelegationCircuitOutput = blake2_with_extended_control_sec_100::ConcreteVerifierOutput;
pub type UnifiedCircuitOutput = unified_reduced_machine_sec_100::ConcreteVerifierOutput;
/// The unified verifier output at setup cap `CAP`: the standard verifier's
/// shape (`UnifiedCircuitOutput` at [`prover::definitions::DEFAULT_CAP_SIZE`])
/// and the L1 feeder verifier's at its generated `CAP_SIZE`.
pub type UnifiedCircuitOutputWithCap<const CAP: usize> = verifier_common::VerifierOutput<
    verifier_common::field::baby_bear::ext4::BabyBearExt4,
    { unified_reduced_machine_sec_100::INIT_AND_TEARDOWN_SETS },
    CAP,
    { unified_reduced_machine_sec_100::NUM_MEMORY_COMMITS },
    { unified_reduced_machine_sec_100::NUM_SETUP_COMMITS },
>;
const _: () = assert!(
    unified_reduced_machine_sec_100_l1_feeder::INIT_AND_TEARDOWN_SETS
        == unified_reduced_machine_sec_100::INIT_AND_TEARDOWN_SETS
);
const _: () = assert!(
    unified_reduced_machine_sec_100_l1_feeder::NUM_MEMORY_COMMITS
        == unified_reduced_machine_sec_100::NUM_MEMORY_COMMITS
);
const _: () = assert!(
    unified_reduced_machine_sec_100_l1_feeder::NUM_SETUP_COMMITS
        == unified_reduced_machine_sec_100::NUM_SETUP_COMMITS
);
