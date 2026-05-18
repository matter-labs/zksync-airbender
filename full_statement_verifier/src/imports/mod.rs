pub mod add_sub_lui_auipc_mop_sec_80;
pub mod bigint_with_extended_control_sec_80;
pub mod blake2_g_function_sec_80;
pub mod blake2_with_extended_control_sec_80;
pub mod inits_and_teardowns_sec_80;
pub mod jump_branch_slt_sec_80;
pub mod keccak_special5_sec_80;
pub mod mem_subword_only_sec_80;
pub mod mem_word_only_sec_80;
pub mod shift_binop_sec_80;
pub mod unified_reduced_machine_sec_80;

pub type UnrolledCircuitOutput = add_sub_lui_auipc_mop_sec_80::ConcreteVerifierOutput;
pub type InitsAndTeardownsCircuitOutput = inits_and_teardowns_sec_80::ConcreteVerifierOutput;
pub type DelegationCircuitOutput = blake2_with_extended_control_sec_80::ConcreteVerifierOutput;
pub type UnifiedCircuitOutput = unified_reduced_machine_sec_80::ConcreteVerifierOutput;
