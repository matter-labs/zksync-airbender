target_sources(gpu_trace_native PRIVATE
        add_sub_lui_auipc_mop.cu
        bigint_with_control.cu
        blake2_g_function.cu
        blake2_with_compression.cu
        jump_branch_slt.cu
        keccak_chi5.cu
        keccak_column_parity.cu
        keccak_special5.cu
        keccak_theta_rho.cu
        load_store_subword_only.cu
        load_store_word_only.cu
        mul_div_unsigned.cu
        shift_binary.cu
        unified_reduced_machine.cu
        template_delegation.cuh
        template_unrolled.cuh
)
