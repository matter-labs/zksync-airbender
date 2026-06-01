target_sources(circuit_prover_native PRIVATE
        bigint_with_control.cu
        blake2_g_function.cu
        blake2_with_compression.cu
        add_sub_lui_auipc_mop.cu
        keccak_special5.cu
        jump_branch_slt.cu
        load_store_subword_only.cu
        load_store_word_only.cu
        mul_div_unsigned.cu
        shift_binary_csr.cu
        template_delegation.cuh
        template_unrolled.cuh
)
