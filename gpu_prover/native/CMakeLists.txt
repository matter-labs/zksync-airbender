cmake_minimum_required(VERSION 3.30)
# Cmake must be at least 3.30 - the earlier one didn't pass cuda_standard properly.
project(gpu_prover_native)
enable_language(CUDA)
if ((NOT DEFINED CMAKE_CUDA_ARCHITECTURES) OR (CMAKE_CUDA_ARCHITECTURES STREQUAL ""))
    set(CMAKE_CUDA_ARCHITECTURES native)
endif ()
add_library(gpu_prover_native STATIC
        arg_utils.cuh
        barycentric.cu
        blake2s.cu
        context.cu
        context.cuh
        common.cuh
        field.cuh
        field_bench.cu
        memory.cuh
        ntt/bitrev_Z_to_natural_evals.cu
        ntt/natural_evals_to_bitrev_Z.cu
        ntt/ntt.cuh
        ops_complex.cu
        ops_complex.cuh
        ops_cub/common.cuh
        ops_cub/device_radix_sort.cu
        ops_cub/device_reduce.cu
        ops_cub/device_run_length_encode.cu
        ops_cub/device_scan/common.cuh
        ops_cub/device_scan/e_add_bf.cu
        ops_cub/device_scan/e_add_e4.cu
        ops_cub/device_scan/e_add_u32.cu
        ops_cub/device_scan/e_mul_bf.cu
        ops_cub/device_scan/e_mul_e4.cu
        ops_cub/device_scan/i_add_bf.cu
        ops_cub/device_scan/i_add_e4.cu
        ops_cub/device_scan/i_add_u32.cu
        ops_cub/device_scan/i_mul_bf.cu
        ops_cub/device_scan/i_mul_e4.cu
        ops_simple.cu
        stage2.cu
        stage3.cu
        stage4.cu
        vectorized.cuh
        witness/circuits/bigint_with_control.cu
        witness/circuits/blake2_with_compression.cu
        witness/circuits/final_reduced_risc_v_machine.cu
        witness/circuits/machine_without_signed_mul_div.cu
        witness/circuits/reduced_risc_v_machine.cu
        witness/circuits/risc_v_cycles.cu
        witness/circuits/template_delegation.cuh
        witness/circuits/template_main.cuh
        witness/column.cuh
        witness/layout.cuh
        witness/memory.cuh
        witness/memory_delegation.cu
        witness/memory_main.cu
        witness/option.cuh
        witness/placeholder.cuh
        witness/ram_access.cuh
        witness/tables.cuh
        witness/trace.cuh
        witness/trace_delegation.cuh
        witness/trace_main.cuh
        witness/witness_generation.cuh
        witness/common.cuh
        witness/multiplicities.cu
)
set_target_properties(gpu_prover_native PROPERTIES CUDA_STANDARD 20)
set_target_properties(gpu_prover_native PROPERTIES CUDA_SEPARABLE_COMPILATION ON)
set_target_properties(gpu_prover_native PROPERTIES CUDA_RESOLVE_DEVICE_SYMBOLS ON)
target_compile_options(gpu_prover_native PRIVATE --expt-relaxed-constexpr)
target_compile_options(gpu_prover_native PRIVATE --ptxas-options=-v)
#target_compile_options(gpu_prover_native PRIVATE -lineinfo)
target_compile_options(gpu_prover_native PRIVATE --keep)
install(TARGETS gpu_prover_native DESTINATION .)
