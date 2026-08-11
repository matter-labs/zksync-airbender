#include "memory_delegation.cuh"

namespace airbender::trace::witness::memory::delegation {

template <bool COMPUTE_WITNESS, typename DESCRIPTION>
DEVICE_FORCEINLINE void generate(const DelegationMemoryLayout &layout, const DelegationAuxLayoutData &aux_layout_data,
                                 const DelegationTrace<DESCRIPTION> &oracle, matrix_setter<bf, st_modifier::cg> memory,
                                 matrix_setter<bf, st_modifier::cg> witness, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  memory.add_row(gid);
  witness.add_row(gid);
  process_delegation_row<COMPUTE_WITNESS>(layout, aux_layout_data, oracle, memory, witness, gid);
}

EXTERN __global__ void ab_generate_memory_values_bigint_with_control_kernel(const __grid_constant__ DelegationMemoryLayout layout,
                                                                            const __grid_constant__ BigintWithControlOracle oracle,
                                                                            const matrix_setter<bf, st_modifier::cg> memory, const unsigned count) {
  generate<false>(layout, {}, oracle, memory, memory, count);
}

EXTERN __global__ void ab_generate_memory_and_witness_values_bigint_with_control_kernel(const __grid_constant__ DelegationMemoryLayout layout,
                                                                                        const __grid_constant__ DelegationAuxLayoutData aux_layout_data,
                                                                                        const __grid_constant__ BigintWithControlOracle oracle,
                                                                                        const matrix_setter<bf, st_modifier::cg> memory,
                                                                                        const matrix_setter<bf, st_modifier::cg> witness,
                                                                                        const unsigned count) {
  generate<true>(layout, aux_layout_data, oracle, memory, witness, count);
}

EXTERN __global__ void ab_generate_memory_values_blake2_with_compression_kernel(const __grid_constant__ DelegationMemoryLayout layout,
                                                                                const __grid_constant__ Blake2WithCompressionOracle oracle,
                                                                                const matrix_setter<bf, st_modifier::cg> memory, const unsigned count) {
  generate<false>(layout, {}, oracle, memory, memory, count);
}

EXTERN __global__ void ab_generate_memory_and_witness_values_blake2_with_compression_kernel(const __grid_constant__ DelegationMemoryLayout layout,
                                                                                            const __grid_constant__ DelegationAuxLayoutData aux_layout_data,
                                                                                            const __grid_constant__ Blake2WithCompressionOracle oracle,
                                                                                            const matrix_setter<bf, st_modifier::cg> memory,
                                                                                            const matrix_setter<bf, st_modifier::cg> witness,
                                                                                            const unsigned count) {
  generate<true>(layout, aux_layout_data, oracle, memory, witness, count);
}

EXTERN __global__ void ab_generate_memory_values_keccak_special5_kernel(const __grid_constant__ DelegationMemoryLayout layout,
                                                                        const __grid_constant__ KeccakSpecial5Oracle oracle,
                                                                        const matrix_setter<bf, st_modifier::cg> memory, const unsigned count) {
  generate<false>(layout, {}, oracle, memory, memory, count);
}

EXTERN __global__ void ab_generate_memory_and_witness_values_keccak_special5_kernel(const __grid_constant__ DelegationMemoryLayout layout,
                                                                                    const __grid_constant__ DelegationAuxLayoutData aux_layout_data,
                                                                                    const __grid_constant__ KeccakSpecial5Oracle oracle,
                                                                                    const matrix_setter<bf, st_modifier::cg> memory,
                                                                                    const matrix_setter<bf, st_modifier::cg> witness, const unsigned count) {
  generate<true>(layout, aux_layout_data, oracle, memory, witness, count);
}

EXTERN __global__ void ab_generate_memory_values_blake2_g_function_kernel(const __grid_constant__ DelegationMemoryLayout layout,
                                                                          const __grid_constant__ Blake2GFunctionOracle oracle,
                                                                          const matrix_setter<bf, st_modifier::cg> memory, const unsigned count) {
  generate<false>(layout, {}, oracle, memory, memory, count);
}

EXTERN __global__ void ab_generate_memory_and_witness_values_blake2_g_function_kernel(const __grid_constant__ DelegationMemoryLayout layout,
                                                                                      const __grid_constant__ DelegationAuxLayoutData aux_layout_data,
                                                                                      const __grid_constant__ Blake2GFunctionOracle oracle,
                                                                                      const matrix_setter<bf, st_modifier::cg> memory,
                                                                                      const matrix_setter<bf, st_modifier::cg> witness, const unsigned count) {
  generate<true>(layout, aux_layout_data, oracle, memory, witness, count);
}

} // namespace airbender::trace::witness::memory::delegation
