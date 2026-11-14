#include "inits_and_teardowns.cuh"

namespace airbender::trace::witness::memory::unrolled {

EXTERN __global__ void ab_generate_memory_values_unrolled_memory_kernel(const __grid_constant__ UnrolledMemoryLayout layout,
                                                                        const __grid_constant__ UnrolledMemoryOracle oracle,
                                                                        matrix_setter<bf, st_modifier::cg> memory, const unsigned count) {
  const unsigned index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= count)
    return;
  memory.add_row(index);
  NoopUnrolledCapture capture;
  process_machine_state_assuming_preprocessed_decoder<false>(layout, oracle, memory, memory, nullptr, capture, index);
  process_shuffle_ram_access_sets<false>(layout, {}, oracle, memory, memory, capture, index);
}

EXTERN __global__ void ab_generate_memory_values_unrolled_non_memory_kernel(const __grid_constant__ UnrolledMemoryLayout layout,
                                                                            const __grid_constant__ UnrolledNonMemoryOracle oracle,
                                                                            matrix_setter<bf, st_modifier::cg> memory, const unsigned count) {
  const unsigned index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= count)
    return;
  memory.add_row(index);
  NoopUnrolledCapture capture;
  process_machine_state_assuming_preprocessed_decoder<false>(layout, oracle, memory, memory, nullptr, capture, index);
  process_shuffle_ram_access_sets<false>(layout, {}, oracle, memory, memory, capture, index);
}

EXTERN __global__ void ab_generate_memory_values_unrolled_unified_kernel(const __grid_constant__ UnrolledMemoryLayout layout,
                                                                         const __grid_constant__ UnrolledUnifiedOracle oracle,
                                                                         matrix_setter<bf, st_modifier::cg> memory, const unsigned count) {
  const unsigned index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= count)
    return;
  memory.add_row(index);
  NoopUnrolledCapture capture;
  process_machine_state_assuming_preprocessed_decoder<false>(layout, oracle, memory, memory, nullptr, capture, index);
  process_shuffle_ram_access_sets<false>(layout, {}, oracle, memory, memory, capture, index);
}

EXTERN __global__ void ab_generate_memory_and_witness_values_unrolled_memory_kernel(const __grid_constant__ UnrolledMemoryLayout layout,
                                                                                    const __grid_constant__ AuxLayoutData aux_layout_data,
                                                                                    const __grid_constant__ UnrolledMemoryOracle oracle,
                                                                                    matrix_setter<bf, st_modifier::cg> memory,
                                                                                    matrix_setter<bf, st_modifier::cg> witness,
                                                                                    u32 *const __restrict__ decoder_lookup_mapping, const unsigned count) {
  const unsigned index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= count)
    return;
  memory.add_row(index);
  witness.add_row(index);
  NoopUnrolledCapture capture;
  process_machine_state_assuming_preprocessed_decoder<true>(layout, oracle, memory, witness, decoder_lookup_mapping, capture, index);
  process_shuffle_ram_access_sets<true>(layout, aux_layout_data, oracle, memory, witness, capture, index);
}

EXTERN __global__ void ab_generate_memory_and_witness_values_unrolled_non_memory_kernel(const __grid_constant__ UnrolledMemoryLayout layout,
                                                                                        const __grid_constant__ AuxLayoutData aux_layout_data,
                                                                                        const __grid_constant__ UnrolledNonMemoryOracle oracle,
                                                                                        matrix_setter<bf, st_modifier::cg> memory,
                                                                                        matrix_setter<bf, st_modifier::cg> witness,
                                                                                        u32 *const __restrict__ decoder_lookup_mapping, const unsigned count) {
  const unsigned index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= count)
    return;
  memory.add_row(index);
  witness.add_row(index);
  NoopUnrolledCapture capture;
  process_machine_state_assuming_preprocessed_decoder<true>(layout, oracle, memory, witness, decoder_lookup_mapping, capture, index);
  process_shuffle_ram_access_sets<true>(layout, aux_layout_data, oracle, memory, witness, capture, index);
}

EXTERN __global__ void ab_generate_memory_and_witness_values_unrolled_inits_and_teardowns_kernel(
    const __grid_constant__ InitsAndTeardownsLayouts init_and_teardown_layouts, const __grid_constant__ InitsAndTeardownsTraceRaw trace,
    matrix_setter<bf, st_modifier::cg> memory, const u32 page_size_log2, const u32 pages_per_set_log2) {
  const unsigned global_word = blockIdx.x * blockDim.x + threadIdx.x;
  process_inits_and_teardowns_pages(init_and_teardown_layouts, trace, memory, page_size_log2, pages_per_set_log2, global_word);
}

EXTERN __global__ void ab_generate_memory_and_witness_values_unrolled_unified_kernel(const __grid_constant__ UnrolledMemoryLayout layout,
                                                                                     const __grid_constant__ AuxLayoutData aux_layout_data,
                                                                                     const __grid_constant__ UnrolledUnifiedOracle oracle,
                                                                                     matrix_setter<bf, st_modifier::cg> memory,
                                                                                     matrix_setter<bf, st_modifier::cg> witness,
                                                                                     u32 *const __restrict__ decoder_lookup_mapping, const unsigned count) {
  const unsigned index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= count)
    return;
  memory.add_row(index);
  witness.add_row(index);
  NoopUnrolledCapture capture;
  process_machine_state_assuming_preprocessed_decoder<true>(layout, oracle, memory, witness, decoder_lookup_mapping, capture, index);
  process_shuffle_ram_access_sets<true>(layout, aux_layout_data, oracle, memory, witness, capture, index);
}

} // namespace airbender::trace::witness::memory::unrolled
