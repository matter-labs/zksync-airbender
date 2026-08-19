#include "memory_unrolled.cuh"

namespace airbender::trace::witness::memory::unrolled {

struct InitsAndTeardownsTraceRaw {
  const u32 num_pages;
  const u32 *const __restrict__ page_indices;
  const u32 *const __restrict__ values_packed;
  const TimestampScalar *const __restrict__ timestamps_packed;
};

#define MAX_INITS_AND_TEARDOWNS_SETS_COUNT 16

struct InitsAndTeardownsLayout {
  const u32 teardown_timestamps_columns[NUM_TIMESTAMP_COLUMNS_FOR_RAM];
  const u32 teardown_values_columns[2];
};

struct InitsAndTeardownsLayouts {
  const u32 count;
  const InitsAndTeardownsLayout layouts[MAX_INITS_AND_TEARDOWNS_SETS_COUNT];
};

DEVICE_FORCEINLINE void process_inits_and_teardowns_pages(const InitsAndTeardownsLayouts &init_and_teardown_layouts, const InitsAndTeardownsTraceRaw &trace,
                                                          const matrix_setter<bf, st_modifier::cg> memory, const u32 page_size_log2,
                                                          const u32 pages_per_set_log2, const unsigned global_word) {
  if (global_word >= trace.num_pages << page_size_log2)
    return;
  const u32 page_size_mask = (1u << page_size_log2) - 1u;
  const u32 pages_per_set_mask = (1u << pages_per_set_log2) - 1u;
  const unsigned page_slot = global_word >> page_size_log2;
  const unsigned word_in_page = global_word & page_size_mask;
  const u32 page_idx = trace.page_indices[page_slot];
  const u32 set_idx = page_idx >> pages_per_set_log2;
  const unsigned row_idx = ((page_idx & pages_per_set_mask) << page_size_log2) | word_in_page;
  const u32 val = trace.values_packed[global_word];
  const TimestampScalar ts_scalar = trace.timestamps_packed[global_word];
  const auto layout = init_and_teardown_layouts.layouts[set_idx];
  const auto row_memory = memory.copy().add_row(row_idx);
  write_timestamp_value(layout.teardown_timestamps_columns, TimestampData::from_scalar(ts_scalar), row_memory);
  write_u32_value(layout.teardown_values_columns, val, row_memory);
}

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
