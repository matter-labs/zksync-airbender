#include "field.cuh"

#include "memory.cuh"

#include "../inits_and_teardowns.cuh"

using namespace ::airbender::trace::witness::memory::unrolled;

namespace airbender::trace::witness::proth120::memory::unrolled {

EXTERN __global__ void ab_pr_generate_inits_and_teardowns_kernel(const __grid_constant__ InitsAndTeardownsLayouts init_and_teardown_layouts,
                                                                 const __grid_constant__ InitsAndTeardownsTraceRaw trace,
                                                                 matrix_setter<pr, st_modifier::cg> memory, const u32 page_size_log2,
                                                                 const u32 pages_per_set_log2) {
  const unsigned global_word = blockIdx.x * blockDim.x + threadIdx.x;
  process_inits_and_teardowns_pages(init_and_teardown_layouts, trace, memory, page_size_log2, pages_per_set_log2, global_word);
}

} // namespace airbender::trace::witness::proth120::memory::unrolled
