#include "common.cuh"

namespace airbender::gkr::ops {

// ---------------------------------------------------------------------------
// Assemble query indexes from a stream of random u32 words (device-side).
//
// Mirrors the host `BitSource` + `assemble_query_index(log_domain_size, ...)`
// chain used in WHIR PoW query derivation. The bit stream is LE-packed across
// u32 words; the first 32 bits are skipped (they were consumed as the PoW
// header in `draw_query_bits_after_verified_pow`). Each query reads
// `log_domain_size` contiguous bits.
//
// Buffer contracts:
// - `raw_bits`: padded u32 buffer (matches the squeeze output size, at least
//   `ceil((32 + num_queries * log_domain_size) / 32)` words).
// - `indexes_out`: `num_queries` u32 indexes, one per thread.
// ---------------------------------------------------------------------------
EXTERN __global__ void ab_assemble_query_indexes_kernel(const u32 *raw_bits, u32 *indexes_out, const unsigned num_queries, const unsigned log_domain_size) {
  const unsigned idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (idx >= num_queries)
    return;
  // Skip the first 32 bits (PoW header word); each subsequent query consumes
  // log_domain_size bits.
  const unsigned start_bit = 32u + idx * log_domain_size;
  u32 result = 0;
  for (unsigned i = 0; i < log_domain_size; i++) {
    const unsigned bit_pos = start_bit + i;
    const unsigned word_idx = bit_pos >> 5;
    const unsigned bit_idx = bit_pos & 31u;
    const u32 bit = (raw_bits[word_idx] >> bit_idx) & 1u;
    result |= bit << i;
  }
  indexes_out[idx] = result;
}

} // namespace airbender::gkr::ops
