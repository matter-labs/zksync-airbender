#include "ff_config.cuh"

namespace airbender::primitives::field {

// definition of the header's `extern __device__ __constant__` declaration;
// (modulus * inv_proth120) % 2^32 == -1 % 2^32, and modulus ≡ 1 (mod 2^32)
__device__ __constant__ uint32_t inv_proth120 = 0xffffffff;

} // namespace airbender::primitives::field
