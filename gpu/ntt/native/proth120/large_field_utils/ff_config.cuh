#pragma once
#include <common.cuh>

namespace airbender::primitives::field {

// 32-bit Montgomery helper such that (modulus * inv_proth120) % 2^32 = -1 % 2^32.
// Can't make this a member of proth120. nvcc does not allow __constant__ on members.
extern __device__ __constant__ u32 inv_proth120;

} // namespace airbender::primitives::field
