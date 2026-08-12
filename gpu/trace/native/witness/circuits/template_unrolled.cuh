#pragma once
#include "../fused_trace_accessor.cuh"
#include "../lookup_mapping.cuh"
#include "../memory_unrolled.cuh"
#include "../trace_unrolled.cuh"
#include "../witness_generation.cuh"

using namespace ::airbender::trace::witness::generation;
using namespace ::airbender::trace::witness::memory::unrolled;
using namespace ::airbender::trace::witness::multiplicities;
using namespace ::airbender::trace::witness::trace::unrolled;

namespace airbender::trace::witness::circuits::NAME {

#include UNROLLED_CIRCUIT_INCLUDE(NAME)

KERNEL(NAME, ORACLE)

#include "../fused_unrolled.cuh"

} // namespace airbender::trace::witness::circuits::NAME
