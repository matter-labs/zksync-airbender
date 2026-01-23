#pragma once
#include "../trace_unrolled.cuh"
#include "../witness_generation.cuh"

using namespace ::airbender::witness::generation;
using namespace ::airbender::witness::trace::unrolled;

namespace airbender::witness::circuits::NAME {

#include UNROLLED_CIRCUIT_INCLUDE(NAME)

KERNEL(NAME, UnrolledMemoryTrace)

} // namespace airbender::witness::circuits::NAME