#pragma once
#include "../trace_unrolled.cuh"
#include "../witness_generation.cuh"

using namespace ::airbender::trace::witness::generation;
using namespace ::airbender::trace::witness::trace::unrolled;

namespace airbender::trace::witness::circuits::NAME {

#include UNROLLED_CIRCUIT_INCLUDE(NAME)

KERNEL(NAME, ORACLE)

} // namespace airbender::trace::witness::circuits::NAME
