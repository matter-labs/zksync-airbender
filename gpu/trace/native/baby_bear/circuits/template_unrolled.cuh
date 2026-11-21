#pragma once
#include "baby_bear/field.cuh"
#include "baby_bear/witness_generation.cuh"
#include "witness/fused_trace_accessor.cuh"
#include "witness/lookup_mapping.cuh"
#include "witness/memory_unrolled.cuh"
#include "witness/trace_unrolled.cuh"

using namespace ::airbender::trace::witness::generation;
using namespace ::airbender::trace::witness::memory::unrolled;
using namespace ::airbender::trace::witness::multiplicities;
using namespace ::airbender::trace::witness::trace::unrolled;

namespace airbender::trace::witness::circuits::NAME {

#include UNROLLED_CIRCUIT_INCLUDE(NAME)

KERNEL(NAME, ORACLE)

#include "baby_bear/fused_unrolled.cuh"

} // namespace airbender::trace::witness::circuits::NAME
