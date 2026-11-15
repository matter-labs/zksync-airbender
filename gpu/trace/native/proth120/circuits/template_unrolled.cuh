#pragma once

#include "proth120/field.cuh"

#include "witness/memory.cuh"

#include "witness/memory_unrolled.cuh"

#include "proth120/relations.cuh"
#include "proth120/witness_generation.cuh"
#include "witness/fused_trace_accessor.cuh"
#include "witness/trace_unrolled.cuh"

using namespace ::airbender::trace::witness::proth120::generation;
using namespace ::airbender::trace::witness::multiplicities;
using namespace ::airbender::trace::witness::memory::unrolled;
using namespace ::airbender::trace::witness::trace::unrolled;

namespace airbender::trace::witness::proth120::circuits::NAME {

#include UNROLLED_CIRCUIT_INCLUDE(CIRCUIT_DIR)

#include "proth120/fused_unrolled.cuh"

} // namespace airbender::trace::witness::proth120::circuits::NAME
