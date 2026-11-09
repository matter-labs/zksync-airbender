#pragma once

#include "field.cuh"

#include "memory.cuh"

#include "../memory_unrolled.cuh"

#include "../fused_trace_accessor.cuh"
#include "../trace_unrolled.cuh"
#include "relations.cuh"
#include "witness_generation.cuh"

using namespace ::airbender::trace::witness::proth120::generation;
using namespace ::airbender::trace::witness::memory::unrolled;
using namespace ::airbender::trace::witness::trace::unrolled;

namespace airbender::trace::witness::proth120::circuits::NAME {

#include UNROLLED_CIRCUIT_INCLUDE(CIRCUIT_DIR)

KERNEL(NAME, ORACLE)

#include "fused_unrolled.cuh"

} // namespace airbender::trace::witness::proth120::circuits::NAME
