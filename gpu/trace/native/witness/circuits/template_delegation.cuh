#pragma once
#include "../fused_trace_accessor.cuh"
#include "../lookup_mapping.cuh"
#include "../memory_delegation.cuh"
#include "../trace_delegation.cuh"
#include "../witness_generation.cuh"

using namespace ::airbender::trace::witness::generation;
using namespace ::airbender::trace::witness::memory::delegation;
using namespace ::airbender::trace::witness::multiplicities;
using namespace ::airbender::trace::witness::trace::delegation;

namespace airbender::trace::witness::circuits::NAME {

#include CIRCUIT_INCLUDE(NAME)

KERNEL(NAME, ORACLE)

#include "../fused_delegation.cuh"

} // namespace airbender::trace::witness::circuits::NAME
