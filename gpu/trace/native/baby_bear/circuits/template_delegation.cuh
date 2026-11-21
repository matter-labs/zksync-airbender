#pragma once
#include "baby_bear/field.cuh"
#include "baby_bear/witness_generation.cuh"
#include "witness/fused_trace_accessor.cuh"
#include "witness/lookup_mapping.cuh"
#include "witness/memory_delegation.cuh"
#include "witness/trace_delegation.cuh"

using namespace ::airbender::trace::witness::generation;
using namespace ::airbender::trace::witness::memory::delegation;
using namespace ::airbender::trace::witness::multiplicities;
using namespace ::airbender::trace::witness::trace::delegation;

namespace airbender::trace::witness::circuits::NAME {

#include CIRCUIT_INCLUDE(NAME)

KERNEL(NAME, ORACLE)

#include "baby_bear/fused_delegation.cuh"

} // namespace airbender::trace::witness::circuits::NAME
