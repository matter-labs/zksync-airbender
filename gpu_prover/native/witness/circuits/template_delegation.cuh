#pragma once
#include "../trace_delegation.cuh"
#include "../witness_generation.cuh"

using namespace ::airbender::witness::generation;
using namespace ::airbender::witness::trace::delegation;

namespace airbender::witness::circuits::NAME {

#include CIRCUIT_INCLUDE(NAME)

KERNEL(NAME, DelegationTrace)

} // namespace airbender::witness::circuits::NAME