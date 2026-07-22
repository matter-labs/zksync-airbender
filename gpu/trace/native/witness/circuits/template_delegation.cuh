#pragma once
#include "../trace_delegation.cuh"
#include "../witness_generation.cuh"

using namespace ::airbender::trace::witness::generation;
using namespace ::airbender::trace::witness::trace::delegation;

namespace airbender::trace::witness::circuits::NAME {

#include CIRCUIT_INCLUDE(NAME)

KERNEL(NAME, ORACLE)

} // namespace airbender::trace::witness::circuits::NAME