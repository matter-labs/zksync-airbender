#pragma once
#include "../trace_main.cuh"
#include "../witness_generation.cuh"

using namespace ::airbender::witness::generation;
using namespace ::airbender::witness::trace::main;

namespace airbender::witness::circuits::NAME {

#include CIRCUIT_INCLUDE(NAME)

KERNEL(NAME, MainTrace)

} // namespace airbender::witness::circuits::NAME