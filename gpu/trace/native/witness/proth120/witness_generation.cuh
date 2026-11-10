#pragma once
#include "field.cuh"
#define WITNESS_GENERATION_NAMESPACE proth120::generation
#define WITNESS_VALUE pr
#include "../witness_generation.cuh"
#define CONSTANT_PR(N, A, B, C, D) [[maybe_unused]] constexpr wrapped_f VAR(N) = wrapped_f::new_const_limbs(A, B, C, D);
