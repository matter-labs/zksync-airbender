#pragma once

#include "common.cuh"

using namespace ::airbender::witness;

namespace airbender::witness::option {

enum OptionTag : u32 {
  None,
  Some,
};

template <typename T> struct Option {
  OptionTag tag;
  T value;
};

} // namespace airbender::witness::option