#pragma once

#include "common.cuh"

using namespace ::airbender::witness;

namespace airbender::witness::option {

namespace OptionU8 {

enum OptionTag : u8 {
  None = 0,
  Some = 1,
};

template <typename T> struct Option {
  OptionTag tag;
  T value;
};

} // namespace OptionU8

namespace OptionU32 {

enum OptionTag : u32 {
  None = 0,
  Some = 1,
};

template <typename T> struct Option {
  OptionTag tag;
  T value;
};

} // namespace OptionU32

} // namespace airbender::witness::option