#pragma once

#include "common.cuh"

#define REGISTER_SIZE 2
#define NUM_TIMESTAMP_COLUMNS_FOR_RAM 2

template <u32 WIDTH> struct ColumnSet {
  u32 offset;
  u32 num_elements;
};

enum ColumnAddressTag : u32 {
  WitnessSubtree,
  MemorySubtree,
  SetupSubtree,
  OptimizedOut,
};

struct ColumnAddress {
  ColumnAddressTag tag;
  u32 offset;
};
