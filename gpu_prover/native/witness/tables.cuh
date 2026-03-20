#pragma once

#include "common.cuh"

using namespace ::airbender::witness;

namespace airbender::witness::tables {

enum TableType : u16 {
  ZeroEntry = 0,
  RegIsZero,
  JumpCleanupOffset,
  GetSignExtensionByte,
  Xor = 4,
  U16GetSign,
  Or = 6,
  And = 7,
  TruncateShiftAmountAndRangeCheck8,
  ShiftImplementationOverBytes,
  RangeCheck8x8,
  AndNot,
  U16GetSignAndHighByte,
  MemoryOffsetGetBits,
  MemoryLoadGetSigns,
  RomAddressSpaceSeparator,
  RomRead,
  Xor3,
  Xor4,
  Xor7,
  Xor9,
  Xor12,
  RangeCheck9x9,
  RangeCheck10x10,
  RangeCheck11,
  RangeCheck12,
  RangeCheck13,
  U16SelectByteAndGetByteSign,
  ExtendLoadedValue,
  StoreByteSourceContribution,
  StoreByteExistingContribution,
  ConditionalJmpBranchSlt,
  MemoryGetOffsetAndMaskWithTrap,
  MemoryLoadHalfwordOrByte,
  AlignedRomRead,
  MemStoreClearOriginalRamValueLimb,
  MemStoreClearWrittenValueLimb,
  KeccakPermutationIndices12,
  KeccakPermutationIndices34,
  KeccakPermutationIndices56,
  XorSpecialIota,
  AndN,
  RotL,
  Decoder,
  DynamicPlaceholder,
};

template <unsigned K> DEVICE_FORCEINLINE void keys_into_binary_keys(const bf keys[K], u32 binary_keys[K]) {
#pragma unroll
  for (unsigned i = 0; i < K; i++)
    binary_keys[i] = bf::into_canonical_u32(keys[i]);
}

template <unsigned... SHIFTS> DEVICE_FORCEINLINE u32 index_for_binary_keys(const u32 keys[sizeof...(SHIFTS)]) {
  constexpr u32 shifts[sizeof...(SHIFTS)] = {SHIFTS...};
  u32 result = shifts[0] ? keys[0] << shifts[0] : keys[0];
#pragma unroll
  for (unsigned i = 1; i < sizeof...(SHIFTS); i++)
    result |= shifts[i] ? keys[i] << shifts[i] : keys[i];
  return result;
}

template <> DEVICE_FORCEINLINE u32 index_for_binary_keys<0>(const u32 keys[1]) { return keys[0]; }

template <unsigned... SHIFTS> DEVICE_FORCEINLINE u32 index_for_keys(const bf keys[sizeof...(SHIFTS)]) {
  u32 binary_keys[sizeof...(SHIFTS)];
  keys_into_binary_keys<sizeof...(SHIFTS)>(keys, binary_keys);
  return index_for_binary_keys<SHIFTS...>(binary_keys);
}

template <> DEVICE_FORCEINLINE u32 index_for_keys<0>(const bf keys[1]) { return bf::into_canonical_u32(keys[0]); }

template <unsigned K, unsigned V> struct TableDriver {
  const bf *tables;
  const unsigned stride;
  const u32 *offsets;

  DEVICE_FORCEINLINE u32 get_absolute_index(const TableType table_type, const u32 index) const { return offsets[table_type] + index; }

  DEVICE_FORCEINLINE void set_values_from_tables(const u32 absolute_index, bf *values) const {
    const unsigned col_offset = absolute_index / (stride - 1) * (1 + K + V) + K;
    const unsigned row = absolute_index % (stride - 1);
#pragma unroll
    for (unsigned i = 0; i < V; i++) {
      const unsigned col = i + col_offset;
      const unsigned idx = col * stride + row;
      values[i] = tables[idx];
    }
  }

  static DEVICE_FORCEINLINE u32 get_relative_index(const TableType table_type, const bf keys[K]) {
    switch (table_type) {
    case ZeroEntry:
      return 0;
    case RegIsZero:
    case JumpCleanupOffset:
    case GetSignExtensionByte:
    case U16GetSign:
    case U16GetSignAndHighByte:
    case MemoryOffsetGetBits:
    case MemoryLoadGetSigns:
    case RomAddressSpaceSeparator:
    case RangeCheck11:
    case RangeCheck12:
    case RangeCheck13:
    case U16SelectByteAndGetByteSign:
    case ExtendLoadedValue:
    case ConditionalJmpBranchSlt:
    case MemoryGetOffsetAndMaskWithTrap:
    case MemoryLoadHalfwordOrByte:
    case AlignedRomRead:
    case MemStoreClearOriginalRamValueLimb:
    case MemStoreClearWrittenValueLimb:
    case KeccakPermutationIndices12:
    case KeccakPermutationIndices34:
    case KeccakPermutationIndices56:
    case RotL:
    case Decoder:
      return index_for_keys<0>(keys);
    case XorSpecialIota:
    case AndN:
      return index_for_keys<0, 8>(keys);
    case StoreByteSourceContribution:
    case StoreByteExistingContribution:
      return index_for_keys<1, 0>(keys);
    case Xor3:
      return index_for_keys<3, 0>(keys);
    case Xor4:
      return index_for_keys<4, 0>(keys);
    case Xor7:
      return index_for_keys<7, 0>(keys);
    case Xor:
    case Or:
    case And:
    case TruncateShiftAmountAndRangeCheck8:
    case RangeCheck8x8:
    case AndNot:
      return index_for_keys<8, 0>(keys);
    case Xor9:
    case RangeCheck9x9:
      return index_for_keys<9, 0>(keys);
    case RangeCheck10x10:
      return index_for_keys<10, 0>(keys);
    case Xor12:
      return index_for_keys<12, 0>(keys);
    case ShiftImplementationOverBytes:
      return index_for_keys<16, 8, 3, 0>(keys);
    case RomRead:
      return bf::into_canonical_u32(keys[0]) >> 2;
    default:
      __trap();
    }
  }

  DEVICE_FORCEINLINE u32 get_index_and_set_values(const TableType table_type, const bf keys[K], bf *values) const {
    const u32 relative_index = get_relative_index(table_type, keys);
    const u32 absolute_index = get_absolute_index(table_type, relative_index);
    set_values_from_tables(absolute_index, values);
    return absolute_index;
  }
};

template <> DEVICE_FORCEINLINE void TableDriver<3, 0>::set_values_from_tables(const u32, bf *) const {}

} // namespace airbender::witness::tables
