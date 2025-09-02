#pragma once

#include "common.cuh"

enum TableType : u16 {
  ZeroEntry = 0,
  OpTypeBitmask,
  PowersOf2,
  InsnEncodingChecker,
  Xor = 4,
  CsrBitmask,
  Or = 6,
  And = 7,
  RangeCheckSmall, // 8
  RangeCheckLarge,
  AndNot,
  QuickDecodeDecompositionCheck4x4x4,
  QuickDecodeDecompositionCheck7x3x6,
  MRetProcessLow,
  MRetClearHigh,
  TrapProcessLow,
  U16GetSignAndHighByte, // 16
  JumpCleanupOffset,
  MemoryOffsetGetBits,
  MemoryLoadGetSigns,
  SRASignFiller,
  ConditionalOpUnsignedConditionsResolver,
  ConditionalOpAllConditionsResolver,
  RomAddressSpaceSeparator,
  RomRead, // 24
  SpecialCSRProperties,
  Xor3,
  Xor4,
  Xor7,
  Xor9,
  Xor12,
  U16SplitAsBytes,
  RangeCheck9x9, // 32
  RangeCheck10x10,
  RangeCheck11,
  RangeCheck12,
  RangeCheck13,
  ShiftImplementation,
  U16SelectByteAndGetByteSign,
  ExtendLoadedValue,
  StoreByteSourceContribution,
  StoreByteExistingContribution,
  TruncateShift,
  ConditionalJmpBranchSlt,
  MemoryGetOffsetAndMaskWithTrap,
  MemoryLoadHalfwordOrByte,
  AlignedRomRead,
  TruncateShiftAmount,
  SllWith16BitInputLow,
  SllWith16BitInputHigh,
  SrlWith16BitInputLow,
  SrlWith16BitInputHigh,
  Sra16BitInputSignFill,
  RangeCheck16WithZeroPads,
  MemStoreClearOriginalRamValueLimb,
  MemStoreClearWrittenValueLimb,
  KeccakPermutationIndices12,
  KeccakPermutationIndices34,
  KeccakPermutationIndices56,
  XorSpecialIota,
  AndN,
  RotL,
  DynamicPlaceholder,
};

DEVICE_FORCEINLINE const u16 *u32_as_u16s(const u32 &value) { return reinterpret_cast<const u16 *>(&value); }

DEVICE_FORCEINLINE void set_u16_values_from_u32(const u32 value, bf *values) {
  values[0] = bf(u32_as_u16s(value)[0]);
  values[1] = bf(u32_as_u16s(value)[1]);
}

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

template <unsigned N> DEVICE_FORCEINLINE void set_to_zero(bf *values) {
#pragma unroll
  for (unsigned i = 0; i < N; i++)
    values[i] = bf::zero();
}

template <> DEVICE_FORCEINLINE void set_to_zero<0>(bf *) {}

__constant__ constexpr u64 KECCAK_PERMUTATIONS_ADJUSTED[25 * 25] = {
    0,  1,  2,  3,  4,  5,  6,  7,  8,  9,  10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0,  6,  12, 18, 24, 3,  9,  10, 16, 22, 1,  7,
    13, 19, 20, 4,  5,  11, 17, 23, 2,  8,  14, 15, 21, 0,  9,  13, 17, 21, 18, 22, 1,  5,  14, 6,  10, 19, 23, 2,  24, 3,  7,  11, 15, 12, 16, 20, 4,
    8,  0,  22, 19, 11, 8,  17, 14, 6,  3,  20, 9,  1,  23, 15, 12, 21, 18, 10, 7,  4,  13, 5,  2,  24, 16, 0,  14, 23, 7,  16, 11, 20, 9,  18, 2,  22,
    6,  15, 4,  13, 8,  17, 1,  10, 24, 19, 3,  12, 21, 5,  0,  20, 15, 10, 5,  7,  2,  22, 17, 12, 14, 9,  4,  24, 19, 16, 11, 6,  1,  21, 23, 18, 13,
    8,  3,  0,  2,  4,  1,  3,  10, 12, 14, 11, 13, 20, 22, 24, 21, 23, 5,  7,  9,  6,  8,  15, 17, 19, 16, 18, 0,  12, 24, 6,  18, 1,  13, 20, 7,  19,
    2,  14, 21, 8,  15, 3,  10, 22, 9,  16, 4,  11, 23, 5,  17, 0,  13, 21, 9,  17, 6,  19, 2,  10, 23, 12, 20, 8,  16, 4,  18, 1,  14, 22, 5,  24, 7,
    15, 3,  11, 0,  19, 8,  22, 11, 9,  23, 12, 1,  15, 13, 2,  16, 5,  24, 17, 6,  20, 14, 3,  21, 10, 4,  18, 7,  0,  23, 16, 14, 7,  22, 15, 13, 6,
    4,  19, 12, 5,  3,  21, 11, 9,  2,  20, 18, 8,  1,  24, 17, 10, 0,  15, 5,  20, 10, 14, 4,  19, 9,  24, 23, 13, 3,  18, 8,  7,  22, 12, 2,  17, 16,
    6,  21, 11, 1,  0,  4,  3,  2,  1,  20, 24, 23, 22, 21, 15, 19, 18, 17, 16, 10, 14, 13, 12, 11, 5,  9,  8,  7,  6,  0,  24, 18, 12, 6,  2,  21, 15,
    14, 8,  4,  23, 17, 11, 5,  1,  20, 19, 13, 7,  3,  22, 16, 10, 9,  0,  21, 17, 13, 9,  12, 8,  4,  20, 16, 24, 15, 11, 7,  3,  6,  2,  23, 19, 10,
    18, 14, 5,  1,  22, 0,  8,  11, 19, 22, 13, 16, 24, 2,  5,  21, 4,  7,  10, 18, 9,  12, 15, 23, 1,  17, 20, 3,  6,  14, 0,  16, 7,  23, 14, 19, 5,
    21, 12, 3,  8,  24, 10, 1,  17, 22, 13, 4,  15, 6,  11, 2,  18, 9,  20, 0,  5,  10, 15, 20, 23, 3,  8,  13, 18, 16, 21, 1,  6,  11, 14, 19, 24, 4,
    9,  7,  12, 17, 22, 2,  0,  3,  1,  4,  2,  15, 18, 16, 19, 17, 5,  8,  6,  9,  7,  20, 23, 21, 24, 22, 10, 13, 11, 14, 12, 0,  18, 6,  24, 12, 4,
    17, 5,  23, 11, 3,  16, 9,  22, 10, 2,  15, 8,  21, 14, 1,  19, 7,  20, 13, 0,  17, 9,  21, 13, 24, 11, 3,  15, 7,  18, 5,  22, 14, 1,  12, 4,  16,
    8,  20, 6,  23, 10, 2,  19, 0,  11, 22, 8,  19, 21, 7,  18, 4,  10, 17, 3,  14, 20, 6,  13, 24, 5,  16, 2,  9,  15, 1,  12, 23, 0,  7,  14, 16, 23,
    8,  10, 17, 24, 1,  11, 18, 20, 2,  9,  19, 21, 3,  5,  12, 22, 4,  6,  13, 15, 0,  10, 20, 5,  15, 16, 1,  11, 21, 6,  7,  17, 2,  12, 22, 23, 8,
    18, 3,  13, 14, 24, 9,  19, 4,  0,  1,  2,  3,  4,  5,  6,  7,  8,  9,  10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
};

__constant__ constexpr u64 KECCAK_ROUND_CONSTANTS_ADJUSTED[24] = {
    0,
    1,
    32898,
    9223372036854808714,
    9223372039002292224,
    32907,
    2147483649,
    9223372039002292353,
    9223372036854808585,
    138,
    136,
    2147516425,
    2147483658,
    2147516555,
    9223372036854775947,
    9223372036854808713,
    9223372036854808579,
    9223372036854808578,
    9223372036854775936,
    32778,
    9223372039002259466,
    9223372039002292353,
    9223372036854808704,
    2147483649,
};

__constant__ constexpr u64 KECCAK_PRECOMPILE_THETA_RHO_IDCOLS[5] = {29, 25, 26, 27, 28};

template <unsigned K, unsigned V> struct TableDriver {
  static_assert(K + V == 3);
  const bf *tables;
  const unsigned stride;
  const u32 *offsets;

  template <TableType T> DEVICE_FORCEINLINE u32 get_absolute_index(const u32 index) const { return offsets[T] + index; }

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

  template <TableType T> DEVICE_FORCEINLINE u32 single_key_set_values_from_tables(const bf keys[K], bf *values) const {
    const u32 index = index_for_keys<0>(keys);
    const u32 absolute_index = get_absolute_index<T>(index);
    if (V != 0)
      set_values_from_tables(absolute_index, values);
    return absolute_index;
  }

  DEVICE_FORCEINLINE u32 op_type_bitmask(const bf keys[K], bf *values) const { return single_key_set_values_from_tables<OpTypeBitmask>(keys, values); }

  template <TableType T> DEVICE_FORCEINLINE u32 set_values_from_single_key(const bf keys[K], bf *values, void (*const setter)(u32, u32 *)) const {
    const u32 index = index_for_keys<0>(keys);
    if (V != 0)
      setter(index, reinterpret_cast<u32 *>(values));
    return get_absolute_index<T>(index);
  }

  DEVICE_FORCEINLINE u32 powers_of_2(const bf keys[K], bf *values) const {
    auto setter = [](const u32 index, u32 *result) {
      const u32 shifted = 1u << index;
      const auto u16s = u32_as_u16s(shifted);
      result[0] = u16s[0];
      result[1] = u16s[1];
    };
    return set_values_from_single_key<PowersOf2>(keys, values, setter);
  }

  template <TableType T, unsigned WIDTH> DEVICE_FORCEINLINE u32 binary_op(const bf keys[K], bf *values, u32 (*const op)(u32, u32)) const {
    u32 binary_keys[2];
    keys_into_binary_keys<2>(keys, binary_keys);
    const u32 index = index_for_binary_keys<WIDTH, 0>(binary_keys);
    if (V != 0)
      values[0] = bf(op(binary_keys[0], binary_keys[1]));
    return get_absolute_index<T>(index);
  }

  template <TableType T, unsigned WIDTH> DEVICE_FORCEINLINE u32 xor_(const bf keys[K], bf *values) const {
    auto op = [](const u32 a, const u32 b) { return a ^ b; };
    return binary_op<T, WIDTH>(keys, values, op);
  }

  DEVICE_FORCEINLINE u32 or_(const bf keys[K], bf *values) const {
    auto op = [](const u32 a, const u32 b) { return a | b; };
    return binary_op<Or, 8>(keys, values, op);
  }

  DEVICE_FORCEINLINE u32 and_(const bf keys[K], bf *values) const {
    auto op = [](const u32 a, const u32 b) { return a & b; };
    return binary_op<And, 8>(keys, values, op);
  }

  DEVICE_FORCEINLINE u32 and_not(const bf keys[K], bf *values) const {
    auto op = [](const u32 a, const u32 b) { return a & !b; };
    return binary_op<AndNot, 8>(keys, values, op);
  }

  template <TableType T, unsigned... SHIFTS> DEVICE_FORCEINLINE u32 ranges_generic(const bf keys[K]) const {
    u32 binary_keys[sizeof...(SHIFTS)];
    keys_into_binary_keys<sizeof...(SHIFTS)>(keys, binary_keys);
    const u32 index = index_for_binary_keys<SHIFTS...>(binary_keys);
    return get_absolute_index<T>(index);
  }

  DEVICE_FORCEINLINE u32 u16_get_sign_and_high_byte(const bf keys[K], bf *values) const {
    auto setter = [](const u32 index, u32 *result) {
      result[0] = index >> 15;
      result[1] = index >> 8;
    };
    return set_values_from_single_key<U16GetSignAndHighByte>(keys, values, setter);
  }

  DEVICE_FORCEINLINE u32 jump_cleanup_offset(const bf keys[K], bf *values) const {
    auto setter = [](const u32 index, u32 *result) {
      result[0] = index >> 1 & 0x1;
      result[1] = index & ~0x3;
    };
    return set_values_from_single_key<JumpCleanupOffset>(keys, values, setter);
  }

  DEVICE_FORCEINLINE u32 memory_offset_get_bits(const bf keys[K], bf *values) const {
    auto setter = [](const u32 index, u32 *result) {
      result[0] = index & 0x1;
      result[1] = index >> 1 & 0x1;
    };
    return set_values_from_single_key<MemoryOffsetGetBits>(keys, values, setter);
  }

  DEVICE_FORCEINLINE u32 memory_load_get_signs(const bf keys[K], bf *values) const {
    auto setter = [](const u32 index, u32 *result) {
      result[0] = index >> 7 & 0x1;
      result[1] = index >> 15 & 0x1;
    };
    return set_values_from_single_key<MemoryLoadGetSigns>(keys, values, setter);
  }

  DEVICE_FORCEINLINE u32 sra_sign_filler(const bf keys[K], bf *values) const {
    auto setter = [](const u32 index, u32 *result) {
      const bool input_sign = index & 1 != 0;
      const bool is_sra = index >> 1 & 1 != 0;
      const u32 shift_amount = index >> 2;
      if (input_sign == false || is_sra == false) {
        // either it's positive, or we are not doing SRA (and it's actually the only case when shift amount can be >= 32
        // in practice, but we have to fill the table)
        result[0] = 0;
        result[1] = 0;
      } else if (shift_amount == 0) {
        // special case
        result[0] = 0;
        result[1] = 0;
      } else {
        const unsigned mask = 0xffffffff << (32 - shift_amount);
        result[0] = mask & 0xffff;
        result[1] = mask >> 16;
      }
    };
    return set_values_from_single_key<SRASignFiller>(keys, values, setter);
  }

  DEVICE_FORCEINLINE u32 conditional_op_all_conditions(const bf keys[K], bf *values) const {
    auto setter = [](const u32 index, u32 *result) {
      constexpr u32 FUNCT3_MASK = 0x7;
      constexpr unsigned UNSIGNED_LT_BIT_SHIFT = 3;
      constexpr unsigned EQ_BIT_SHIFT = 4;
      constexpr unsigned SRC1_BIT_SHIFT = 5;
      constexpr unsigned SRC2_BIT_SHIFT = 6;

      const u32 funct3 = index & FUNCT3_MASK;
      const bool unsigned_lt_flag = index & 1u << UNSIGNED_LT_BIT_SHIFT;
      const bool eq_flag = index & 1u << EQ_BIT_SHIFT;
      const bool src1_bit = index & 1u << SRC1_BIT_SHIFT;
      const bool src2_bit = index & 1u << SRC2_BIT_SHIFT;
      const bool operands_different_signs_flag = src1_bit ^ src2_bit;

      bool should_branch = false;
      bool should_store = false;

      switch (funct3) {
      case 0b000:
        // BEQ
        should_branch = eq_flag;
        should_store = false;
        break;
      case 0b001:
        // BNE
        should_branch = !eq_flag;
        should_store = false;
        break;
      case 0b010:
        // STL
        // signs are different,
        // so if rs1 is negative, and rs2 is positive (so condition holds)
        // then LT must be false
        // or
        // just unsigned comparison works for both cases
        should_branch = false;
        should_store = operands_different_signs_flag ^ unsigned_lt_flag;
        break;
      case 0b011:
        // STLU
        // just unsigned comparison works for both cases
        should_branch = false;
        should_store = unsigned_lt_flag;
        break;
      case 0b100:
        // BLT
        // signs are different,
        // so if rs1 is negative, and rs2 is positive (so condition holds)
        // then LT must be false
        // or
        // just unsigned comparison works for both cases
        should_branch = operands_different_signs_flag ^ unsigned_lt_flag;
        should_store = false;
        break;
      case 0b101:
        // BGE
        // inverse of BLT
        should_branch = !(operands_different_signs_flag ^ unsigned_lt_flag);
        should_store = false;
        break;
      case 0b110:
        // BLTU
        should_branch = unsigned_lt_flag;
        should_store = false;
        break;
      case 0b111:
        // BGEU
        // inverse of BLTU
        should_branch = !unsigned_lt_flag;
        should_store = false;
        break;
      default:
        break;
      }

      result[0] = should_branch;
      result[1] = should_store;
    };
    return set_values_from_single_key<ConditionalOpAllConditionsResolver>(keys, values, setter);
  }

  DEVICE_FORCEINLINE u32 rom_address_space_separator(const bf keys[K], bf *values) const {
    auto setter = [](const u32 index, u32 *result) {
      constexpr unsigned ROM_ADDRESS_SPACE_SECOND_WORD_BITS = 5;
      result[0] = index >> ROM_ADDRESS_SPACE_SECOND_WORD_BITS != 0;
      result[1] = index & (1u << ROM_ADDRESS_SPACE_SECOND_WORD_BITS) - 1;
    };
    return set_values_from_single_key<RomAddressSpaceSeparator>(keys, values, setter);
  }

  DEVICE_FORCEINLINE u32 rom_read(const bf keys[K], bf *values) const {
    const u32 index = bf::into_canonical_u32(keys[0]) >> 2;
    const u32 absolute_index = get_absolute_index<RomRead>(index);
    if (V != 0)
      set_values_from_tables(absolute_index, values);
    return absolute_index;
  }

  DEVICE_FORCEINLINE u32 special_csr_properties(const bf keys[K], bf *values) const {
    return single_key_set_values_from_tables<SpecialCSRProperties>(keys, values);
  }

  DEVICE_FORCEINLINE u32 u16_split_as_bytes(const bf keys[K], bf *values) const {
    auto setter = [](const u32 index, u32 *result) {
      result[0] = index & 0xff;
      result[1] = index >> 8;
    };
    return set_values_from_single_key<U16SplitAsBytes>(keys, values, setter);
  }

  DEVICE_FORCEINLINE u32 shift_implementation(const bf keys[K], bf *values) const {
    // take 16 bits of input half-word || shift || is_right
    auto setter = [](const u32 index, u32 *result) {
      const u32 a = index;
      const u32 input_word = a & 0xffff;
      const u32 shift_amount = a >> 16 & 0b11111;
      const bool is_right_shift = a >> (16 + 5) != 0;
      if (is_right_shift) {
        const u32 input = input_word << 16;
        const u32 t = input >> shift_amount;
        const u32 in_place = t >> 16;
        const u32 overflow = t & 0xffff;
        result[0] = in_place;
        result[1] = overflow;
      } else {
        const u32 input = input_word;
        const u32 t = input << shift_amount;
        const u32 in_place = t & 0xffff;
        const u32 overflow = t >> 16;
        result[0] = in_place;
        result[1] = overflow;
      }
    };
    return set_values_from_single_key<ShiftImplementation>(keys, values, setter);
  }

  DEVICE_FORCEINLINE u32 u16_select_byte_and_get_byte_sign(const bf keys[K], bf *values) const {
    auto setter = [](const u32 index, u32 *result) {
      const bool selector_bit = index >> 16 != 0;
      const u32 selected_byte = (selector_bit ? index >> 8 : index) & 0xff;
      const bool sign_bit = (selected_byte & 1u << 7) != 0;
      result[0] = selected_byte;
      result[1] = sign_bit;
    };
    return set_values_from_single_key<U16SelectByteAndGetByteSign>(keys, values, setter);
  }

  DEVICE_FORCEINLINE u32 extend_loaded_value(const bf keys[K], bf *values) const {
    // 16-bit half-word || low/high value bit || funct3
    auto setter = [](const u32 index, u32 *result) {
      const u32 word = index & 0xffff;
      const bool use_high_half = (index & 0x00010000) != 0;
      const u32 funct3 = index >> 17;
      const u32 selected_byte = use_high_half ? word >> 8 : word & 0xff;
      u32 loaded_word = 0;
      switch (funct3) {
      case 0b000:
        // LB
        // sign-extend selected byte
        loaded_word = (selected_byte & 0x80) != 0 ? selected_byte | 0xffffff00 : selected_byte;
        break;
      case 0b100:
        // LBU
        // zero-extend selected byte
        loaded_word = selected_byte;
        break;
      case 0b001:
        // LH
        // sign-extend selected word
        loaded_word = (word & 0x8000) != 0 ? word | 0xffff0000 : word;
        break;
      case 0b101:
        // LHU
        // zero-extend selected word
        loaded_word = word;
        break;
      default:
        // Not important
        loaded_word = 0;
      }
      result[0] = loaded_word & 0xffff;
      result[1] = loaded_word >> 16;
    };
    return set_values_from_single_key<ExtendLoadedValue>(keys, values, setter);
  }

  DEVICE_FORCEINLINE u32 store_byte_source_contribution(const bf keys[K], bf *values) const {
    u32 binary_keys[2];
    keys_into_binary_keys<2>(keys, binary_keys);
    const u32 index = index_for_binary_keys<1, 0>(binary_keys);
    if (V != 0) {
      const u32 a = binary_keys[0];
      const u32 b = binary_keys[1];
      const bool bit_0 = b != 0;
      const u32 byte = a & 0xff;
      const u32 result = bit_0 ? byte << 8 : byte;
      values[0] = bf(result);
    }
    return get_absolute_index<StoreByteSourceContribution>(index);
  }

  DEVICE_FORCEINLINE u32 store_byte_existing_contribution(const bf keys[K], bf *values) const {
    u32 binary_keys[2];
    keys_into_binary_keys<2>(keys, binary_keys);
    const u32 index = index_for_binary_keys<1, 0>(binary_keys);
    if (V != 0) {
      const u32 a = binary_keys[0];
      const u32 b = binary_keys[1];
      const bool bit_0 = b != 0;
      const u32 result = bit_0 ? a & 0x00ff : a & 0xff00;
      values[0] = bf(result);
    }
    return get_absolute_index<StoreByteExistingContribution>(index);
  }

  DEVICE_FORCEINLINE u32 truncate_shift(const bf keys[K], bf *values) const {
    u32 binary_keys[2];
    keys_into_binary_keys<2>(keys, binary_keys);
    const u32 index = index_for_binary_keys<1, 0>(binary_keys);
    if (V != 0) {
      const u32 a = binary_keys[0];
      const u32 b = binary_keys[1];
      const bool is_right_shift = b != 0;
      const u32 shift_amount = a & 31;
      const u32 result = is_right_shift ? shift_amount : 32 - shift_amount;
      values[0] = bf(result);
    }
    return get_absolute_index<TruncateShift>(index);
  }

  template <TableType T, unsigned I, unsigned J> DEVICE_FORCEINLINE u32 kecak_permutation_indices(const bf keys[K], bf *values) const {
    auto setter = [](const u32 index, u32 *result) {
      const u32 iter = __clz(static_cast<int>(__brev((index >> 5) & 0b11111)));
      const u32 round = index >> 10;
      u64 indices[6] = {0, 1, 2, 3, 4, 5};
      if (iter < 5 && round < 24) {
        constexpr u32 PRECOMPILE_IOTA_COLUMNXOR = 0;
        constexpr u32 PRECOMPILE_COLUMNMIX = 1;
        constexpr u32 PRECOMPILE_THETA_RHO = 2;
        constexpr u32 PRECOMPILE_CHI1 = 3;
        constexpr u32 PRECOMPILE_CHI2 = 4;
        const u32 precompile = __clz(static_cast<int>(__brev(index & 0b11111)));
        switch (precompile) {
        case PRECOMPILE_IOTA_COLUMNXOR: {
          const auto pi = &KECCAK_PERMUTATIONS_ADJUSTED[round * 25]; // indices before applying round permutation
          const u64 idcol = 25 + iter;
          const u64 idx0 = pi[iter];
          const u64 idx5 = pi[iter + 5];
          const u64 idx10 = pi[iter + 10];
          const u64 idx15 = pi[iter + 15];
          const u64 idx20 = pi[iter + 20];
          indices[0] = idx0;
          indices[1] = idx5;
          indices[2] = idx10;
          indices[3] = idx15;
          indices[4] = idx20;
          indices[5] = idcol;
          break;
        }
        case PRECOMPILE_COLUMNMIX:
          indices[0] = 25;
          indices[1] = 26;
          indices[2] = 27;
          indices[3] = 28;
          indices[4] = 29;
          indices[5] = 0;
          break;
        case PRECOMPILE_THETA_RHO: {
          const auto pi = &KECCAK_PERMUTATIONS_ADJUSTED[round * 25]; // indices before applying round permutation
          const u64 idcol = KECCAK_PRECOMPILE_THETA_RHO_IDCOLS[iter];
          const u64 idx0 = pi[iter];
          const u64 idx5 = pi[iter + 5];
          const u64 idx10 = pi[iter + 10];
          const u64 idx15 = pi[iter + 15];
          const u64 idx20 = pi[iter + 20];
          indices[0] = idx0;
          indices[1] = idx5;
          indices[2] = idx10;
          indices[3] = idx15;
          indices[4] = idx20;
          indices[5] = idcol;
          break;
        }
        case PRECOMPILE_CHI1: {
          const auto pi = &KECCAK_PERMUTATIONS_ADJUSTED[(round + 1) * 25]; // indices after applying round permutation
          const u64 idx = iter * 5;
          const u64 idx1 = pi[idx + 1];
          const u64 idx2 = pi[idx + 2];
          const u64 idx3 = pi[idx + 3];
          const u64 idx4 = pi[idx + 4];
          indices[0] = idx1;
          indices[1] = idx2;
          indices[2] = idx3;
          indices[3] = idx4;
          indices[4] = 25;
          indices[5] = 26;
          break;
        }
        case PRECOMPILE_CHI2: {
          const auto pi = &KECCAK_PERMUTATIONS_ADJUSTED[(round + 1) * 25]; // indices after applying round permutation
          const u64 idx = iter * 5;
          const u64 idx0 = pi[idx];
          const u64 idx3 = pi[idx + 3];
          const u64 idx4 = pi[idx + 4];
          indices[0] = idx0;
          indices[1] = idx3;
          indices[2] = idx4;
          indices[3] = 25;
          indices[4] = 26;
          indices[5] = 27;
          break;
        }
        default:
          break;
        }
      }
      result[0] = indices[I];
      result[1] = indices[J];
    };
    return set_values_from_single_key<T>(keys, values, setter);
  }

  DEVICE_FORCEINLINE u32 xor_special_iota(const bf keys[K], bf *values) const {
    u32 binary_keys[2];
    keys_into_binary_keys<2>(keys, binary_keys);
    const u32 index = index_for_binary_keys<0, 8>(binary_keys);
    if (V != 0) {
      const u32 a = binary_keys[0];
      const u32 b_control = binary_keys[1];
      const u32 round_if_iter0 = b_control & 0b11111;
      const u32 u8_position = b_control >> 5;
      u32 b = 0;
      if (round_if_iter0 < 24) {
        const u64 round_constant = KECCAK_ROUND_CONSTANTS_ADJUSTED[round_if_iter0];
        b = round_constant >> (u8_position * 8) & 0xff;
      }
      const u32 result = a ^ b;
      values[0] = bf(result);
    }
    return get_absolute_index<XorSpecialIota>(index);
  }

  DEVICE_FORCEINLINE u32 andn(const bf keys[K], bf *values) const {
    u32 binary_keys[2];
    keys_into_binary_keys<2>(keys, binary_keys);
    const u32 index = index_for_binary_keys<0, 8>(binary_keys);
    if (V != 0) {
      const u32 a = binary_keys[0];
      const u32 b = binary_keys[1];
      const u32 result = !a & b;
      values[0] = bf(result);
    }
    return get_absolute_index<AndN>(index);
  }

  DEVICE_FORCEINLINE u32 rotl(const bf keys[K], bf *values) const {
    auto setter = [](const u32 index, u32 *result) {
      const u32 word = index & 0xffff;
      const u32 rot_const = index >> 16;
      result[0] = word >> (16 - rot_const);
      result[1] = word << rot_const & 0xffff;
    };
    return set_values_from_single_key<RotL>(keys, values, setter);
  }

  DEVICE_FORCEINLINE u32 get_index_and_set_values(const TableType table_type, const bf keys[K], bf *values) const {
    switch (table_type) {
    case ZeroEntry:
      set_to_zero<V>(values);
      return 0;
    case OpTypeBitmask:
      return op_type_bitmask(keys, values);
    case PowersOf2:
      return powers_of_2(keys, values);
    case Xor:
      return xor_<Xor, 8>(keys, values);
    case Or:
      return or_(keys, values);
    case And:
      return and_(keys, values);
    case RangeCheckSmall:
      return ranges_generic<RangeCheckSmall, 8, 0>(keys);
    case RangeCheckLarge:
      return ranges_generic<RangeCheckLarge, 0>(keys);
    case AndNot:
      return and_not(keys, values);
    case QuickDecodeDecompositionCheck4x4x4:
      return ranges_generic<QuickDecodeDecompositionCheck4x4x4, 8, 4, 0>(keys);
    case QuickDecodeDecompositionCheck7x3x6:
      return ranges_generic<QuickDecodeDecompositionCheck7x3x6, 9, 6, 0>(keys);
    case U16GetSignAndHighByte:
      return u16_get_sign_and_high_byte(keys, values);
    case JumpCleanupOffset:
      return jump_cleanup_offset(keys, values);
    case MemoryOffsetGetBits:
      return memory_offset_get_bits(keys, values);
    case MemoryLoadGetSigns:
      return memory_load_get_signs(keys, values);
    case SRASignFiller:
      return sra_sign_filler(keys, values);
    case ConditionalOpAllConditionsResolver:
      return conditional_op_all_conditions(keys, values);
    case RomAddressSpaceSeparator:
      return rom_address_space_separator(keys, values);
    case RomRead:
      return rom_read(keys, values);
    case SpecialCSRProperties:
      return special_csr_properties(keys, values);
    case Xor3:
      return xor_<Xor3, 3>(keys, values);
    case Xor4:
      return xor_<Xor4, 4>(keys, values);
    case Xor7:
      return xor_<Xor7, 7>(keys, values);
    case Xor9:
      return xor_<Xor9, 9>(keys, values);
    case Xor12:
      return xor_<Xor12, 12>(keys, values);
    case U16SplitAsBytes:
      return u16_split_as_bytes(keys, values);
    case RangeCheck9x9:
      return ranges_generic<RangeCheck9x9, 9, 0>(keys);
    case RangeCheck10x10:
      return ranges_generic<RangeCheck10x10, 10, 0>(keys);
    case RangeCheck11:
      return ranges_generic<RangeCheck11, 0>(keys);
    case RangeCheck12:
      return ranges_generic<RangeCheck12, 0>(keys);
    case RangeCheck13:
      return ranges_generic<RangeCheck13, 0>(keys);
    case ShiftImplementation:
      return shift_implementation(keys, values);
    case U16SelectByteAndGetByteSign:
      return u16_select_byte_and_get_byte_sign(keys, values);
    case ExtendLoadedValue:
      return extend_loaded_value(keys, values);
    case StoreByteSourceContribution:
      return store_byte_source_contribution(keys, values);
    case StoreByteExistingContribution:
      return store_byte_existing_contribution(keys, values);
    case TruncateShift:
      return truncate_shift(keys, values);
    case ConditionalJmpBranchSlt:
    case MemoryGetOffsetAndMaskWithTrap:
    case MemoryLoadHalfwordOrByte:
    case AlignedRomRead:
    case TruncateShiftAmount:
    case SllWith16BitInputLow:
    case SllWith16BitInputHigh:
    case SrlWith16BitInputLow:
    case SrlWith16BitInputHigh:
    case Sra16BitInputSignFill:
    case RangeCheck16WithZeroPads:
    case MemStoreClearOriginalRamValueLimb:
    case MemStoreClearWrittenValueLimb:
      __trap();
      break;
    case KeccakPermutationIndices12:
      return kecak_permutation_indices<KeccakPermutationIndices12, 0, 1>(keys, values);
    case KeccakPermutationIndices34:
      return kecak_permutation_indices<KeccakPermutationIndices34, 2, 3>(keys, values);
    case KeccakPermutationIndices56:
      return kecak_permutation_indices<KeccakPermutationIndices56, 4, 5>(keys, values);
    case XorSpecialIota:
      return xor_special_iota(keys, values);
    case AndN:
      return andn(keys, values);
    case RotL:
      return rotl(keys, values);
    default:
      __trap();
    }
  }
};

template <> DEVICE_FORCEINLINE void TableDriver<3, 0>::set_values_from_tables(const u32, bf *) const {}
