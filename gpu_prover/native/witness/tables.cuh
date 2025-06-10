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
    default:
      __trap();
    }
  }
};

template <> DEVICE_FORCEINLINE void TableDriver<3, 0>::set_values_from_tables(const u32, bf *) const {}
