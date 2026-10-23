#pragma once

#include "../memory.cuh"
#include "field.cuh"
#include <concepts>

namespace airbender::trace::witness::memory {

template <typename Dst>
  requires std::same_as<typename Dst::value_type, pr>
DEVICE_FORCEINLINE void write_bool_value(const Address column, const bool value, const Dst &dst) {
  dst.set_at_col(column.offset, ::airbender::trace::witness::proth120::pr_from_u32(value));
}

template <typename Dst>
  requires std::same_as<typename Dst::value_type, pr>
DEVICE_FORCEINLINE void write_bool_value(const u32 column, const bool value, const Dst &dst) {
  dst.set_at_col(column, ::airbender::trace::witness::proth120::pr_from_u32(value));
}

template <typename Dst>
  requires std::same_as<typename Dst::value_type, pr>
DEVICE_FORCEINLINE void write_u8_value(const Address column, const u8 value, const Dst &dst) {
  dst.set_at_col(column.offset, ::airbender::trace::witness::proth120::pr_from_u32(value));
}

template <typename Dst>
  requires std::same_as<typename Dst::value_type, pr>
DEVICE_FORCEINLINE void write_u8_value(const u32 column, const u8 value, const Dst &dst) {
  dst.set_at_col(column, ::airbender::trace::witness::proth120::pr_from_u32(value));
}

template <typename Dst>
  requires std::same_as<typename Dst::value_type, pr>
DEVICE_FORCEINLINE void write_u16_value(const Address column, const u16 value, const Dst &dst) {
  dst.set_at_col(column.offset, ::airbender::trace::witness::proth120::pr_from_u32(value));
}

template <typename Dst>
  requires std::same_as<typename Dst::value_type, pr>
DEVICE_FORCEINLINE void write_u16_value(const u32 column, const u16 value, const Dst &dst) {
  dst.set_at_col(column, ::airbender::trace::witness::proth120::pr_from_u32(value));
}

template <typename Dst>
  requires std::same_as<typename Dst::value_type, pr>
DEVICE_FORCEINLINE void write_u32_value(const u32 columns[REGISTER_SIZE], const u32 value, const Dst &dst) {
  static_assert(REGISTER_SIZE == 2);
  const u32 low_index = columns[0];
  const u32 high_index = columns[1];
  const u32 low_value = value & 0xffff;
  const u32 high_value = value >> 16;
  dst.set_at_col(low_index, ::airbender::trace::witness::proth120::pr_from_u32(low_value));
  dst.set_at_col(high_index, ::airbender::trace::witness::proth120::pr_from_u32(high_value));
}

template <typename Dst>
  requires std::same_as<typename Dst::value_type, pr>
DEVICE_FORCEINLINE void write_u32_value_as_u8_limbs(const u32 columns[REGISTER_SIZE * 2], const u32 value, const Dst &dst) {
  static_assert(REGISTER_SIZE == 2);
#pragma unroll
  for (unsigned byte = 0; byte < REGISTER_SIZE * 2; ++byte) {
    const u32 column = columns[byte];
    const u32 byte_value = (value >> (byte * 8)) & 0xff;
    dst.set_at_col(column, ::airbender::trace::witness::proth120::pr_from_u32(byte_value));
  }
}

template <typename Dst>
  requires std::same_as<typename Dst::value_type, pr>
DEVICE_FORCEINLINE void write_ram_word_value(const RamWordRepresentation &representation, const u32 value, const Dst &dst) {
  switch (representation.tag) {
  case Zero:
    break;
  case U16Limbs:
    write_u32_value(representation.payload.ram_word_u16_limbs.limbs, value, dst);
    break;
  case U8Limbs:
    write_u32_value_as_u8_limbs(representation.payload.ram_word_u8_limbs.limbs, value, dst);
    break;
  }
}

template <typename Dst>
  requires std::same_as<typename Dst::value_type, pr>
DEVICE_FORCEINLINE void write_u32_as_bf_value(const u32 column, const u32 value, const Dst &dst) {
  dst.set_at_col(column, ::airbender::trace::witness::proth120::pr_from_u32(value));
}

template <typename Dst>
  requires std::same_as<typename Dst::value_type, pr>
DEVICE_FORCEINLINE void write_timestamp_value(const u32 columns[NUM_TIMESTAMP_COLUMNS_FOR_RAM], const TimestampData value, const Dst &dst) {
  static_assert(NUM_TIMESTAMP_COLUMNS_FOR_RAM == 2);
  const u32 low_index = columns[0];
  const u32 high_index = columns[1];
  const u32 low_value = value.get_low();
  const u32 high_value = value.get_high();
  dst.set_at_col(low_index, ::airbender::trace::witness::proth120::pr_from_u32(low_value));
  dst.set_at_col(high_index, ::airbender::trace::witness::proth120::pr_from_u32(high_value));
}

} // namespace airbender::trace::witness::memory
