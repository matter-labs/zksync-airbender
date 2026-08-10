#pragma once

#include "../memory_unrolled.cuh"
#include "../witness_generation.cuh"

using namespace ::airbender::trace::witness::generation;
using namespace ::airbender::trace::witness::memory::unrolled;
using namespace ::airbender::trace::witness::trace::unrolled;

namespace airbender::trace::witness::circuits::NAME {

#include UNROLLED_CIRCUIT_INCLUDE(NAME)

KERNEL(NAME, ORACLE)

DEVICE_FORCEINLINE u32 canonical(const bf value) { return bf::into_canonical_u32(value); }

template <unsigned I>
DEVICE_FORCEINLINE void emit_timestamp_pair(const TimestampData initial_ts, const TimestampData read_ts, const bool borrow,
                                            const matrix_setter<u32, st_modifier::cs> timestamp_mapping) {
  const bf two19 = bf::from_u32_unchecked(1u << 19);
  bf low = bf::sub(bf::from_u32_unchecked(read_ts.get_low()), bf::from_u32_unchecked(initial_ts.get_low()));
  low = bf::add(low, bf::mul(two19, bf::from_u32_unchecked(borrow)));
  low = bf::sub(low, bf::from_u32_unchecked(I));
  bf high = bf::sub(bf::from_u32_unchecked(read_ts.get_high()), bf::from_u32_unchecked(initial_ts.get_high()));
  high = bf::sub(high, bf::from_u32_unchecked(borrow));
  high = bf::add(high, two19);
  timestamp_mapping.set_at_col(2 + 2 * I, canonical(low));
  timestamp_mapping.set_at_col(3 + 2 * I, canonical(high));
}

struct AddSubMappingCapture {
  const matrix_setter<u32, st_modifier::cs> range16_mapping;
  const matrix_setter<u32, st_modifier::cs> timestamp_mapping;
  TimestampData initial_timestamp{};

  DEVICE_FORCEINLINE void on_machine_state(const bool, const u32, const TimestampData initial_ts, const u32 final_pc, const TimestampData final_ts) {
    initial_timestamp = initial_ts;
    const ushort2 final_pc_limbs = u32_to_u16_tuple(final_pc);
    range16_mapping.set_at_col(4, canonical(bf::from_u32_unchecked(final_pc_limbs.x)));
    range16_mapping.set_at_col(5, canonical(bf::from_u32_unchecked(final_pc_limbs.y)));
    timestamp_mapping.set_at_col(0, canonical(bf::from_u32_unchecked(final_ts.get_low())));
    timestamp_mapping.set_at_col(1, canonical(bf::from_u32_unchecked(final_ts.get_high())));
  }

  DEVICE_FORCEINLINE void on_decoder(const ExecutorFamilyDecoderData &) const {}

  template <unsigned I>
  DEVICE_FORCEINLINE void on_ram_access(const TimestampData read_timestamp, const u32, const bool has_write, const u32 write_value,
                                        const bool intermediate_borrow) const {
    if constexpr (I == 2) {
      if (has_write) {
        const ushort2 write_value_limbs = u32_to_u16_tuple(write_value);
        range16_mapping.set_at_col(2, canonical(bf::from_u32_unchecked(write_value_limbs.x)));
        range16_mapping.set_at_col(3, canonical(bf::from_u32_unchecked(write_value_limbs.y)));
      }
    }
    emit_timestamp_pair<I>(initial_timestamp, read_timestamp, intermediate_borrow, timestamp_mapping);
  }
};

struct AddSubGeneratedMappingProvider {
  const GlobalTraceProvider global;
  const matrix_setter<u32, st_modifier::cs> range16_mapping;

  template <typename T, unsigned IDX> DEVICE_FORCEINLINE T get_memory() const { return global.template get_memory<T, IDX>(); }

  template <typename T, unsigned IDX> DEVICE_FORCEINLINE T get_witness() const { return global.template get_witness<T, IDX>(); }

  template <unsigned IDX, typename T> DEVICE_FORCEINLINE void set_memory(const T &value) const { global.template set_memory<IDX>(value); }

  template <unsigned IDX, typename T> DEVICE_FORCEINLINE void set_witness(const T &value) const {
    global.template set_witness<IDX>(value);
    if constexpr (IDX == 11)
      range16_mapping.set_at_col(0, canonical(wrapped_f::from(value).inner));
    if constexpr (IDX == 12)
      range16_mapping.set_at_col(1, canonical(wrapped_f::from(value).inner));
  }
};

EXTERN __launch_bounds__(128, 8) __global__ void ab_generate_memory_and_witness_values_add_sub_with_mappings_kernel(
    const __grid_constant__ UnrolledMemoryLayout layout, const __grid_constant__ AuxLayoutData aux_layout_data,
    const __grid_constant__ UnrolledNonMemoryOracle oracle, matrix_setter<bf, st_modifier::cg> memory, matrix_setter<bf, st_modifier::cg> witness,
    matrix_setter<u32, st_modifier::cs> decoder_lookup_mapping, matrix_setter<u32, st_modifier::cs> range16_mapping,
    matrix_setter<u32, st_modifier::cs> timestamp_mapping, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  memory.add_row(gid);
  witness.add_row(gid);
  range16_mapping.add_row(gid);
  timestamp_mapping.add_row(gid);
  AddSubMappingCapture capture{range16_mapping, timestamp_mapping};
  process_machine_state_assuming_preprocessed_decoder<true>(layout, oracle, memory, witness, decoder_lookup_mapping.ptr, capture, gid);
  process_shuffle_ram_access_sets<true>(layout, aux_layout_data, oracle, memory, witness, capture, gid);
}

EXTERN __launch_bounds__(128, 8) __global__ void ab_generate_witness_values_add_sub_with_mappings_kernel(
    const __grid_constant__ UnrolledNonMemoryOracle oracle, matrix_getter<wrapped_f, ld_modifier::cg> generic_lookup_tables,
    matrix_setter<wrapped_f, st_modifier::cg> memory, matrix_setter<wrapped_f, st_modifier::cg> witness, matrix_setter<wrapped_f, st_modifier::cg> scratch,
    matrix_setter<u32, st_modifier::cs> generic_lookup_mapping, matrix_setter<u32, st_modifier::cs> range16_mapping,
    matrix_setter<u32, st_modifier::cs> timestamp_mapping, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  range16_mapping.add_row(gid);
  timestamp_mapping.add_row(gid);
  const GlobalTraceProvider global = {memory.ptr, witness.ptr, witness.stride, gid};
  const AddSubGeneratedMappingProvider places = {global, range16_mapping};
  const WitnessProxy<UnrolledNonMemoryOracle, AddSubGeneratedMappingProvider> p = {
      oracle, generic_lookup_tables.ptr, places, generic_lookup_mapping.ptr, scratch.ptr, static_cast<unsigned>(witness.stride), gid};
  FN_CALL(generate)
}

struct AddSubCapturedRow {
  bf memory_2;
  bf memory_3;
  bf memory_7;
  bf memory_8;
  bf memory_12;
  bf memory_13;
  bf memory_18;
  bf memory_19;
  bf witness_0;
  bf witness_1;
  bf witness_2;
  bf witness_3;
  bf witness_4;
  bf witness_5;
  bf witness_6;
  bf witness_7;
  bf witness_8;
  bf witness_10;
};

struct AddSubFusedCapture {
  AddSubMappingCapture mappings;
  AddSubCapturedRow &captured;

  DEVICE_FORCEINLINE void on_machine_state(const bool execute, const u32 initial_pc, const TimestampData initial_ts, const u32 final_pc,
                                           const TimestampData final_ts) {
    mappings.on_machine_state(execute, initial_pc, initial_ts, final_pc, final_ts);
    const ushort2 limbs = u32_to_u16_tuple(initial_pc);
    captured.memory_18 = bf::from_u32_unchecked(limbs.x);
    captured.memory_19 = bf::from_u32_unchecked(limbs.y);
  }

  DEVICE_FORCEINLINE void on_decoder(const ExecutorFamilyDecoderData &decoder) const {
    const ushort2 imm = u32_to_u16_tuple(decoder.imm);
    captured.witness_0 = bf::from_u32_unchecked(imm.x);
    captured.witness_1 = bf::from_u32_unchecked(imm.y);
    captured.witness_2 = bf::from_u32_unchecked(static_cast<bool>(decoder.opcode_family_bits & (1u << 0)));
    captured.witness_3 = bf::from_u32_unchecked(static_cast<bool>(decoder.opcode_family_bits & (1u << 1)));
    captured.witness_4 = bf::from_u32_unchecked(static_cast<bool>(decoder.opcode_family_bits & (1u << 2)));
    captured.witness_5 = bf::from_u32_unchecked(static_cast<bool>(decoder.opcode_family_bits & (1u << 3)));
    captured.witness_6 = bf::from_u32_unchecked(static_cast<bool>(decoder.opcode_family_bits & (1u << 4)));
    captured.witness_7 = bf::from_u32_unchecked(static_cast<bool>(decoder.opcode_family_bits & (1u << 5)));
    captured.witness_8 = bf::from_u32_unchecked(static_cast<bool>(decoder.opcode_family_bits & (1u << 6)));
    captured.witness_10 = bf::from_u32_unchecked(static_cast<bool>(decoder.opcode_family_bits & (1u << 8)));
  }

  template <unsigned I>
  DEVICE_FORCEINLINE void on_ram_access(const TimestampData read_timestamp, const u32 read_value, const bool has_write, const u32 write_value,
                                        const bool intermediate_borrow) const {
    mappings.template on_ram_access<I>(read_timestamp, read_value, has_write, write_value, intermediate_borrow);
    const ushort2 limbs = u32_to_u16_tuple(read_value);
    if constexpr (I == 0) {
      captured.memory_2 = bf::from_u32_unchecked(limbs.x);
      captured.memory_3 = bf::from_u32_unchecked(limbs.y);
    } else if constexpr (I == 1) {
      captured.memory_7 = bf::from_u32_unchecked(limbs.x);
      captured.memory_8 = bf::from_u32_unchecked(limbs.y);
    } else if constexpr (I == 2) {
      captured.memory_12 = bf::from_u32_unchecked(limbs.x);
      captured.memory_13 = bf::from_u32_unchecked(limbs.y);
    }
  }
};

template <unsigned> inline constexpr bool ADD_SUB_CAPTURED_INDEX_IS_UNSUPPORTED = false;

struct AddSubCapturedProvider {
  const AddSubCapturedRow &captured;
  wrapped_f *const __restrict__ witness;
  const matrix_setter<u32, st_modifier::cs> range16_mapping;
  const unsigned stride;
  const unsigned row;

  template <typename T, unsigned IDX> DEVICE_FORCEINLINE T get_memory() const {
    if constexpr (IDX == 2)
      return T::from(wrapped_f::new_(captured.memory_2));
    else if constexpr (IDX == 3)
      return T::from(wrapped_f::new_(captured.memory_3));
    else if constexpr (IDX == 7)
      return T::from(wrapped_f::new_(captured.memory_7));
    else if constexpr (IDX == 8)
      return T::from(wrapped_f::new_(captured.memory_8));
    else if constexpr (IDX == 12)
      return T::from(wrapped_f::new_(captured.memory_12));
    else if constexpr (IDX == 13)
      return T::from(wrapped_f::new_(captured.memory_13));
    else if constexpr (IDX == 18)
      return T::from(wrapped_f::new_(captured.memory_18));
    else if constexpr (IDX == 19)
      return T::from(wrapped_f::new_(captured.memory_19));
    else
      static_assert(ADD_SUB_CAPTURED_INDEX_IS_UNSUPPORTED<IDX>, "unsupported add/sub captured memory getter");
  }

  template <typename T, unsigned IDX> DEVICE_FORCEINLINE T get_witness() const {
    if constexpr (IDX == 0)
      return T::from(wrapped_f::new_(captured.witness_0));
    else if constexpr (IDX == 1)
      return T::from(wrapped_f::new_(captured.witness_1));
    else if constexpr (IDX == 2)
      return T::from(wrapped_f::new_(captured.witness_2));
    else if constexpr (IDX == 3)
      return T::from(wrapped_f::new_(captured.witness_3));
    else if constexpr (IDX == 4)
      return T::from(wrapped_f::new_(captured.witness_4));
    else if constexpr (IDX == 5)
      return T::from(wrapped_f::new_(captured.witness_5));
    else if constexpr (IDX == 6)
      return T::from(wrapped_f::new_(captured.witness_6));
    else if constexpr (IDX == 7)
      return T::from(wrapped_f::new_(captured.witness_7));
    else if constexpr (IDX == 8)
      return T::from(wrapped_f::new_(captured.witness_8));
    else if constexpr (IDX == 10)
      return T::from(wrapped_f::new_(captured.witness_10));
    else
      static_assert(ADD_SUB_CAPTURED_INDEX_IS_UNSUPPORTED<IDX>, "unsupported add/sub captured witness getter");
  }

  template <unsigned IDX, typename T> DEVICE_FORCEINLINE void set_memory(const T &) const {
    static_assert(ADD_SUB_CAPTURED_INDEX_IS_UNSUPPORTED<IDX>, "unsupported add/sub generated memory setter");
  }

  template <unsigned IDX, typename T> DEVICE_FORCEINLINE void set_witness(const T &value) const {
    const wrapped_f field_value = wrapped_f::from(value);
    witness[IDX * stride + row] = field_value;
    if constexpr (IDX == 11)
      range16_mapping.set_at_col(0, canonical(field_value.inner));
    if constexpr (IDX == 12)
      range16_mapping.set_at_col(1, canonical(field_value.inner));
  }
};

EXTERN __launch_bounds__(128, 4) __global__ void ab_generate_memory_and_witness_values_add_sub_fused_kernel(
    const __grid_constant__ UnrolledMemoryLayout layout, const __grid_constant__ AuxLayoutData aux_layout_data,
    const __grid_constant__ UnrolledNonMemoryOracle oracle, matrix_getter<wrapped_f, ld_modifier::cg> generic_lookup_tables,
    matrix_setter<bf, st_modifier::cg> memory, matrix_setter<bf, st_modifier::cg> witness, matrix_setter<wrapped_f, st_modifier::cg> scratch,
    matrix_setter<u32, st_modifier::cs> generic_lookup_mapping, matrix_setter<u32, st_modifier::cs> decoder_lookup_mapping,
    matrix_setter<u32, st_modifier::cs> range16_mapping, matrix_setter<u32, st_modifier::cs> timestamp_mapping, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  wrapped_f *const witness_base = reinterpret_cast<wrapped_f *>(witness.ptr);
  memory.add_row(gid);
  witness.add_row(gid);
  range16_mapping.add_row(gid);
  timestamp_mapping.add_row(gid);
  AddSubCapturedRow captured{};
  AddSubFusedCapture capture{{range16_mapping, timestamp_mapping}, captured};
  process_machine_state_assuming_preprocessed_decoder<true>(layout, oracle, memory, witness, decoder_lookup_mapping.ptr, capture, gid);
  process_shuffle_ram_access_sets<true>(layout, aux_layout_data, oracle, memory, witness, capture, gid);
  const AddSubCapturedProvider places = {captured, witness_base, range16_mapping, static_cast<unsigned>(witness.stride), gid};
  const WitnessProxy<UnrolledNonMemoryOracle, AddSubCapturedProvider> p = {
      oracle, generic_lookup_tables.ptr, places, generic_lookup_mapping.ptr, scratch.ptr, static_cast<unsigned>(witness.stride), gid};
  FN_CALL(generate)
}

} // namespace airbender::trace::witness::circuits::NAME
