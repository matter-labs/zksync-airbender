#pragma once
#include "placeholder.cuh"
#include "tables.cuh"

using namespace ::airbender::witness::placeholder;
using namespace ::airbender::witness::tables;

namespace airbender::witness::generation {

// #define PRINT_ENABLED
#define PRINT_THREAD_IDX 0

using namespace field;

struct wrapped_f {
  using innerType = bf;
  bf inner;

  static constexpr DEVICE_FORCEINLINE wrapped_f new_(const bf value) { return {bf::into_canonical(value)}; }

  static constexpr DEVICE_FORCEINLINE wrapped_f new_(const u32 value) { return {bf::into_canonical(bf(value))}; }

  template <typename T> static DEVICE_FORCEINLINE wrapped_f from(const T &value) { return wrapped_f(bf::into_canonical(bf(value.inner))); }

  static DEVICE_FORCEINLINE wrapped_f add(const wrapped_f &lhs, const wrapped_f &rhs) { return wrapped_f(bf::into_canonical(bf::add(lhs.inner, rhs.inner))); }

  static DEVICE_FORCEINLINE wrapped_f sub(const wrapped_f &lhs, const wrapped_f &rhs) { return wrapped_f(bf::into_canonical(bf::sub(lhs.inner, rhs.inner))); }

  static DEVICE_FORCEINLINE wrapped_f mul(const wrapped_f &lhs, const wrapped_f &rhs) { return wrapped_f(bf::into_canonical(bf::mul(lhs.inner, rhs.inner))); }

  static DEVICE_FORCEINLINE wrapped_f mul_add(const wrapped_f &mul_0, const wrapped_f &mul_1, const wrapped_f &add) {
    return wrapped_f(bf::into_canonical(bf::add(bf::mul(mul_0.inner, mul_1.inner), add.inner)));
  }

  static DEVICE_FORCEINLINE wrapped_f inv(const wrapped_f &value) { return wrapped_f(bf::into_canonical(bf::inv(value.inner))); }
};

struct wrapped_b {
  using innerType = bool;
  bool inner;

  static constexpr DEVICE_FORCEINLINE wrapped_b new_(const bool value) { return {value}; }

  template <typename T> static DEVICE_FORCEINLINE wrapped_b from(const T &value) { return wrapped_b(value.inner); }

  template <typename T> static DEVICE_FORCEINLINE wrapped_b from_integer_equality(const T &lhs, const T &rhs) { return wrapped_b{lhs.inner == rhs.inner}; }

  template <typename T> static DEVICE_FORCEINLINE wrapped_b from_integer_carry(const T &lhs, const T &rhs) { return wrapped_b{T::add_carry(lhs, rhs)}; }

  template <typename T> static DEVICE_FORCEINLINE wrapped_b from_integer_borrow(const T &lhs, const T &rhs) { return wrapped_b{T::sub_borrow(lhs, rhs)}; }

  static DEVICE_FORCEINLINE wrapped_b from_field_equality(const wrapped_f &lhs, const wrapped_f &rhs) {
    return wrapped_b{bf::into_canonical_u32(lhs.inner) == bf::into_canonical_u32(rhs.inner)};
  }

  static DEVICE_FORCEINLINE wrapped_b and_(const wrapped_b &lhs, const wrapped_b &rhs) { return wrapped_b{lhs.inner && rhs.inner}; }

  static DEVICE_FORCEINLINE wrapped_b or_(const wrapped_b &lhs, const wrapped_b &rhs) { return wrapped_b{lhs.inner || rhs.inner}; }

  template <typename T> static DEVICE_FORCEINLINE T select(const wrapped_b &selector, const T &if_true, const T &if_false) {
    return selector.inner ? if_true : if_false;
  }

  static DEVICE_FORCEINLINE wrapped_b negate(const wrapped_b &value) { return wrapped_b{!value.inner}; }
};

template <typename T> struct wrapped_integer {
  using innerType = T;
  T inner;

  static constexpr DEVICE_FORCEINLINE wrapped_integer new_(const T value) { return {value}; }

  template <typename U> static DEVICE_FORCEINLINE wrapped_integer from(const U &value) { return wrapped_integer{static_cast<T>(value.inner)}; }

  static DEVICE_FORCEINLINE wrapped_integer add(const wrapped_integer &lhs, const wrapped_integer &rhs) { return wrapped_integer(lhs.inner + rhs.inner); }

  static DEVICE_FORCEINLINE bool add_carry(const wrapped_integer &lhs, const wrapped_integer &rhs) { return ::add_carry(lhs.inner, rhs.inner).y; }

  static DEVICE_FORCEINLINE wrapped_integer sub(const wrapped_integer &lhs, const wrapped_integer &rhs) { return wrapped_integer(lhs.inner - rhs.inner); }

  static DEVICE_FORCEINLINE bool sub_borrow(const wrapped_integer &lhs, const wrapped_integer &rhs) { return ::sub_borrow(lhs.inner, rhs.inner).y; }

  static DEVICE_FORCEINLINE wrapped_integer mul(const wrapped_integer &lhs, const wrapped_integer &rhs) { return wrapped_integer(lhs.inner * rhs.inner); }

  static DEVICE_FORCEINLINE wrapped_integer mul_add(const wrapped_integer &mul_0, const wrapped_integer &mul_1, const wrapped_integer &add) {
    return wrapped_integer(mul_0.inner * mul_1.inner + add.inner);
  }

  static DEVICE_FORCEINLINE wrapped_integer shl(const wrapped_integer &value, const unsigned &shift) { return wrapped_integer(value.inner << shift); }

  static DEVICE_FORCEINLINE wrapped_integer shr(const wrapped_integer &value, const unsigned &shift) { return wrapped_integer(value.inner >> shift); }

  static DEVICE_FORCEINLINE wrapped_integer lowest_bits(const wrapped_integer &value, const unsigned &count) {
    return wrapped_integer(value.inner & (1u << count) - 1);
  }

  static DEVICE_FORCEINLINE wrapped_integer mul_low(const wrapped_integer &lhs, const wrapped_integer &rhs);

  static DEVICE_FORCEINLINE wrapped_integer mul_high(const wrapped_integer &lhs, const wrapped_integer &rhs);

  static DEVICE_FORCEINLINE wrapped_integer div(const wrapped_integer &lhs, const wrapped_integer &rhs) { return wrapped_integer(lhs.inner / rhs.inner); }

  static DEVICE_FORCEINLINE wrapped_integer rem(const wrapped_integer &lhs, const wrapped_integer &rhs) { return wrapped_integer(lhs.inner % rhs.inner); }

  template <typename U> static DEVICE_FORCEINLINE U signed_mul_low(const wrapped_integer &lhs, const wrapped_integer &rhs);

  template <typename U> static DEVICE_FORCEINLINE U signed_mul_high(const wrapped_integer &lhs, const wrapped_integer &rhs);

  template <typename U> static DEVICE_FORCEINLINE U mixed_mul_low(const wrapped_integer &lhs, const U &rhs);

  template <typename U> static DEVICE_FORCEINLINE U mixed_mul_high(const wrapped_integer &lhs, const U &rhs);
};

typedef wrapped_integer<u8> wrapped_u8;
typedef wrapped_integer<u16> wrapped_u16;
typedef wrapped_integer<u32> wrapped_u32;
typedef wrapped_integer<int32_t> wrapped_i32;

template <> DEVICE_FORCEINLINE wrapped_f wrapped_f::from(const wrapped_u32 &value) { return wrapped_f{bf::into_canonical(bf::from_u32(value.inner))}; }

template <> DEVICE_FORCEINLINE wrapped_b wrapped_b::from(const wrapped_f &value) {
  const u32 canonical = bf::into_canonical_u32(value.inner);
  return wrapped_b{static_cast<bool>(canonical)};
}

template <> template <> DEVICE_FORCEINLINE wrapped_u8 wrapped_u8::from(const wrapped_f &value) {
  const u32 canonical = bf::into_canonical_u32(value.inner);
  return wrapped_u8{static_cast<u8>(canonical)};
}

template <> template <> DEVICE_FORCEINLINE wrapped_u16 wrapped_u16::from(const wrapped_f &value) {
  const u32 canonical = bf::into_canonical_u32(value.inner);
  return wrapped_u16{static_cast<u16>(canonical)};
}

template <> template <> DEVICE_FORCEINLINE wrapped_u32 wrapped_u32::from(const wrapped_f &value) {
  const u32 canonical = bf::into_canonical_u32(value.inner);
  return wrapped_u32{canonical};
}

template <> template <> DEVICE_FORCEINLINE wrapped_i32 wrapped_i32::from(const wrapped_f &value) {
  const u32 canonical = bf::into_canonical_u32(value.inner);
  return wrapped_i32{static_cast<int32_t>(canonical)};
}

template <> DEVICE_FORCEINLINE wrapped_u8 wrapped_u8::mul_low(const wrapped_u8 &lhs, const wrapped_u8 &rhs) {
  const u16 result = static_cast<u16>(lhs.inner) * static_cast<u16>(rhs.inner);
  return wrapped_u8{static_cast<u8>(result)};
}

template <> DEVICE_FORCEINLINE wrapped_u16 wrapped_u16::mul_low(const wrapped_u16 &lhs, const wrapped_u16 &rhs) {
  const u32 result = static_cast<u32>(lhs.inner) * static_cast<u32>(rhs.inner);
  return wrapped_u16{static_cast<u8>(result)};
}

template <> DEVICE_FORCEINLINE wrapped_u32 wrapped_u32::mul_low(const wrapped_u32 &lhs, const wrapped_u32 &rhs) {
  const u64 result = static_cast<u64>(lhs.inner) * static_cast<u64>(rhs.inner);
  return wrapped_u32{static_cast<u32>(result)};
}

template <> DEVICE_FORCEINLINE wrapped_i32 wrapped_i32::mul_low(const wrapped_i32 &lhs, const wrapped_i32 &rhs) {
  const int64_t result = static_cast<int64_t>(lhs.inner) * static_cast<int64_t>(rhs.inner);
  return wrapped_i32{static_cast<int32_t>(result)};
}

template <> DEVICE_FORCEINLINE wrapped_u8 wrapped_u8::mul_high(const wrapped_u8 &lhs, const wrapped_u8 &rhs) {
  const u16 result = static_cast<u16>(lhs.inner) * static_cast<u16>(rhs.inner);
  return wrapped_u8{static_cast<u8>(result >> 8)};
}

template <> DEVICE_FORCEINLINE wrapped_u16 wrapped_u16::mul_high(const wrapped_u16 &lhs, const wrapped_u16 &rhs) {
  const u32 result = static_cast<u32>(lhs.inner) * static_cast<u32>(rhs.inner);
  return wrapped_u16{static_cast<u8>(result >> 16)};
}

template <> DEVICE_FORCEINLINE wrapped_u32 wrapped_u32::mul_high(const wrapped_u32 &lhs, const wrapped_u32 &rhs) {
  const u64 result = static_cast<u64>(lhs.inner) * static_cast<u64>(rhs.inner);
  return wrapped_u32{static_cast<u32>(result >> 32)};
}

template <> DEVICE_FORCEINLINE wrapped_i32 wrapped_i32::mul_high(const wrapped_i32 &lhs, const wrapped_i32 &rhs) {
  const int64_t result = static_cast<int64_t>(lhs.inner) * static_cast<int64_t>(rhs.inner);
  return wrapped_i32{static_cast<int32_t>(result >> 32)};
}

template <> template <> DEVICE_FORCEINLINE wrapped_u32 wrapped_i32::signed_mul_low(const wrapped_i32 &lhs, const wrapped_i32 &rhs) {
  const int64_t result = static_cast<int64_t>(lhs.inner) * static_cast<int64_t>(rhs.inner);
  return wrapped_u32{static_cast<u32>(static_cast<u64>(result))};
}

template <> template <> DEVICE_FORCEINLINE wrapped_u32 wrapped_i32::signed_mul_high(const wrapped_i32 &lhs, const wrapped_i32 &rhs) {
  const int64_t result = static_cast<int64_t>(lhs.inner) * static_cast<int64_t>(rhs.inner);
  return wrapped_u32{static_cast<u32>(static_cast<u64>(result) >> 32)};
}

template <> template <> DEVICE_FORCEINLINE wrapped_u32 wrapped_i32::mixed_mul_low(const wrapped_i32 &lhs, const wrapped_u32 &rhs) {
  const int64_t result = static_cast<int64_t>(lhs.inner) * static_cast<int64_t>(rhs.inner);
  return wrapped_u32{static_cast<u32>(static_cast<u64>(result))};
}

template <> template <> DEVICE_FORCEINLINE wrapped_u32 wrapped_i32::mixed_mul_high(const wrapped_i32 &lhs, const wrapped_u32 &rhs) {
  const int64_t result = static_cast<int64_t>(lhs.inner) * static_cast<int64_t>(rhs.inner);
  return wrapped_u32{static_cast<u32>(static_cast<u64>(result) >> 32)};
}

template <class R> struct WitnessProxy {
  const R oracle;
  const wrapped_f *const __restrict__ generic_lookup_tables;
  const wrapped_f *const __restrict__ memory;
  wrapped_f *const __restrict__ witness;
  u32 *const __restrict__ lookup_mappings;
  wrapped_f *const scratch;
  const unsigned stride;
  const unsigned offset;

  template <typename T> DEVICE_FORCEINLINE T get_memory_place(const unsigned idx) const {
    const auto value = memory[idx * stride + offset];
#ifdef PRINT_ENABLED
    if (offset == PRINT_THREAD_IDX)
      printf("M[%u] -> %u\n", idx, value.inner.limb);
#endif
    return T::from(value);
  }

  template <typename T> DEVICE_FORCEINLINE T get_witness_place(const unsigned idx) const {
    auto value = witness[idx * stride + offset];
#ifdef PRINT_ENABLED
    if (offset == PRINT_THREAD_IDX)
      printf("W[%u] -> %u\n", idx, value.inner.limb);
#endif
    return T::from(value);
  }

  template <typename T> DEVICE_FORCEINLINE T get_scratch_place(const unsigned idx) const {
    auto value = scratch[idx];
#ifdef PRINT_ENABLED
    if (offset == PRINT_THREAD_IDX)
      printf("S[%u] -> %u\n", idx, value.inner.limb);
#endif
    return T::from(value);
  }

  template <typename T> DEVICE_FORCEINLINE T get_oracle_value(const Placeholder placeholder) const {
    const auto value = oracle.template get_witness_from_placeholder<typename T::innerType>(placeholder, offset);
#ifdef PRINT_ENABLED
    if (offset == PRINT_THREAD_IDX)
      printf("O[%u] -> %u\n", placeholder.tag, static_cast<u32>(value));
#endif
    return T(value);
  }

  template <typename T> DEVICE_FORCEINLINE void set_memory_place(const unsigned idx, const T &value) const {
    auto f = wrapped_f::from(value);
#ifdef PRINT_ENABLED
    if (offset == PRINT_THREAD_IDX)
      printf("M[%u] <- %u\n", idx, f.inner.limb);
#endif
    memory[idx * stride + offset] = f;
  }

  template <typename T> DEVICE_FORCEINLINE void set_witness_place(const unsigned idx, const T &value) const {
    const auto f = wrapped_f::from(value);
#ifdef PRINT_ENABLED
    if (offset == PRINT_THREAD_IDX)
      printf("W[%u] <- %u\n", idx, f.inner.limb);
#endif
    witness[idx * stride + offset] = f;
  }

  template <typename T> DEVICE_FORCEINLINE void set_scratch_place(const unsigned idx, const T &value) const {
    auto f = wrapped_f::from(value);
#ifdef PRINT_ENABLED
    if (offset == PRINT_THREAD_IDX)
      printf("S[%u] <- %u\n", idx, f.inner.limb);
#endif
    scratch[idx] = f;
  }

  template <unsigned I, unsigned O>
  DEVICE_FORCEINLINE u32 get_lookup_index_and_value(const wrapped_f *inputs, const wrapped_u16 table_id, wrapped_f *outputs, const u32 *offsets) const {
    const auto tables = reinterpret_cast<const bf *>(generic_lookup_tables);
    const TableDriver<I, O> table_driver{
        tables,
        stride,
        offsets,
    };
    const auto table_type = static_cast<TableType>(table_id.inner);
    const auto keys = reinterpret_cast<const bf *>(inputs);
    const auto values = reinterpret_cast<bf *>(outputs);
    const u32 index = table_driver.get_index_and_set_values(table_type, keys, values);
#ifdef PRINT_ENABLED
    if (offset == PRINT_THREAD_IDX) {
      printf("L[%u] -> %u [", table_id.inner, index);
      for (unsigned i = 0; i < I; ++i)
        printf("%s%u", i == 0 ? "" : ", ", keys[i].limb);
      printf("] -> [");
      for (unsigned i = 0; i < O; ++i)
        printf("%s%u", i == 0 ? "" : ", ", values[i].limb);
      printf("]\n");
    }
#endif
    return index;
  }

  template <unsigned I, unsigned O>
  DEVICE_FORCEINLINE void lookup(const wrapped_f inputs[I], const wrapped_u16 table_id, wrapped_f outputs[O], const unsigned lookup_mapping_idx,
                                 const u32 *offsets) const {
    static_assert(I + O == 3);
    const u32 index = get_lookup_index_and_value<I, O>(inputs, table_id, outputs, offsets);
    lookup_mappings[lookup_mapping_idx * stride + offset] = index;
  }

  template <unsigned N>
  DEVICE_FORCEINLINE void lookup_enforce(const wrapped_f values[N], const wrapped_u16 table_id, const unsigned lookup_mapping_idx, const u32 *offsets) const {
    static_assert(N == 3);
    const u32 index = get_lookup_index_and_value<N, 0>(values, table_id, nullptr, offsets);
    lookup_mappings[lookup_mapping_idx * stride + offset] = index;
  }

  template <unsigned I, unsigned O>
  DEVICE_FORCEINLINE void maybe_lookup(const wrapped_f inputs[I], const wrapped_u16 table_id, const wrapped_b mask, wrapped_f outputs[O],
                                       const u32 *offsets) const {
    static_assert(I + O == 3);
    if (!mask.inner)
      return;
    get_lookup_index_and_value<I, O>(inputs, table_id, outputs, offsets);
  }
};

#define VAR(N) var_##N
#define CONSTANT(T, N, VALUE) constexpr wrapped_##T VAR(N) = wrapped_##T::new_(VALUE);
#define GET_MEMORY_PLACE(T, N, IDX) const wrapped_##T VAR(N) = p.template get_memory_place<wrapped_##T>(IDX);
#define GET_WITNESS_PLACE(T, N, IDX) const wrapped_##T VAR(N) = p.template get_witness_place<wrapped_##T>(IDX);
#define GET_SCRATCH_PLACE(T, N, IDX) const wrapped_##T VAR(N) = p.template get_scratch_place<wrapped_##T>(IDX);
#define GET_ORACLE_VALUE(T, N, P) const wrapped_##T VAR(N) = p.template get_oracle_value<wrapped_##T>(P);
#define LOOKUP_TABLE_OFFSETS(...) static constexpr __device__ u32 lookup_table_offsets[] = {__VA_ARGS__};
#define LOOKUP_OUTPUTS(N, NO) wrapped_f VAR(N)[NO] = {};
#define LOOKUP(N, NI, NO, TID, LMI, ...)                                                                                                                       \
  LOOKUP_OUTPUTS(N, NO) {                                                                                                                                      \
    wrapped_f inputs[] = {__VA_ARGS__};                                                                                                                        \
    p.template lookup<NI, NO>(inputs, VAR(TID), VAR(N), LMI, lookup_table_offsets);                                                                            \
  }
#define LOOKUP_ENFORCE(NI, TID, LMI, ...)                                                                                                                      \
  {                                                                                                                                                            \
    wrapped_f inputs[] = {__VA_ARGS__};                                                                                                                        \
    p.template lookup_enforce<NI>(inputs, VAR(TID), LMI, lookup_table_offsets);                                                                                \
  }
#define MAYBE_LOOKUP(N, NI, NO, TID, M, ...)                                                                                                                   \
  LOOKUP_OUTPUTS(N, NO) {                                                                                                                                      \
    wrapped_f inputs[] = {__VA_ARGS__};                                                                                                                        \
    p.template maybe_lookup<NI, NO>(inputs, VAR(TID), VAR(M), VAR(N), lookup_table_offsets);                                                                   \
  }
#define ACCESS_LOOKUP(N, O, IDX) const wrapped_f VAR(N) = VAR(O)[IDX];
#define FROM(T, N, I) const wrapped_##T VAR(N) = wrapped_##T::from(VAR(I));
#define B_FROM_INTEGER_EQUALITY(N, LHS, RHS) const wrapped_b VAR(N) = wrapped_b::from_integer_equality(VAR(LHS), VAR(RHS));
#define B_FROM_INTEGER_CARRY(N, LHS, RHS) const wrapped_b VAR(N) = wrapped_b::from_integer_carry(VAR(LHS), VAR(RHS));
#define B_FROM_INTEGER_BORROW(N, LHS, RHS) const wrapped_b VAR(N) = wrapped_b::from_integer_borrow(VAR(LHS), VAR(RHS));
#define B_FROM_FIELD_EQUALITY(N, LHS, RHS) const wrapped_b VAR(N) = wrapped_b::from_field_equality(VAR(LHS), VAR(RHS));
#define AND(N, LHS, RHS) const wrapped_b VAR(N) = wrapped_b::and_(VAR(LHS), VAR(RHS));
#define OR(N, LHS, RHS) const wrapped_b VAR(N) = wrapped_b::or_(VAR(LHS), VAR(RHS));
#define SELECT(T, N, S, TRUE, FALSE) const wrapped_##T VAR(N) = wrapped_b::select(VAR(S), VAR(TRUE), VAR(FALSE));
#define SELECT_VAR(S, TRUE, FALSE) wrapped_b::select(VAR(S), VAR(TRUE), VAR(FALSE))
#define NEGATE(N, I) const wrapped_b VAR(N) = wrapped_b::negate(VAR(I));
#define ADD(T, N, LHS, RHS) const wrapped_##T VAR(N) = wrapped_##T::add(VAR(LHS), VAR(RHS));
#define SUB(T, N, LHS, RHS) const wrapped_##T VAR(N) = wrapped_##T::sub(VAR(LHS), VAR(RHS));
#define MUL(T, N, LHS, RHS) const wrapped_##T VAR(N) = wrapped_##T::mul(VAR(LHS), VAR(RHS));
#define MUL_ADD(T, N, M0, M1, A) const wrapped_##T VAR(N) = wrapped_##T::mul_add(VAR(M0), VAR(M1), VAR(A));
#define INV(T, N, I) const wrapped_##T VAR(N) = wrapped_##T::inv(VAR(I));
#define SHL(T, N, I, M) const wrapped_##T VAR(N) = wrapped_##T::shl(VAR(I), M);
#define SHR(T, N, I, M) const wrapped_##T VAR(N) = wrapped_##T::shr(VAR(I), M);
#define LOWEST_BITS(T, N, I, M) const wrapped_##T VAR(N) = wrapped_##T::lowest_bits(VAR(I), M);
#define MUL_LOW(T, N, LHS, RHS) const wrapped_##T VAR(N) = wrapped_##T::mul_low(VAR(LHS), VAR(RHS));
#define MUL_HIGH(T, N, LHS, RHS) const wrapped_##T VAR(N) = wrapped_##T::mul_high(VAR(LHS), VAR(RHS));
#define DIV(T, N, LHS, RHS) const wrapped_##T VAR(N) = wrapped_##T::div(VAR(LHS), VAR(RHS));
#define REM(T, N, LHS, RHS) const wrapped_##T VAR(N) = wrapped_##T::rem(VAR(LHS), VAR(RHS));
#define SIGNED_MUL_LOW(N, LHS, RHS) const wrapped_u32 VAR(N) = wrapped_i32::signed_mul_low<wrapped_u32>(VAR(LHS), VAR(RHS));
#define SIGNED_MUL_HIGH(N, LHS, RHS) const wrapped_u32 VAR(N) = wrapped_i32::signed_mul_high<wrapped_u32>(VAR(LHS), VAR(RHS));
#define MIXED_MUL_LOW(N, LHS, RHS) const wrapped_u32 VAR(N) = wrapped_i32::mixed_mul_low<wrapped_u32>(VAR(LHS), VAR(RHS));
#define MIXED_MUL_HIGH(N, LHS, RHS) const wrapped_u32 VAR(N) = wrapped_i32::mixed_mul_high<wrapped_u32>(VAR(LHS), VAR(RHS));
#define IF(S, T)                                                                                                                                               \
  if (VAR(S).inner) {                                                                                                                                          \
    T                                                                                                                                                          \
  }
#define SET_MEMORY_PLACE(IDX, V) p.template set_memory_place(IDX, VAR(V));
#define SET_WITNESS_PLACE(IDX, V) p.template set_witness_place(IDX, VAR(V));
#define SET_SCRATCH_PLACE(IDX, V) p.set_scratch_place(IDX, VAR(V));

#define FN_BEGIN(N) template <class R> DEVICE_FORCEINLINE void fn_##N(const WitnessProxy<R> p) {
#define FN_END }

#define FN_CALL(N) fn_##N(p);

// clang-format off
#define INCLUDE_PREFIX ../../../../circuit_defs/ // whitespace! NOLINT
#define INCLUDE_SUFFIX /generated/witness_generation_fn.cuh
// clang-format on
#define STRINGIFY(X) STRINGIFY2(X)
#define STRINGIFY2(X) #X
#define IDENT(x) x
#define CAT_3(x, y, z) IDENT(x) IDENT(y) IDENT(z)
#define CIRCUIT_INCLUDE(NAME) STRINGIFY(CAT_3(INCLUDE_PREFIX, NAME, INCLUDE_SUFFIX))
#define KERNEL_NAME(NAME) ab_generate_##NAME##_witness_kernel
#define KERNEL(NAME, ORACLE)                                                                                                                                   \
  EXTERN __global__ void KERNEL_NAME(NAME)(const __grid_constant__ ORACLE oracle, const wrapped_f *const __restrict__ generic_lookup_tables,                   \
                                           const wrapped_f *const __restrict__ memory, wrapped_f *const __restrict__ witness,                                  \
                                           u32 *const __restrict__ lookup_mappings, const unsigned stride, const unsigned count) {                             \
    const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;                                                                                                \
    if (gid >= count)                                                                                                                                          \
      return;                                                                                                                                                  \
    SCRATCH                                                                                                                                                    \
    const WitnessProxy<ORACLE> p = {oracle, generic_lookup_tables, memory, witness, lookup_mappings, scratch, stride, gid};                                    \
    FN_CALL(generate)                                                                                                                                          \
  }

} // namespace airbender::witness::generation