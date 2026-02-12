#include "field.cuh"

using namespace ::airbender::field;

namespace airbender::monolith {

typedef base_field bf;

constexpr unsigned WARP_SIZE = 32;
constexpr unsigned CAPACITY = 8;
constexpr unsigned RATE = 8;
constexpr unsigned WIDTH = CAPACITY + RATE;
constexpr unsigned NUM_ROUNDS = 6;
constexpr unsigned NUM_FULL_ROUNDS = NUM_ROUNDS - 1;
constexpr unsigned NUM_BARS = 8;

__constant__ constexpr uint32_t ROUND_CONSTANTS[NUM_FULL_ROUNDS][WIDTH] = {
    {1821280327, 1805192324, 127749067, 534494027, 504066389, 661859220, 1964605566, 11087311, 1178584041, 412585466, 2078905810, 549234502, 1181028407,
     363220519, 1649192353, 895839514},
    {939676630, 132824540, 1081150345, 1901266162, 1248854474, 722216947, 711899879, 991065584, 872971327, 1747874412, 889258434, 857014393, 1145792277,
     329607215, 1069482641, 1809464251},
    {1792923486, 1071073386, 2086334655, 615259270, 1680936759, 2069228098, 679754665, 598972355, 1448263353, 2102254560, 1676515281, 1529495635, 981915006,
     436108429, 1959227325, 1710180674},
    {814766386, 746021429, 758709057, 1777861169, 1875425297, 1630916709, 180204592, 1301124329, 307222363, 297236795, 866482358, 1784330946, 1841790988,
     1855089478, 2122902104, 1522878966},
    {1132611924, 1823267038, 539457094, 934064219, 561891167, 1325624939, 1683493283, 1582152536, 851185378, 1187215684, 1520269176, 801897118, 741765053,
     1300119213, 1960664069, 1633755961},
};

//__constant__ constexpr uint32_t MDS_MATRIX[WIDTH] = {2097152, 2, 1, 1, 131072, 1, 2, 512, 16, 1, 32768, 4, 2048, 8, 32, 3};

__constant__ constexpr unsigned MDS_MATRIX_INDEXES[WIDTH + 1] = {0, 4, 10, 12, 7, 14, 8, 13, 11, 1, 6, 15, 2, 3, 5, 9, 15};

__constant__ constexpr unsigned MDS_MATRIX_SHIFTS[WIDTH + 1] = {4, 2, 4, 2, 4, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0};

__shared__ uint8_t bar_lookup[(1u << 8) + (1u << 7)];

DEVICE_FORCEINLINE uint8_t rotl_8(const uint8_t x, const unsigned shift) { return x << shift | x >> (8 - shift); }

DEVICE_FORCEINLINE uint8_t rotl_7(const uint8_t x, const unsigned shift) { return (x << shift | x >> (7 - shift)) & 0x7F; }

DEVICE_FORCEINLINE uint8_t s_box_8(const uint8_t x) { return rotl_8(x ^ ~rotl_8(x, 1) & rotl_8(x, 2) & rotl_8(x, 3), 1); }

DEVICE_FORCEINLINE uint8_t s_box_7(const uint8_t x) { return rotl_7(x ^ ~rotl_7(x, 1) & rotl_7(x, 2), 1); }

DEVICE_FORCEINLINE void initialize_lookup(const unsigned tid, const unsigned block_size) {
  for (unsigned i = tid; i < 1u << 8; i += block_size)
    bar_lookup[i] = s_box_8(i);
  for (unsigned i = tid; i < 1u << 7; i += block_size)
    bar_lookup[(1u << 8) + i] = s_box_7(i);
  __syncthreads();
}

// DEVICE_FORCEINLINE uint32_t bar(const uint32_t limb) {
//   const uint32_t limb_l1 = (~limb & 0x40000000) >> 6 | (~limb & 0x808080) >> 7 | (~limb & 0x3F7F7F7F) << 1; // Left rotation by 1
//   const uint32_t limb_l2 = (limb & 0x60000000) >> 5 | (limb & 0xC0C0C0) >> 6 | (limb & 0x1F3F3F3F) << 2;    // Left rotation by 2
//   const uint32_t limb_l3 = 0xFF000000 | (limb & 0xE0E0E0) >> 5 | (limb & 0x1F1F1F) << 3;                    // Left rotation by 3
//   const uint32_t tmp = limb ^ limb_l1 & limb_l2 & limb_l3;
//   return (tmp & 0x40000000) >> 6 | (tmp & 0x808080) >> 7 | (tmp & 0x3F7F7F7F) << 1; // Final rotation
// }

// DEVICE_FORCEINLINE uint32_t bar(uint32_t limb) {
//     auto bytes = reinterpret_cast<uint8_t *>(&limb);
//     bytes[0] = s_box_8(bytes[0]);
//     bytes[1] = s_box_8(bytes[1]);
//     bytes[2] = s_box_8(bytes[2]);
//     bytes[3] = s_box_7(bytes[3]);
//     return limb;
// }

// DEVICE_FORCEINLINE uint32_t bar(uint32_t limb) {
//       uint32_t result;
//       const auto l = reinterpret_cast<uint8_t *>(&limb);
//       const auto r = reinterpret_cast<uint8_t *>(&result);
//       r[0] = bar_lookup_8[l[0]];
//       r[1] = bar_lookup_8[l[1]];
//       r[2] = bar_lookup_8[l[2]];
//       r[3] = bar_lookup_7[l[3]];
//       return result;
// }

DEVICE_FORCEINLINE void print_state(const bf state[WIDTH]) {
  // #pragma unroll
  //   for (unsigned i = 0; i < WIDTH; i++)
  //     printf("%d ", state[i].limb);
  //   printf("\n");
}

DEVICE_FORCEINLINE uint32_t bar(uint32_t limb) {
  // WARNING: This code relies on the fact that bar_lookup structure is
  // the first structure in the shared memory and therefore having address 0
  uint32_t result;
  asm("{\n"
      ".reg .u32 r<13>;\n"
      "and.b32 r0, %1, 255;\n"
      "shr.u32 r1, %1, 8;\n"
      "and.b32 r2, r1, 255;\n"
      "shr.u32 r3, %1, 16;\n"
      "and.b32 r4, r3, 255;\n"
      "shr.u32 r5, %1, 24;\n"
      "add.s32 r6, 256, r5;\n"
      "ld.shared.u8 r10, [r6];\n"
      "ld.shared.u8 r9, [r4];\n"
      "ld.shared.u8 r8, [r2];\n"
      "ld.shared.u8 r7, [r0];\n"
      "prmt.b32 r11, r8, r7, 30212;\n"
      "prmt.b32 r12, r9, r11, 28756;\n"
      "prmt.b32 %0, r10, r12, 1620;\n"
      "}"
      : "=r"(result)
      : "r"(limb));
  return result;
}

DEVICE_FORCEINLINE void bars_st(bf state[WIDTH]) {
#pragma unroll
  for (unsigned i = 0; i < NUM_BARS; i++)
    state[i] = bf(bar(state[i].limb));
}

DEVICE_FORCEINLINE void bars_mt(bf &state, const unsigned tid) {
  if (tid < NUM_BARS)
    state = bf(bar(state.limb));
}

DEVICE_FORCEINLINE void bricks_st(bf state[WIDTH]) {
#pragma unroll
  for (unsigned i = WIDTH - 1; i > 0; i--)
    state[i] = bf::add(state[i], bf::sqr(state[i - 1]));
}

DEVICE_FORCEINLINE void bricks_mt(bf &state, const unsigned tid) {
  const uint32_t previous = __shfl_up_sync(0xFFFFFFFF, state.limb, 1, WIDTH);
  if (tid)
    state = bf::add(state, bf::sqr(bf(previous)));
}

template <unsigned ROUND> DEVICE_FORCEINLINE void concrete_shl_st(bf state[WIDTH]) {
  bf result[WIDTH];
#pragma unroll
  for (unsigned row = 0; row < WIDTH; row++) {
    uint64_t acc = 0;
#pragma unroll
    for (unsigned i = 0; i < WIDTH + 1; i++) {
      const unsigned index = MDS_MATRIX_INDEXES[i];
      const unsigned col = (index + row) % WIDTH;
      const uint32_t value = state[col].limb;
      acc = i ? acc + value : value;
      if (const unsigned shift = MDS_MATRIX_SHIFTS[i])
        acc <<= shift;
    }
    acc <<= 2; // multiply by 4 for compatibility with the FFT variant
    if (ROUND != 0 && ROUND < NUM_ROUNDS)
      acc += ROUND_CONSTANTS[ROUND - 1][row];
    result[row] = bf::from_u62_max_minus_one(acc);
  }
#pragma unroll
  for (unsigned i = 0; i < WIDTH; i++)
    state[i] = result[i];
}

template <unsigned ROUND> DEVICE_FORCEINLINE void concrete_shl_mt(bf &state, const unsigned tid) {
  uint64_t acc = 0;
#pragma unroll
  for (unsigned i = 0; i < WIDTH + 1; i++) {
    const unsigned index = MDS_MATRIX_INDEXES[i];
    const int src_lane = static_cast<int>(index + tid);
    const uint32_t value = __shfl_sync(0xFFFFFFFF, state.limb, src_lane, WIDTH);
    acc = i ? acc + value : value;
    if (const unsigned shift = MDS_MATRIX_SHIFTS[i])
      acc <<= shift;
  }
  acc <<= 2; // multiply by 4 for compatibility with the FFT variant
  if (ROUND != 0 && ROUND < NUM_ROUNDS)
    acc += ROUND_CONSTANTS[ROUND - 1][tid];
  state = bf::from_u62_max_minus_one(acc);
}

template <unsigned ROUND> DEVICE_FORCEINLINE void concrete_st(bf state[WIDTH]) { concrete_shl_st<ROUND>(state); }

template <unsigned ROUND> DEVICE_FORCEINLINE void concrete_mt(bf &state, const unsigned tid) { concrete_shl_mt<ROUND>(state, tid); }

template <unsigned ROUND> DEVICE_FORCEINLINE void round_st(bf state[WIDTH]) {
  if (ROUND != 0) {
    bars_st(state);
    print_state(state);
    bricks_st(state);
    print_state(state);
  }
  concrete_st<ROUND>(state);
  print_state(state);
}

template <unsigned ROUND> DEVICE_FORCEINLINE void round_mt(bf &state, const unsigned tid) {
  if (ROUND != 0) {
    bars_mt(state, tid);
    bricks_mt(state, tid);
  }
  concrete_mt<ROUND>(state, tid);
}

DEVICE_FORCEINLINE void permutation_st(bf state[WIDTH]) {
  static_assert(NUM_ROUNDS == 6);
  round_st<0>(state);
  round_st<1>(state);
  round_st<2>(state);
  round_st<3>(state);
  round_st<4>(state);
  round_st<5>(state);
  round_st<6>(state);
}

DEVICE_FORCEINLINE void permutation_mt(bf &state, const unsigned tid) {
  static_assert(NUM_ROUNDS == 6);
  round_mt<0>(state, tid);
  round_mt<1>(state, tid);
  round_mt<2>(state, tid);
  round_mt<3>(state, tid);
  round_mt<4>(state, tid);
  round_mt<5>(state, tid);
  round_mt<6>(state, tid);
}

EXTERN __launch_bounds__(128, 7) __global__
    void ab_monolith_leaves_st_kernel(const bf *values, bf *results, const unsigned log_rows_count, const unsigned cols_count, const unsigned count) {
  static_assert(CAPACITY + RATE == WIDTH);
  const unsigned gid = threadIdx.x + blockIdx.x * blockDim.x;
  initialize_lookup(threadIdx.x, blockDim.x);
  if (gid >= count)
    return;
  values += gid << log_rows_count;
  results += gid * CAPACITY;
  const unsigned row_mask = (1u << log_rows_count) - 1;
  auto read = [=](const unsigned offset) {
    const unsigned row = offset & row_mask;
    const unsigned col = offset >> log_rows_count;
    return col < cols_count ? load_cs(values + row + ((col * count) << log_rows_count)) : bf::zero();
  };
  bf state[WIDTH];
  unsigned offset = 0;
#pragma unroll
  for (unsigned i = 0; i < WIDTH; i++, offset++)
    state[i] = read(offset);
  permutation_st(state);
  while (offset < cols_count << log_rows_count) {
#pragma unroll
    for (unsigned i = 0; i < RATE; i++, offset++)
      state[i + CAPACITY] = read(offset);
    permutation_st(state);
  }
#pragma unroll
  for (unsigned i = 0; i < CAPACITY; i++)
    store_cs(&results[i], state[i]);
}

EXTERN __launch_bounds__(128, 9) __global__
    void ab_monolith_leaves_mt_kernel(const bf *values, bf *results, const unsigned log_rows_count, const unsigned cols_count, const unsigned count) {
  static_assert(CAPACITY + RATE == WIDTH);
  static_assert(WARP_SIZE % WIDTH == 0);
  const unsigned gid = threadIdx.y + blockIdx.x * blockDim.y;
  initialize_lookup(threadIdx.x + threadIdx.y * blockDim.x, blockDim.x * blockDim.y);
  if (gid >= count)
    return;
  const unsigned tid = threadIdx.x;
  values += gid << log_rows_count;
  results += gid * CAPACITY + tid;
  const unsigned row_mask = (1u << log_rows_count) - 1;
  auto read = [=](const unsigned offset) {
    const unsigned row = offset & row_mask;
    const unsigned col = offset >> log_rows_count;
    return col < cols_count ? load_cs(values + row + ((col * count) << log_rows_count)) : bf::zero();
  };
  bf state = read(tid);
  permutation_mt(state, tid);
  for (unsigned offset = WIDTH; offset < (cols_count << log_rows_count); offset += RATE) {
    if (tid >= CAPACITY)
      state = read(offset + tid - CAPACITY);
    permutation_mt(state, tid);
  }
  if (tid < CAPACITY)
    store_cs(results, state);
}

EXTERN __launch_bounds__(128, 7) __global__ void ab_monolith_nodes_st_kernel(const bf *values, bf *results, const unsigned count) {
  static_assert(CAPACITY == RATE);
  static_assert(CAPACITY + RATE == WIDTH);
  const unsigned gid = threadIdx.x + blockIdx.x * blockDim.x;
  initialize_lookup(threadIdx.x, blockDim.x);
  if (gid >= count)
    return;
  values += gid * WIDTH;
  results += gid * CAPACITY;
  bf state[WIDTH];
#pragma unroll
  for (unsigned i = 0; i < WIDTH; i++, values++)
    state[i] = load_cs(values);
  permutation_st(state);
#pragma unroll
  for (unsigned i = 0; i < CAPACITY; i++)
    store_cs(&results[i], state[i]);
}

EXTERN __launch_bounds__(128, 10) __global__ void ab_monolith_nodes_mt_kernel(const bf *values, bf *results, const unsigned count) {
  static_assert(CAPACITY == RATE);
  static_assert(CAPACITY + RATE == WIDTH);
  static_assert(WARP_SIZE % WIDTH == 0);
  const unsigned gid = threadIdx.y + blockIdx.x * blockDim.y;
  initialize_lookup(threadIdx.x + threadIdx.y * blockDim.x, blockDim.x * blockDim.y);
  if (gid >= count)
    return;
  const unsigned tid = threadIdx.x;
  bf state = load_cs(values + gid * WIDTH + tid);
  permutation_mt(state, tid);
  if (tid < CAPACITY)
    store_cs(results + gid * CAPACITY + tid, state);
}

EXTERN __global__ void ab_gather_rows_kernel(const unsigned *indexes, const unsigned indexes_count, const matrix_getter<bf, ld_modifier::cs> values,
                                             const matrix_setter<bf, st_modifier::cs> results) {
  const unsigned idx = threadIdx.y + blockIdx.x * blockDim.y;
  if (idx >= indexes_count)
    return;
  const unsigned index = indexes[idx];
  const unsigned src_row = index * blockDim.x + threadIdx.x;
  const unsigned dst_row = idx * blockDim.x + threadIdx.x;
  const unsigned col = blockIdx.y;
  results.set(dst_row, col, values.get(src_row, col));
}

EXTERN __global__ void ab_gather_merkle_paths_kernel(const unsigned *indexes, const unsigned indexes_count, const bf *values, const unsigned log_leaves_count,
                                                     bf *results) {
  const unsigned idx = threadIdx.y + blockIdx.x * blockDim.y;
  if (idx >= indexes_count)
    return;
  const unsigned leaf_index = indexes[idx];
  const unsigned layer_index = blockIdx.y;
  const unsigned layer_offset = ((1u << log_leaves_count + 1) - (1u << log_leaves_count + 1 - layer_index)) * CAPACITY;
  const unsigned hash_offset = (leaf_index >> layer_index ^ 1) * CAPACITY;
  const unsigned element_offset = threadIdx.x;
  const unsigned src_index = layer_offset + hash_offset + element_offset;
  const unsigned dst_index = layer_index * indexes_count * CAPACITY + idx * CAPACITY + element_offset;
  results[dst_index] = values[src_index];
}

// #include "cuda/std/array"
// template <size_t S> using bfa = cuda::std::array<bf, S>;
// typedef __align__(16) bfa<RATE> digest_t;
// #include "cuda/std/tuple"
//
// template <class T, size_t S> using a = cuda::std::array<T, S>;
// template <class... T> using t = cuda::std::tuple<T...>;
//
// using u64 = uint64_t;
// using i64 = int64_t;
//__constant__ constexpr a<i64, 4> MDS_FREQ_BLOCK_ONE = {2230288, 520, 32803, 12};
//__constant__ constexpr a<t<i64, i64>, 4> MDS_FREQ_BLOCK_TWO = {t<i64, i64>{4194272, 258048}, {-1018, -6}, {60, -65534}, {14, 2}};
//__constant__ constexpr a<i64, 4> MDS_FREQ_BLOCK_THREE = {1964048, 510, -32735, 6};
//
//// using u64 = bf;
//// using i64 = bf;
////__constant__ constexpr a<i64, 4> MDS_FREQ_BLOCK_ONE = {i64(2230288), i64(520), i64(32803), i64(12)};
////__constant__ constexpr a<t<i64, i64>, 4> MDS_FREQ_BLOCK_TWO = {t<i64, i64>{i64(4194272), i64(258048)}, {i64(i64::ORDER-1018), i64(i64::ORDER-6)}, {i64(60),
//// i64(i64::ORDER-65534)}, {i64(14), i64 (2)}};
////__constant__ constexpr a<i64, 4> MDS_FREQ_BLOCK_THREE = {i64(1964048), i64(510), i64(i64::ORDER-32735), i64(6)};
//
//// 16 muls
//// 12 adds
// DEVICE_FORCEINLINE a<i64, 4> block1(const a<i64, 4> x) {
//   constexpr a<i64, 4> y = MDS_FREQ_BLOCK_ONE;
//   const auto [x0, x1, x2, x3] = x;
//   const auto [y0, y1, y2, y3] = y;
//   const i64 z0 = x0 * y0 + x1 * y3 + x2 * y2 + x3 * y1;
//   const i64 z1 = x0 * y1 + x1 * y0 + x2 * y3 + x3 * y2;
//   const i64 z2 = x0 * y2 + x1 * y1 + x2 * y0 + x3 * y3;
//   const i64 z3 = x0 * y3 + x1 * y2 + x2 * y1 + x3 * y0;
//   return {z0, z1, z2, z3};
// }
//
//// 48 muls
//// 91 adds
// DEVICE_FORCEINLINE a<t<i64, i64>, 4> block2(const a<t<i64, i64>, 4> x) {
//   constexpr a<t<i64, i64>, 4> y = MDS_FREQ_BLOCK_TWO;
//   const auto [x0, x1, x2, x3] = x;
//   const auto [y0, y1, y2, y3] = y;
//   const auto [x0r, x0i] = x0;
//   const auto [x1r, x1i] = x1;
//   const auto [x2r, x2i] = x2;
//   const auto [x3r, x3i] = x3;
//   const auto [y0r, y0i] = y0;
//   const auto [y1r, y1i] = y1;
//   const auto [y2r, y2i] = y2;
//   const auto [y3r, y3i] = y3;
//
//   const i64 x0s = x0r + x0i;
//   const i64 x1s = x1r + x1i;
//   const i64 x2s = x2r + x2i;
//   const i64 x3s = x3r + x3i;
//   const i64 y0s = y0r + y0i;
//   const i64 y1s = y1r + y1i;
//   const i64 y2s = y2r + y2i;
//   const i64 y3s = y3r + y3i;
//
//   i64 m0r, m0i, m1r, m1i, m2r, m2i, m3r, m3i;
//
//   // Compute x0​y0 ​− ix1​y3​ − ix2​y2 - ix3y1​ using Karatsuba for complex numbers multiplication
//   m0r = x0r * y0r;
//   m0i = x0i * y0i;
//   m1r = x1r * y3r;
//   m1i = x1i * y3i;
//   m2r = x2r * y2r;
//   m2i = x2i * y2i;
//   m3r = x3r * y1r;
//   m3i = x3i * y1i;
//   const i64 z0r = (m0r - m0i) + (x1s * y3s - m1r - m1i) + (x2s * y2s - m2r - m2i) + (x3s * y1s - m3r - m3i);
//   const i64 z0i = (x0s * y0s - m0r - m0i) + (-m1r + m1i) + (-m2r + m2i) + (-m3r + m3i);
//   const t<i64, i64> z0 = {z0r, z0i};
//
//   // Compute x0​y1​ + x1​y0​ − ix2​y3 - ix3y2 using Karatsuba for complex numbers multiplication
//   m0r = x0r * y1r;
//   m0i = x0i * y1i;
//   m1r = x1r * y0r;
//   m1i = x1i * y0i;
//   m2r = x2r * y3r;
//   m2i = x2i * y3i;
//   m3r = x3r * y2r;
//   m3i = x3i * y2i;
//   const i64 z1r = (m0r - m0i) + (m1r - m1i) + (x2s * y3s - m2r - m2i) + (x3s * y2s - m3r - m3i);
//   const i64 z1i = (x0s * y1s - m0r - m0i) + (x1s * y0s - m1r - m1i) + (-m2r + m2i) + (-m3r + m3i);
//   const t<i64, i64> z1 = {z1r, z1i};
//
//   // Compute x0​y2​ + x1​y1 ​+ x2​y0 - ix3y3​ using Karatsuba for complex numbers multiplication
//   m0r = x0r * y2r;
//   m0i = x0i * y2i;
//   m1r = x1r * y1r;
//   m1i = x1i * y1i;
//   m2r = x2r * y0r;
//   m2i = x2i * y0i;
//   m3r = x3r * y3r;
//   m3i = x3i * y3i;
//   const i64 z2r = (m0r - m0i) + (m1r - m1i) + (m2r - m2i) + (x3s * y3s - m3r - m3i);
//   const i64 z2i = (x0s * y2s - m0r - m0i) + (x1s * y1s - m1r - m1i) + (x2s * y0s - m2r - m2i) + (-m3r + m3i);
//   const t<i64, i64> z2 = {z2r, z2i};
//
//   // Compute x0​y3​ + x1​y2 ​+ x2​y1 + x3y0​ using Karatsuba for complex numbers multiplication
//   m0r = x0r * y3r;
//   m0i = x0i * y3i;
//   m1r = x1r * y2r;
//   m1i = x1i * y2i;
//   m2r = x2r * y1r;
//   m2i = x2i * y1i;
//   m3r = x3r * y0r;
//   m3i = x3i * y0i;
//   const i64 z3r = (m0r - m0i) + (m1r - m1i) + (m2r - m2i) + (m3r - m3i);
//   const i64 z3i = (x0s * y3s - m0r - m0i) + (x1s * y2s - m1r - m1i) + (x2s * y1s - m2r - m2i) + (x3s * y0s - m3r - m3i);
//   const t<i64, i64> z3 = {z3r, z3i};
//
//   return {z0, z1, z2, z3};
// }
//
//// 16 muls
//// 12 adds
// DEVICE_FORCEINLINE a<i64, 4> block3(const a<i64, 4> x) {
//   constexpr a<i64, 4> y = MDS_FREQ_BLOCK_THREE;
//   const auto [x0, x1, x2, x3] = x;
//   const auto [y0, y1, y2, y3] = y;
//   const i64 z0 = x0 * y0 - x1 * y3 - x2 * y2 - x3 * y1;
//   const i64 z1 = x0 * y1 + x1 * y0 - x2 * y3 - x3 * y2;
//   const i64 z2 = x0 * y2 + x1 * y1 + x2 * y0 - x3 * y3;
//   const i64 z3 = x0 * y3 + x1 * y2 + x2 * y1 + x3 * y0;
//   return {z0, z1, z2, z3};
// }
//
//// 2 adds
// DEVICE_FORCEINLINE a<i64, 2> fft2_real(const a<u64, 2> x) { return {i64(x[0]) + i64(x[1]), i64(x[0]) - i64(x[1])}; }
//
//// 2 adds
// DEVICE_FORCEINLINE a<u64, 2> ifft2_real_unreduced(const a<i64, 2> y) { return {u64(y[0] + y[1]), u64(y[0] - y[1])}; }
//
//// 7 adds
// DEVICE_FORCEINLINE t<i64, t<i64, i64>, i64> fft4_real(const a<u64, 4> x) {
//   const auto [z0, z2] = fft2_real({x[0], x[2]});
//   const auto [z1, z3] = fft2_real({x[1], x[3]});
//   const i64 y0 = z0 + z1;
//   const t<i64, i64> y1 = {z2, -z3};
//   const i64 y2 = z0 - z1;
//   return {y0, y1, y2};
// }
//
//// 7 adds
// DEVICE_FORCEINLINE a<u64, 4> ifft4_real_unreduced(const t<i64, t<i64, i64>, i64> y) {
//   const auto [y0, y1, y2] = y;
//   const i64 z0 = y0 + y2;
//   const i64 z1 = y0 - y2;
//   const auto [y10, y11] = y1;
//   const i64 z2 = y10;
//   const i64 z3 = -y11;
//   const auto [x0, x2] = ifft2_real_unreduced({z0, z2});
//   const auto [x1, x3] = ifft2_real_unreduced({z1, z3});
//   return {x0, x1, x2, x3};
// }
//
//// 80 muls
//// 171 adds
// DEVICE_FORCEINLINE a<u64, 16> mds_multiply_freq(const a<u64, 16> state) {
//   const auto [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15] = state;
//
//   const auto [u0, u1, u2] = fft4_real({s0, s4, s8, s12});     // 7 adds
//   const auto [u4, u5, u6] = fft4_real({s1, s5, s9, s13});     // 7 adds
//   const auto [u8, u9, u10] = fft4_real({s2, s6, s10, s14});   // 7 adds
//   const auto [u12, u13, u14] = fft4_real({s3, s7, s11, s15}); // 7 adds
//
//   const auto [v0, v4, v8, v12] = block1({u0, u4, u8, u12});   // 16 muls, 12 adds
//   const auto [v1, v5, v9, v13] = block2({u1, u5, u9, u13});   // 48 muls, 91 adds
//   const auto [v2, v6, v10, v14] = block3({u2, u6, u10, u14}); // 16 muls, 12 adds
//
//   const auto [r0, r4, r8, r12] = ifft4_real_unreduced({v0, v1, v2});     // 7 adds
//   const auto [r1, r5, r9, r13] = ifft4_real_unreduced({v4, v5, v6});     // 7 adds
//   const auto [r2, r6, r10, r14] = ifft4_real_unreduced({v8, v9, v10});   // 7 adds
//   const auto [r3, r7, r11, r15] = ifft4_real_unreduced({v12, v13, v14}); // 7 adds
//
//   return {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15};
// }
//
// DEVICE_FORCEINLINE void concrete_fft(bf state[WIDTH]) {
//   a<u64, 16> state_u64;
// #pragma unroll
//   for (unsigned i = 0; i < WIDTH; i++)
//     state_u64[i] = state[i].limb;
//   state_u64 = mds_multiply_freq(state_u64);
// #pragma unroll
//   for (unsigned i = 0; i < WIDTH; i++)
//     state[i] = bf::from_u62_max_minus_one(state_u64[i]);
//   //  a<u64, 16> state_u64;
//   // #pragma unroll
//   //  for (unsigned i = 0; i < WIDTH; i++)
//   //    state_u64[i] = state[i];
//   //  state_u64 = mds_multiply_freq(state_u64);
//   // #pragma unroll
//   //  for (unsigned i = 0; i < WIDTH; i++)
//   //    state[i] = state_u64[i];
// }

} // namespace airbender::monolith