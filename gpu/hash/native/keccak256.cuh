#pragma once

#include "common.cuh"
#include "primitives/field.cuh"
#include "primitives/proth120.cuh"

namespace airbender::hash::keccak256 {

using ::airbender::primitives::field::proth120;

struct digest {
  u32 words[8];
};

static_assert(sizeof(digest) == 32);
static_assert(alignof(digest) == 4);
static_assert(std::is_standard_layout_v<digest>);

DEVICE_FORCEINLINE u64 rotate_left(u64 value, unsigned shift) { return shift == 0 ? value : (value << shift) | (value >> (64 - shift)); }

DEVICE_FORCEINLINE u32 byte_swap(u32 value) { return __byte_perm(value, 0, 0x0123); }

DEVICE_FORCEINLINE u64 round_constant(unsigned round) {
  switch (round) {
  case 0:
    return 0x0000000000000001ULL;
  case 1:
    return 0x0000000000008082ULL;
  case 2:
    return 0x800000000000808aULL;
  case 3:
    return 0x8000000080008000ULL;
  case 4:
    return 0x000000000000808bULL;
  case 5:
    return 0x0000000080000001ULL;
  case 6:
    return 0x8000000080008081ULL;
  case 7:
    return 0x8000000000008009ULL;
  case 8:
    return 0x000000000000008aULL;
  case 9:
    return 0x0000000000000088ULL;
  case 10:
    return 0x0000000080008009ULL;
  case 11:
    return 0x000000008000000aULL;
  case 12:
    return 0x000000008000808bULL;
  case 13:
    return 0x800000000000008bULL;
  case 14:
    return 0x8000000000008089ULL;
  case 15:
    return 0x8000000000008003ULL;
  case 16:
    return 0x8000000000008002ULL;
  case 17:
    return 0x8000000000000080ULL;
  case 18:
    return 0x000000000000800aULL;
  case 19:
    return 0x800000008000000aULL;
  case 20:
    return 0x8000000080008081ULL;
  case 21:
    return 0x8000000000008080ULL;
  case 22:
    return 0x0000000080000001ULL;
  default:
    return 0x8000000080008008ULL;
  }
}

DEVICE_FORCEINLINE void keccak_round(u64 state[25], u64 constant) {
  constexpr unsigned rotations[25] = {0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14};
  u64 columns[5], delta[5], moved[25];
#pragma unroll
  for (unsigned x = 0; x < 5; x++)
    columns[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
#pragma unroll
  for (unsigned x = 0; x < 5; x++)
    delta[x] = columns[(x + 4) % 5] ^ rotate_left(columns[(x + 1) % 5], 1);
#pragma unroll
  for (unsigned i = 0; i < 25; i++)
    state[i] ^= delta[i % 5];
#pragma unroll
  for (unsigned x = 0; x < 5; x++)
#pragma unroll
    for (unsigned y = 0; y < 5; y++)
      moved[y + 5 * ((2 * x + 3 * y) % 5)] = rotate_left(state[x + 5 * y], rotations[x + 5 * y]);
#pragma unroll
  for (unsigned y = 0; y < 5; y++)
#pragma unroll
    for (unsigned x = 0; x < 5; x++)
      state[x + 5 * y] = moved[x + 5 * y] ^ (~moved[(x + 1) % 5 + 5 * y] & moved[(x + 2) % 5 + 5 * y]);
  state[0] ^= constant;
}

template <bool ROUND_LOOP> DEVICE_FORCEINLINE void permute(u64 state[25]) {
  if constexpr (ROUND_LOOP) {
#pragma unroll 1
    for (unsigned round = 0; round < 24; round++)
      keccak_round(state, round_constant(round));
  } else {
    keccak_round(state, 0x0000000000000001ULL);
    keccak_round(state, 0x0000000000008082ULL);
    keccak_round(state, 0x800000000000808aULL);
    keccak_round(state, 0x8000000080008000ULL);
    keccak_round(state, 0x000000000000808bULL);
    keccak_round(state, 0x0000000080000001ULL);
    keccak_round(state, 0x8000000080008081ULL);
    keccak_round(state, 0x8000000000008009ULL);
    keccak_round(state, 0x000000000000008aULL);
    keccak_round(state, 0x0000000000000088ULL);
    keccak_round(state, 0x0000000080008009ULL);
    keccak_round(state, 0x000000008000000aULL);
    keccak_round(state, 0x000000008000808bULL);
    keccak_round(state, 0x800000000000008bULL);
    keccak_round(state, 0x8000000000008089ULL);
    keccak_round(state, 0x8000000000008003ULL);
    keccak_round(state, 0x8000000000008002ULL);
    keccak_round(state, 0x8000000000000080ULL);
    keccak_round(state, 0x000000000000800aULL);
    keccak_round(state, 0x800000008000000aULL);
    keccak_round(state, 0x8000000080008081ULL);
    keccak_round(state, 0x8000000000008080ULL);
    keccak_round(state, 0x0000000080000001ULL);
    keccak_round(state, 0x8000000080008008ULL);
  }
}

DEVICE_FORCEINLINE void keccak_f1600(u64 state[25]) { permute<false>(state); }

template <unsigned HALF> DEVICE_FORCEINLINE u64 canonical_lane(const u8 bytes[16]) {
  u64 lane = 0;
#pragma unroll
  for (unsigned i = 0; i < 8; i++)
    lane |= static_cast<u64>(bytes[HALF * 8 + i]) << (8 * i);
  return lane;
}

template <bool ROUND_LOOP = false> struct sponge_impl {
  u64 state[25]{};
  unsigned position = 0;

  template <unsigned LANE> DEVICE_FORCEINLINE void absorb_lane(u64 value) {
    static_assert(LANE < 17);
    state[LANE] ^= value;
  }

  template <typename Read> DEVICE_FORCEINLINE void absorb_stream(u64 len, Read read) {
    u64 offset = 0;
    while (offset < len) {
      const unsigned take = static_cast<unsigned>(min(static_cast<u64>(136 - position), len - offset));
#pragma unroll
      for (unsigned lane = 0; lane < 17; lane++) {
        u64 value = 0;
#pragma unroll
        for (unsigned byte = 0; byte < 8; byte++) {
          const unsigned index = lane * 8 + byte;
          if (index >= position && index < position + take)
            value |= static_cast<u64>(read(offset + index - position)) << (byte * 8);
        }
        state[lane] ^= value;
      }
      offset += take;
      position += take;
      if (position == 136) {
        permute<ROUND_LOOP>(state);
        position = 0;
      }
    }
  }

  DEVICE_FORCEINLINE void absorb_bytes(const u8 *input, u64 len) {
    absorb_stream(len, [=](u64 index) { return input[index]; });
  }

  DEVICE_FORCEINLINE void absorb_u32_stream(const u32 *input, u64 count) {
    absorb_stream(count * 4, [=](u64 index) { return static_cast<u8>(input[index >> 2] >> (8 * (index & 3))); });
  }

  DEVICE_FORCEINLINE void absorb_fields(const proth120 *input, u64 count) {
    u64 cached_index = ~u64{0}, first = 0, second = 0;
    absorb_stream(count * 16, [&](u64 index) {
      const u64 element = index >> 4;
      if (element != cached_index) {
        u8 bytes[16];
        proth120::to_canonical_be_bytes(input[element], bytes);
        first = canonical_lane<0>(bytes);
        second = canonical_lane<1>(bytes);
        cached_index = element;
      }
      return static_cast<u8>((index & 8 ? second : first) >> (8 * (index & 7)));
    });
  }

  DEVICE_FORCEINLINE void finalize(u8 out[32]) {
#pragma unroll
    for (unsigned lane = 0; lane < 17; lane++)
      if (position / 8 == lane)
        state[lane] ^= u64{1} << (8 * (position & 7));
    state[16] ^= 0x8000000000000000ULL;
    permute<ROUND_LOOP>(state);
#pragma unroll
    for (unsigned i = 0; i < 32; i++)
      out[i] = static_cast<u8>(state[i / 8] >> (8 * (i & 7)));
  }
};

using sponge = sponge_impl<>;

DEVICE_FORCEINLINE void hash_bytes(const u8 *input, u64 len, u8 out[32]) {
  sponge hash;
  hash.absorb_bytes(input, len);
  hash.finalize(out);
}

DEVICE_FORCEINLINE digest digest_from_bytes(const u8 bytes[32]) {
  digest result;
#pragma unroll
  for (unsigned word = 0; word < 8; word++)
    result.words[word] = (static_cast<u32>(bytes[4 * word]) << 24) | (static_cast<u32>(bytes[4 * word + 1]) << 16) |
                         (static_cast<u32>(bytes[4 * word + 2]) << 8) | bytes[4 * word + 3];
  return result;
}

DEVICE_FORCEINLINE void digest_to_bytes(const digest &value, u8 bytes[32]) {
#pragma unroll
  for (unsigned word = 0; word < 8; word++)
#pragma unroll
    for (unsigned byte = 0; byte < 4; byte++)
      bytes[4 * word + byte] = static_cast<u8>(value.words[word] >> (24 - 8 * byte));
}

DEVICE_FORCEINLINE digest digest_from_state(const u64 state[25]) {
  digest result;
#pragma unroll
  for (unsigned word = 0; word < 8; word++)
    result.words[word] = byte_swap(static_cast<u32>(state[word / 2] >> (32 * (word & 1))));
  return result;
}

DEVICE_FORCEINLINE digest hash_node(const digest &left, const digest &right) {
  sponge hash;
#pragma unroll
  for (unsigned lane = 0; lane < 4; lane++) {
    hash.state[lane] = byte_swap(left.words[2 * lane]) | (static_cast<u64>(byte_swap(left.words[2 * lane + 1])) << 32);
    hash.state[lane + 4] = byte_swap(right.words[2 * lane]) | (static_cast<u64>(byte_swap(right.words[2 * lane + 1])) << 32);
  }
  hash.state[8] = 1;
  hash.state[16] = 0x8000000000000000ULL;
  keccak_f1600(hash.state);
  return digest_from_state(hash.state);
}

DEVICE_FORCEINLINE digest hash_leaf(const proth120 *values, const u32 log_domain, const u32 log_v, const u32 columns, const u32 leaf) {
  const u32 log_leaves = log_domain - log_v;
  const u32 slot_mask = (1u << log_v) - 1;
  const u32 lanes = columns << (log_v + 1);
  const u32 blocks = lanes / 17 + 1;
  u64 state[25]{};
  u64 second = 0;
  for (u32 block = 0; block < blocks; block++) {
#pragma unroll
    for (u32 lane = 0; lane < 17; lane++) {
      const u32 global = block * 17 + lane;
      if (global < lanes) {
        if (global & 1) {
          state[lane] ^= second;
        } else {
          const u32 element = global >> 1;
          const u64 column = element >> log_v;
          const u64 slot = bitreverse_low_bits(element & slot_mask, log_v);
          u8 bytes[16];
          proth120::to_canonical_be_bytes(values[(column << log_domain) + leaf + (slot << log_leaves)], bytes);
          state[lane] ^= canonical_lane<0>(bytes);
          second = canonical_lane<1>(bytes);
        }
      } else if (global == lanes) {
        state[lane] ^= 1;
      }
    }
    if (block == blocks - 1)
      state[16] ^= 0x8000000000000000ULL;
    keccak_f1600(state);
  }
  return digest_from_state(state);
}

template <typename LaneAt> DEVICE_FORCEINLINE void absorb_lanes(u64 state[25], const u64 bytes, LaneAt lane_at) {
  const u64 lanes = bytes / 8 + (bytes % 8 != 0);
  const u64 pad_lane = bytes / 8;
  const u64 pad = u64{1} << (8 * (bytes % 8));
  const u64 blocks = bytes / 136 + 1;
  for (u64 block = 0; block < blocks; block++) {
#pragma unroll
    for (u32 lane = 0; lane < 17; lane++) {
      const u64 global = block * 17 + lane;
      if (global < lanes)
        state[lane] ^= lane_at(global);
      if (global == pad_lane)
        state[lane] ^= pad;
    }
    if (block == blocks - 1)
      state[16] ^= 0x8000000000000000ULL;
    keccak_f1600(state);
  }
}

DEVICE_FORCEINLINE void seed_to_state(const u8 seed[32], u64 state[25]) {
#pragma unroll
  for (u32 lane = 0; lane < 25; lane++)
    state[lane] = 0;
#pragma unroll
  for (u32 byte = 0; byte < 32; byte++)
    state[byte / 8] |= static_cast<u64>(seed[byte]) << (8 * (byte % 8));
}

DEVICE_FORCEINLINE void state_to_seed(const u64 state[25], u8 seed[32]) {
#pragma unroll
  for (u32 byte = 0; byte < 32; byte++)
    seed[byte] = static_cast<u8>(state[byte / 8] >> (8 * (byte % 8)));
}

DEVICE_FORCEINLINE u64 u32_pair_lane(const u32 *input, const u64 count, const u64 lane) {
  const u64 word = 2 * lane;
  const u64 low = input[word];
  const u64 high = word + 1 < count ? input[word + 1] : 0;
  return low | (high << 32);
}

DEVICE_FORCEINLINE void commit_initial_u32(const u32 *input, u64 count, u8 seed[32]) {
  u64 state[25]{};
  absorb_lanes(state, 4 * count, [=](const u64 lane) { return u32_pair_lane(input, count, lane); });
  state_to_seed(state, seed);
}

DEVICE_FORCEINLINE void commit_u32(u8 seed[32], const u32 *input, u64 count) {
  u64 state[25];
  seed_to_state(seed, state);
  absorb_lanes(state, 32 + 4 * count, [=](const u64 lane) { return lane < 4 ? 0 : u32_pair_lane(input, count, lane - 4); });
  state_to_seed(state, seed);
}

DEVICE_FORCEINLINE void commit_fields(u8 seed[32], const proth120 *input, u64 count) {
  u64 state[25];
  seed_to_state(seed, state);
  u64 second = 0;
  absorb_lanes(state, 32 + 16 * count, [&](const u64 lane) {
    if (lane < 4)
      return u64{0};
    const u64 offset = lane - 4;
    if (offset & 1)
      return second;
    u8 bytes[16];
    proth120::to_canonical_be_bytes(input[offset >> 1], bytes);
    second = canonical_lane<1>(bytes);
    return canonical_lane<0>(bytes);
  });
  state_to_seed(state, seed);
}

DEVICE_FORCEINLINE void rehash_seed(u64 state[25]) {
#pragma unroll
  for (u32 lane = 4; lane < 25; lane++)
    state[lane] = 0;
  state[4] = 1;
  state[16] = 0x8000000000000000ULL;
  keccak_f1600(state);
}

DEVICE_FORCEINLINE void draw_u32(u8 seed[32], u32 *out, u64 count) {
  u64 state[25];
  seed_to_state(seed, state);
  for (u64 block = 0; block * 8 < count; block++) {
    rehash_seed(state);
#pragma unroll
    for (u32 word = 0; word < 8; word++)
      if (block * 8 + word < count)
        out[block * 8 + word] = static_cast<u32>(state[word / 2] >> (32 * (word % 2)));
  }
  state_to_seed(state, seed);
}

DEVICE_FORCEINLINE proth120 draw_field(u8 seed[32]) {
  u64 state[25];
  seed_to_state(seed, state);
  rehash_seed(state);
  state_to_seed(state, seed);
  const u32 natural_le[4] = {byte_swap(static_cast<u32>(state[1] >> 32)), byte_swap(static_cast<u32>(state[1])), byte_swap(static_cast<u32>(state[0] >> 32)),
                             byte_swap(static_cast<u32>(state[0]))};
  return proth120::from_u128_with_reduction(natural_le);
}

DEVICE_FORCEINLINE void pow_digest(const u8 seed[32], u64 nonce, u8 out[32]) {
  u64 state[25];
  seed_to_state(seed, state);
  state[4] = (static_cast<u64>(byte_swap(static_cast<u32>(nonce))) << 32) | byte_swap(static_cast<u32>(nonce >> 32));
  state[5] = 1;
  state[16] = 0x8000000000000000ULL;
  keccak_f1600(state);
  state_to_seed(state, out);
}

DEVICE_FORCEINLINE bool top_bits_are_zero(const u8 value[32], u32 bits) {
  const u32 full = bits / 8;
  const u32 partial = bits % 8;
#pragma unroll
  for (u32 byte = 0; byte < 32; byte++) {
    if (byte < full && value[byte] != 0)
      return false;
    if (byte == full && partial != 0 && (value[byte] >> (8 - partial)) != 0)
      return false;
  }
  return true;
}

DEVICE_FORCEINLINE bool advance(const u64 nonce, const u64 stride, const u64 max_nonce, u64 &next) {
  if (stride > max_nonce || nonce >= max_nonce - stride) {
    next = 0;
    return false;
  }
  next = nonce + stride;
  return true;
}

} // namespace airbender::hash::keccak256
