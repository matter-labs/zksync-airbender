#include <keccak256.cuh>
#include <proth120/transform.cuh>

namespace airbender::trace::commit {

using namespace ::airbender::ntt;
using ::airbender::hash::keccak256::digest;
using ::airbender::hash::keccak256::hash_node;
using ::airbender::hash::keccak256::leaf_sponge;
using ::airbender::hash::keccak256::static_for;

// Tiles [first_tile, first_tile + tiles) of the suffix tile layout [coset][tile][column][f_lo][w][2^V]: one thread per
// leaf j = g + 2^a f_lo, g = (first_tile + tile) 2^sb + w; the block's 256 leaves give its depth-TREE_DEPTH nodes
// out[coset * out_coset_stride + (j >> TREE_DEPTH)].
struct leaf_sink_args {
  const pr *tile;
  digest *out;
  u64 tile_coset_stride;
  u64 out_coset_stride;
  u32 log_a;
  u32 log_r;
  u32 skip_bottom;
  u32 first_tile;
  u32 log_n;
  u32 log_domain;
  u32 k0;
  u32 reserved;
};

static_assert(sizeof(leaf_sink_args) == 64);

// An openings slot (skip_bottom >= 8): the queries in coset *coset whose depth-skip_bottom subtree the block belongs to,
// gated by *gate. Hit blocks write the queried leaves' values [query][slot'][column] and path layers 0..2 [query][depth]
// besides their depth-3 nodes; blocks without a hit return.
struct leaf_open_args {
  const u32 *gate;
  const u32 *coset;
  const u32 *queries;
  pr *leaves;
  digest *paths;
  u32 count;
  u32 log_lde;
  u32 depth;
  u32 reserved;
};

static_assert(sizeof(leaf_open_args) == 56);

struct sink_leaf {
  u32 tile;
  u32 f_lo;
  u32 w;
  u32 g;
  u32 j;
};

DEVICE_FORCEINLINE sink_leaf leaf_of(const leaf_sink_args &args, const u32 log_f, const u32 index) {
  const u32 w = index & ((1u << args.skip_bottom) - 1);
  const u32 f_lo = (index >> args.skip_bottom) & ((1u << log_f) - 1);
  const u32 tile = index >> (args.skip_bottom + log_f);
  const u32 g = ((args.first_tile + tile) << args.skip_bottom) + w;
  return {tile, f_lo, w, g, g + (f_lo << args.log_a)};
}

// Column loads stay in program order behind the previous column's absorb: a load hoisted above a permutation keeps its 16 bytes
// live across it.
DEVICE_FORCEINLINE pr load_in_order(const pr *address) {
  pr value;
  asm volatile("ld.volatile.global.v4.u32 {%0, %1, %2, %3}, [%4];"
               : "=r"(value.limbs[0]), "=r"(value.limbs[1]), "=r"(value.limbs[2]), "=r"(value.limbs[3])
               : "l"(address));
  return value;
}

// The last V stages of one leaf group: local stage u, local region z at x[2^(V-u) z ..].
template <u32 V, class T> DEVICE_FORCEINLINE void finish_leaf_group(pr (&x)[1u << V], const T &twiddle) {
#pragma unroll
  for (u32 u = 0; u < V; u++) {
#pragma unroll
    for (u32 z = 0; z < (1u << u); z++) {
      const pr w = twiddle(u, z);
#pragma unroll
      for (u32 i = 0; i < ((1u << V) >> (u + 1)); i++)
        dit_policy{}.exchg(x[(z << (V - u)) + i], x[(z << (V - u)) + i + ((1u << V) >> (u + 1))], w);
    }
  }
}

template <u32 C, u32 V, u32 TREE_DEPTH, bool CONVERT, bool OPEN>
DEVICE_FORCEINLINE void leaf_sink(const leaf_sink_args &args, const leaf_open_args &open, const proth120_twiddle_descriptor &d) {
  static_assert(TREE_DEPTH >= 3 && TREE_DEPTH <= 8 && (!OPEN || (TREE_DEPTH == 3 && !CONVERT)));
  constexpr u32 VALUES = 1u << V;
  __shared__ digest leaves[256];
  __shared__ digest layer_1[128];
  __shared__ digest layer_2[64];
  const u32 tid = threadIdx.x;
  const u32 log_f = args.log_r - V;
  __shared__ u32 hits[OPEN ? 1024 : 1];
  __shared__ u32 hit_count;
  const u32 block_j = leaf_of(args, log_f, blockIdx.x * 256).j;
  if constexpr (OPEN) {
    if (open.gate && !*open.gate)
      return;
    const u32 coset = *open.coset;
    if (tid == 0)
      hit_count = 0;
    __syncthreads();
    for (u32 q = tid; q < open.count; q += 256) {
      const u32 query = open.queries[q];
      if ((query & ((1u << open.log_lde) - 1)) == coset && (query >> open.log_lde) >> args.skip_bottom == block_j >> args.skip_bottom)
        hits[atomicAdd(&hit_count, 1)] = q;
    }
    __syncthreads();
    if (hit_count == 0)
      return;
  }
  const sink_leaf leaf = leaf_of(args, log_f, blockIdx.x * 256 + tid);
  const u32 region = (bitreverse_low_bits(leaf.g, args.log_a) << log_f) + bitreverse_low_bits(leaf.f_lo, log_f);
  const u64 column_stride = u64{1} << (args.skip_bottom + args.log_r);
  const pr *group = args.tile + blockIdx.z * args.tile_coset_stride + static_cast<u64>(leaf.tile) * C * column_stride +
                    (static_cast<u64>((leaf.f_lo << args.skip_bottom) + leaf.w) << V);
  // The column loop's twiddles (C > 1) and the leaf elements absorbed after the first permutation (C = 1, V = 4) wait in
  // shared memory instead of registers, [entry][thread].
  constexpr u32 HOISTED = C > 1 ? VALUES - 1 : 0;
  constexpr u32 PARKED = C == 1 && VALUES > 8 ? VALUES - 8 : 0;
  __shared__ pr waiting[(HOISTED > PARKED ? HOISTED : PARKED) * 256 + 1];
  if constexpr (HOISTED) {
#pragma unroll
    for (u32 u = 0; u < V; u++)
#pragma unroll
      for (u32 z = 0; z < (1u << u); z++)
        waiting[((1u << u) - 1 + z) * 256 + tid] = get_forward_pr_twiddle(d, (region << u) + z);
  }
  const auto twiddle = [&](const u32 u, const u32 z) {
    if constexpr (HOISTED)
      return waiting[((1u << u) - 1 + z) * 256 + tid];
    else
      return get_forward_pr_twiddle(d, (region << u) + z);
  };
  pr base_root_inv{};
  if constexpr (CONVERT) {
    const u32 log_l = d.log_max_domain;
    const u64 k = args.k0 + blockIdx.z;
    const u64 mask = (u64{1} << log_l) - 1;
    base_root_inv = pr_root_power_inv(d, ((k << (log_l - args.log_domain)) + (static_cast<u64>(leaf.j) << (log_l - args.log_n))) & mask);
  }
  leaf_sponge<2 * C * VALUES, true> sponge;
  static_for<C>([&](auto column) {
    pr x[VALUES];
#pragma unroll
    for (u32 t = 0; t < VALUES; t++)
      x[t] = load_in_order(group + decltype(column)::value * column_stride + t);
    finish_leaf_group<V>(x, twiddle);
    if constexpr (CONVERT)
      ab_pr_convert_leaf<V>(d, x, base_root_inv);
    if constexpr (OPEN) {
      for (u32 i = 0; i < hit_count; i++) {
        const u32 q = hits[i];
        if (open.queries[q] >> open.log_lde == leaf.j) {
#pragma unroll
          for (u32 t = 0; t < VALUES; t++)
            open.leaves[static_cast<u64>(q) * C * VALUES + t * C + decltype(column)::value] = x[t];
        }
      }
    }
    static_for<VALUES>([&](auto t) {
      constexpr u32 T = decltype(t)::value;
      if constexpr (PARKED && T >= 8)
        waiting[(T - 8) * 256 + tid] = x[T];
      else
        sponge.template absorb_element<decltype(column)::value * VALUES + T>(x[T]);
    });
  });
  static_for<PARKED>([&](auto t) { sponge.template absorb_element<8 + decltype(t)::value>(waiting[decltype(t)::value * 256 + tid]); });
  leaves[tid] = sponge.finalize();
  __syncthreads();
  if (tid < 128)
    layer_1[tid] = hash_node<true>(leaves[2 * tid], leaves[2 * tid + 1]);
  __syncthreads();
  if (tid < 64)
    layer_2[tid] = hash_node<true>(layer_1[2 * tid], layer_1[2 * tid + 1]);
  __syncthreads();
  if constexpr (OPEN) {
    for (u32 i = tid; i < hit_count; i += 256) {
      const u32 q = hits[i];
      const u32 w = (open.queries[q] >> open.log_lde) - block_j;
      if (w < 256) {
        digest *path = open.paths + static_cast<u64>(q) * open.depth;
        path[0] = leaves[w ^ 1];
        path[1] = layer_1[(w >> 1) ^ 1];
        path[2] = layer_2[(w >> 2) ^ 1];
      }
    }
  }
  if (tid >= 32)
    return;
  digest node = hash_node<true>(layer_2[2 * tid], layer_2[2 * tid + 1]);
#pragma unroll
  for (u32 shift = 0; shift + 3 < TREE_DEPTH; shift++) {
    digest sibling;
#pragma unroll
    for (u32 word = 0; word < 8; word++)
      sibling.words[word] = __shfl_xor_sync(0xffffffffu, node.words[word], 1u << shift);
    if ((tid & ((2u << shift) - 1)) == 0)
      node = hash_node<true>(node, sibling);
  }
  if (tid & ((1u << (TREE_DEPTH - 3)) - 1))
    return;
  const sink_leaf first = leaf_of(args, log_f, blockIdx.x * 256 + 8 * tid);
  args.out[blockIdx.z * args.out_coset_stride + (first.j >> TREE_DEPTH)] = node;
}

#define LEAF_SINK_KERNEL(C, V, TREE_DEPTH, MODE, CONVERT)                                                                                                      \
  EXTERN __launch_bounds__(256, 2)                                                                                                                             \
      __global__ void ab_pr_leaf_sink_##C##_##V##_##TREE_DEPTH##_##MODE##_kernel(const leaf_sink_args args, const proth120_twiddle_descriptor d) {             \
    leaf_sink<C, V, TREE_DEPTH, CONVERT, false>(args, {}, d);                                                                                                  \
  }

#define LEAF_OPEN_KERNEL(C, V)                                                                                                                                 \
  EXTERN __launch_bounds__(256, 2)                                                                                                                             \
      __global__ void ab_pr_leaf_sink_##C##_##V##_3_open_kernel(const leaf_sink_args args, const leaf_open_args open, const proth120_twiddle_descriptor d) {   \
    leaf_sink<C, V, 3, false, true>(args, open, d);                                                                                                            \
  }

LEAF_SINK_KERNEL(1, 2, 3, commit, false)
LEAF_SINK_KERNEL(2, 1, 3, commit, false)
LEAF_SINK_KERNEL(7, 2, 3, commit, false)
LEAF_SINK_KERNEL(13, 1, 3, commit, false)
LEAF_SINK_KERNEL(1, 3, 5, coefficient_tree, true)
LEAF_SINK_KERNEL(1, 4, 5, coefficient_tree, true)
LEAF_OPEN_KERNEL(1, 2)
LEAF_OPEN_KERNEL(2, 1)
LEAF_OPEN_KERNEL(7, 2)
LEAF_OPEN_KERNEL(13, 1)

} // namespace airbender::trace::commit
