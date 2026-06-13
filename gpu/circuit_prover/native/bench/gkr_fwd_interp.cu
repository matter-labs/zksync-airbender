#include "../prover/gkr/forward/flat.cuh"

// LDC-variant program residency: 14336 u16 lanes = 28KB. The module already
// carries ~26KB of production __constant__ symbols in the 64KB budget, so a
// 48KB array would fail device link; 28KB is the spec's program ceiling.
// The host performs a fit check before any upload (bench_interp/mod.rs).
// Definition (no `extern`, mirroring gpu/ntt/native/context.cu); the global
// name is the host-visible symbol the Rust side binds to.
__device__ __constant__ u16 ab_gkr_bench_program[14336];

namespace airbender::prover::gkr::bench {

// 128/4 mirrors the flat kernel's launch bound (flat_layer.cu) and must stay
// >= BENCH_INTERP_THREADS_PER_BLOCK on the Rust side.
// Stub kept from Task 2: proves the build/link/launch path.
EXTERN __launch_bounds__(128, 4) __global__ void ab_gkr_bench_fwd_interp_smoke_kernel(const bf *src, bf *dst, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  dst[gid] = src[gid];
}

// ---------------------------------------------------------------------------
// Interpreter (Task 3 core + Task 4 NativeK payload dispatch).
//
// Decode loop + SumK arity-1 + smem cell file (Task 3); NativeK instructions
// now FIRE their payload routine: operand VALUES are gathered per lane (cell
// read or direct source read at gid — exactly the CPU interpreter's `read`,
// interp.rs:71-89), the payload record (tagged byte buffer, see the ABI
// section) selects the routine, results store to the record's dst pointers at
// gid, and cache payloads additionally write the produced value into their
// alias cells (the CPU sentinel semantics of interp.rs:91-102, realized).
// ---------------------------------------------------------------------------

// ABI mirrored bit-for-bit by bench_interp/mod.rs `InterpDesc`. Keep the two
// in sync field-for-field.
struct interp_desc {
  const u16 *program_ldg;     // lane stream (global); ignored by the LDC variant
  u32 program_lanes;          // total lane count — decode must consume exactly this
  u32 n_instr;                // instruction count (not in the lane stream, isa.rs:157-159)
  const void *const *sources; // ONE table: [0..n_sources_bf) bf columns, then e4
                              // columns — Source{id,e4} banks are separate id
                              // spaces (interp.rs:69-71); e4 index = n_sources_bf + id
  u32 n_sources_bf;
  void *const *outputs; // per ORIGINAL output slot j; null = never written
  const u32 *output_e4; // bitset, 1 bit per output slot (buffer width)
  const bf *consts;     // constant table, pre-converted to Montgomery form
                        // by lower.rs (interp.rs:74-76 converts on read)
  u32 budget_cells;     // per-thread bf cells; dynamic smem = budget*4*blockDim
  u32 count;            // rows
  u32 *native_fired;    // debug: one global counter, += per (NativeK, thread)
  u32 *error_flag;      // debug: atomicOr'd INTERP_ERR_* bits; 0 = clean run
  bf *debug_cells;      // null in timing runs; layout [c * count + gid], budget_cells x count
  // Task 4: NativeK payload table. One byte buffer (16B-aligned base) of
  // variable-size tagged records + a u32 offset per payload index. Always
  // LDG-resident (the blake2-class table does not fit __constant__ next to
  // the program — spec §4). Layout below + bench_interp/lower.rs (writer).
  const u8 *payloads;
  const u32 *payload_offsets;
};

// Unexpected-program report bits (no asm("trap;") so the test context
// survives and can read the flag).
constexpr u32 INTERP_ERR_UNSUPPORTED_OP = 1;       // ProdK/DotK or SumK arity != 1
constexpr u32 INTERP_ERR_UNSUPPORTED_OPERAND = 2;  // Operand::FixedReg (fwd has n_fixed_cells == 0)
constexpr u32 INTERP_ERR_UNSUPPORTED_DST = 4;      // Dst::FixedReg / Dst::GateIn (never emitted by fwd)
constexpr u32 INTERP_ERR_OUTPUT_WIDTH = 8;         // e4_result vs output_e4 bitset disagree
constexpr u32 INTERP_ERR_NULL_OUTPUT = 16;         // write to a slot the lowering left null
constexpr u32 INTERP_ERR_TRAILING_LANES = 32;      // decode didn't consume program_lanes (isa.rs:216)
constexpr u32 INTERP_ERR_UNSUPPORTED_PAYLOAD = 64; // unknown payload kind tag
constexpr u32 INTERP_ERR_PAYLOAD_SHAPE = 128;      // record operand count vs instruction count lane
constexpr u32 INTERP_ERR_OPERAND_WIDTH = 256;      // bf lane expected, e4 lane found

// ---------------------------------------------------------------------------
// Payload ABI (writer: bench_interp/lower.rs `lower_payloads` — keep the PK_*
// tags and per-kind tails in sync; the host mirror in bench_interp/tests.rs
// documents each routine's math).
//
// record (every record starts 16B-aligned within `payloads`):
//   +0  u16 kind            // PK_* tag
//   +2  u16 n_dsts          // dst pointer count (num/den pairs = 2)
//   +4  u16 n_ops           // == instruction operand-count lane (cross-checked)
//   +6  u16 flags           // bit0: decoder select tail present (PK_*VEC*)
//   +8  u32 num_challenges  // gate batch-challenge count (ABI fidelity only)
//   +12 u32 pad
//   +16 u64 dst_ptrs[n_dsts]                 // device column bases, indexed at gid
//   then u32 batch_powers[num_challenges]    // ABSOLUTE batch powers
//        (carried for ABI/byte-cost fidelity with fwd.rs's payload model;
//        forward routines never consume them — flat stores raw outputs)
//   then the per-kind tail (e4 fields padded to 16B):
//     PK_VEC_LOOKUP_GATE / PK_CACHE_VECTORIZED_LOOKUP / PK_CACHE_MEMORY_TUPLE:
//       pad16; e4 const_term; e4 coeffs[n_ops];
//       if flags&1: e4 fill; u64 pred_ptr      // decoder predicate column
//     PK_CACHE_SINGLE_COLUMN: u32 const_mont; u32 coeffs_mont[n_ops]
//     PK_CACHE_LOOKUP_SETUP:  u64 table_ptr; u32 table_len
//     PK_MAX_QUADRATIC: u32 n_quad; u32 n_lin; u32 const_mont;
//       per quad term: u32 n_sub; u32 coeffs_mont[n_sub];
//       then u32 lin_coeffs_mont[n_lin]
//     all other kinds: no tail (gamma rides ab_gkr_lookup_gamma_consts).
//
// GateKind/CacheKind -> tag -> routine (the Task-0 census set; anything else
// fails loudly at LOWERING, never silently on device):
//   TrivialProduct, InitialGrandProductFromCaches
//                     -> PK_PRODUCT             gkr_eval_product             (flat.cuh:357)
//   MaskIntoIdentityProduct
//                     -> PK_MASK_IDENTITY       gkr_eval_mask_identity       (flat.cuh:367)
//   AggregateLookupRationalPair
//                     -> PK_LOOKUP_PAIR4        gkr_eval_lookup_pair         (flat.cuh:377)
//   LookupPairFromMaterializedBaseInputs
//                     -> PK_LOOKUP_BASE_PAIR    gkr_eval_lookup_base_pair_v2 (flat.cuh:404)
//   LookupPairFromMaterializedVectorInputs
//                     -> PK_LOOKUP_EXT_PAIR     gkr_eval_lookup_ext_pair     (flat.cuh:415)
//   LookupFromMaterializedBaseInputWithSetup
//                     -> PK_LOOKUP_BASE_MINUS_MULT
//                          gkr_eval_lookup_base_minus_multiplicity_v2        (flat.cuh:439)
//   LookupFromMaterializedVectorInputWithSetup
//                     -> PK_LOOKUP_EXT_MINUS_MULT
//                          gkr_eval_lookup_base_minus_multiplicity           (flat.cuh:451)
//   LookupWithCachedDensAndSetup
//                     -> PK_LOOKUP_CACHED_DENS  gkr_eval_lookup_cached_dens_and_setup (flat.cuh:426)
//   LookupUnbalancedPairWithMaterializedBaseInputs
//                     -> PK_LOOKUP_UNBALANCED_BASE  gkr_eval_lookup_unbalanced (flat.cuh:463)
//   LookupUnbalancedPairWithMaterializedVectorInputs
//                     -> PK_LOOKUP_UNBALANCED_EXT   gkr_eval_lookup_unbalanced (flat.cuh:475)
//   MaterializedVectorLookupInput
//                     -> PK_VEC_LOOKUP_GATE     alpha-folded affine form (NEW; the
//                        host folds alpha^k * lincomb coeffs into per-lane e4
//                        coefficients — emit_vectorized_lookup's math, value-injected)
//   MaxQuadratic      -> PK_MAX_QUADRATIC       factored flat form (NEW; bf out)
//   CacheKind::SingleColumnLookup
//                     -> PK_CACHE_SINGLE_COLUMN bf lincomb (NEW; emit_lincomb_base's
//                        math — equals the production setup_values[mapping[gid]] gather)
//   CacheKind::VectorizedLookup
//                     -> PK_CACHE_VECTORIZED_LOOKUP same affine fold as the gate,
//                        + decoder fill select (gkr_forward_cache, lookup_helpers.cuh:58-69)
//   CacheKind::MemoryTuple
//                     -> PK_CACHE_MEMORY_TUPLE  challenge-folded affine form (NEW;
//                        gkr_forward_cache_memory_tuple's math, lookup_helpers.cuh:8-33,
//                        host-lowered to const + per-lane e4 coeffs)
//   CacheKind::VectorizedLookupSetup
//                     -> PK_CACHE_LOOKUP_SETUP  gkr_forward_lookup_setup_value
//                        (lookup_helpers.cuh:35-37; table pointer rides the record)
// ---------------------------------------------------------------------------

constexpr u16 PK_PRODUCT = 0;
constexpr u16 PK_MASK_IDENTITY = 1;
constexpr u16 PK_LOOKUP_PAIR4 = 2;
constexpr u16 PK_LOOKUP_BASE_PAIR = 3;
constexpr u16 PK_LOOKUP_EXT_PAIR = 4;
constexpr u16 PK_LOOKUP_BASE_MINUS_MULT = 5;
constexpr u16 PK_LOOKUP_EXT_MINUS_MULT = 6;
constexpr u16 PK_LOOKUP_CACHED_DENS = 7;
constexpr u16 PK_LOOKUP_UNBALANCED_BASE = 8;
constexpr u16 PK_LOOKUP_UNBALANCED_EXT = 9;
constexpr u16 PK_VEC_LOOKUP_GATE = 10;
constexpr u16 PK_MAX_QUADRATIC = 11;
constexpr u16 PK_CACHE_SINGLE_COLUMN = 12;
constexpr u16 PK_CACHE_VECTORIZED_LOOKUP = 13;
constexpr u16 PK_CACHE_MEMORY_TUPLE = 14;
constexpr u16 PK_CACHE_LOOKUP_SETUP = 15;

template <bool LDC> DEVICE_FORCEINLINE u16 program_lane(const interp_desc &d, const u32 i) {
  // LDG variant: program from global via __ldg (read-only cache); LDC variant:
  // from the __constant__ array (host fit-checked <= 14336 lanes).
  return LDC ? ab_gkr_bench_program[i] : __ldg(d.program_ldg + i);
}

// Payload record field loads (record base is 16B-aligned; field offsets keep
// natural alignment per the ABI comment above).
DEVICE_FORCEINLINE u16 rec_u16(const u8 *p) { return *reinterpret_cast<const u16 *>(p); }
DEVICE_FORCEINLINE u32 rec_u32(const u8 *p) { return *reinterpret_cast<const u32 *>(p); }
DEVICE_FORCEINLINE u64 rec_u64(const u8 *p) { return *reinterpret_cast<const u64 *>(p); }
DEVICE_FORCEINLINE e4 rec_e4(const u8 *p) { return *reinterpret_cast<const e4 *>(p); }
DEVICE_FORCEINLINE bf rec_bf(const u8 *p) { return bf(rec_u32(p)); } // raw Montgomery limb
DEVICE_FORCEINLINE const u8 *rec_align16(const u8 *p) { return reinterpret_cast<const u8 *>((reinterpret_cast<uintptr_t>(p) + 15) & ~uintptr_t(15)); }

// ---------------------------------------------------------------------------
// Operand-lane value gather: ONE helper for SumK and every NativeK routine,
// mirroring the CPU `read` closure (interp.rs:71-89). The cell file is
// bf-granular smem, column-per-thread: cell c of this thread lives at
// cell_base[c * blockDim.x] with cell_base = smem + threadIdx.x.
// ---------------------------------------------------------------------------

template <bool LDC> DEVICE_FORCEINLINE e4 operand_value_e4(const interp_desc &d, bf *cell_base, const unsigned gid, const u32 lane_idx, u32 &err) {
  // Lane = kind:3 | e4:1 | idx:12 (isa.rs:140-152).
  const u16 l = program_lane<LDC>(d, lane_idx);
  const u32 kind = l & 0b111;
  const bool op_e4 = ((l >> 3) & 1) != 0;
  const u32 idx = l >> 4;
  switch (kind) {
  case 0: // Operand::Source; same ld.global.ca hints as flat (flat.cuh:292-302)
    return op_e4 ? flat_fwd_load_ext<e4>(d.sources[d.n_sources_bf + idx], gid) : e4::from_scalar(flat_fwd_load_bf(d.sources[idx], gid));
  case 1: { // Operand::Slot — read_cells (interp.rs:38-47)
    if (op_e4) {
      const bf limbs[4] = {cell_base[idx * blockDim.x], cell_base[(idx + 1) * blockDim.x], cell_base[(idx + 2) * blockDim.x],
                           cell_base[(idx + 3) * blockDim.x]};
      return e4(limbs);
    }
    return e4::from_scalar(cell_base[idx * blockDim.x]);
  }
  case 3: // Operand::Const (table is Montgomery-form on device)
    return e4::from_scalar(load<bf, ld_modifier::ca>(d.consts, idx));
  case 4: // Operand::Zero
    return e4::ZERO();
  case 5: // Operand::One
    return e4::ONE();
  case 6: // Operand::NegOne
    return e4::from_scalar(bf::neg(bf::ONE()));
  default: // kind 2 = Operand::FixedReg: forward programs have n_fixed_cells == 0
    err |= INTERP_ERR_UNSUPPORTED_OPERAND;
    return e4::ZERO();
  }
}

// bf-domain gather for routines that consume base lanes (the flat kernel's
// bf-typed arguments). Errors loudly when the lane is e4 — the IR pins these
// lanes to Domain::Base, so a width mismatch is a lowering/compiler bug.
template <bool LDC> DEVICE_FORCEINLINE bf operand_value_bf(const interp_desc &d, bf *cell_base, const unsigned gid, const u32 lane_idx, u32 &err) {
  const u16 l = program_lane<LDC>(d, lane_idx);
  const u32 kind = l & 0b111;
  const bool op_e4 = ((l >> 3) & 1) != 0;
  const u32 idx = l >> 4;
  if (op_e4) {
    err |= INTERP_ERR_OPERAND_WIDTH;
    return bf::ZERO();
  }
  switch (kind) {
  case 0:
    return flat_fwd_load_bf(d.sources[idx], gid);
  case 1:
    return cell_base[idx * blockDim.x];
  case 3:
    return load<bf, ld_modifier::ca>(d.consts, idx);
  case 4:
    return bf::ZERO();
  case 5:
    return bf::ONE();
  case 6:
    return bf::neg(bf::ONE());
  default:
    err |= INTERP_ERR_UNSUPPORTED_OPERAND;
    return bf::ZERO();
  }
}

// ---------------------------------------------------------------------------
// NativeK payload dispatch. Operand lanes start at op_base (cnt lanes);
// values are streamed into the routines one at a time — no operand array is
// ever materialized (wide kinds like MaxQuadratic / vector folds iterate).
// Cache payloads (the only Slot-dst NativeKs, pinned in lower.rs) also write
// the produced value into the alias cells, realizing the CPU sentinel.
// Returns INTERP_ERR_* bits (0 = ok).
// ---------------------------------------------------------------------------

template <bool LDC>
DEVICE_FORCEINLINE u32 fire_payload(const interp_desc &d, bf *cell_base, const unsigned gid, const u32 payload_idx, const u32 op_base, const u32 cnt,
                                    const u32 dst_class, const u32 dst_idx, const bool e4_result) {
  const u8 *rec = d.payloads + d.payload_offsets[payload_idx];
  const u32 kind = rec_u16(rec);
  const u32 n_dsts = rec_u16(rec + 2);
  const u32 n_ops = rec_u16(rec + 4);
  const u32 flags = rec_u16(rec + 6);
  const u32 num_challenges = rec_u32(rec + 8);
  if (n_ops != cnt)
    return INTERP_ERR_PAYLOAD_SHAPE;
  const u8 *dsts = rec + 16;
  // Skip the (unconsumed, ABI-fidelity) batch-power block to the kind tail.
  const u8 *tail = dsts + 8ull * n_dsts + 4ull * num_challenges;

  u32 err = 0;
  auto v_e4 = [&](const u32 k) { return operand_value_e4<LDC>(d, cell_base, gid, op_base + k, err); };
  auto v_bf = [&](const u32 k) { return operand_value_bf<LDC>(d, cell_base, gid, op_base + k, err); };
  auto dst_ptr = [&](const u32 j) { return reinterpret_cast<void *>(rec_u64(dsts + 8ull * j)); };
  auto store_e4 = [&](const u32 j, const e4 v) { store<e4, st_modifier::cs>(reinterpret_cast<e4 *>(dst_ptr(j)), v, gid); };
  auto store_bf = [&](const u32 j, const bf v) { store<bf, st_modifier::cs>(reinterpret_cast<bf *>(dst_ptr(j)), v, gid); };

  // Affine evaluator shared by the vector-lookup folds and memory tuples:
  // value = const_term + sum_k coeff_e4[k] * bf_lane[k] (+ decoder select).
  auto eval_affine_e4 = [&]() -> e4 {
    const u8 *t = rec_align16(tail);
    e4 acc = rec_e4(t);
    t += 16;
    for (u32 k = 0; k < cnt; k++) {
      acc = e4::fma(rec_e4(t), v_bf(k), acc);
      t += 16;
    }
    if (flags & 1) {
      // Decoder lookup: non-executing rows take the precomputed fill value
      // (SELECT_DECODER_FILL / lookup_helpers.cuh:61-66 semantics).
      const e4 fill = rec_e4(t);
      t += 16;
      const bf *pred = reinterpret_cast<const bf *>(rec_u64(t));
      const bf enabled = load<bf, ld_modifier::ca>(pred, gid);
      if (enabled.limb == 0)
        acc = fill;
    }
    return acc;
  };

  // Cache results route through cache_val so the alias-cell write below is
  // uniform; n_dsts==1 stores happen inside the switch.
  e4 cache_val = e4::ZERO();
  bool is_cache_kind = false;

  switch (kind) {
  case PK_PRODUCT: {
    e4 v;
    gkr_eval_product(v_e4(0), v_e4(1), v);
    store_e4(0, v);
    break;
  }
  case PK_MASK_IDENTITY: {
    // Lane order [input, mask] (gate_kind_input_nodes); routine takes (mask, value).
    const e4 input = v_e4(0);
    const e4 mask = v_e4(1);
    e4 v;
    gkr_eval_mask_identity(mask, input, v);
    store_e4(0, v);
    break;
  }
  case PK_LOOKUP_PAIR4: {
    const e4 a = v_e4(0);
    const e4 b = v_e4(1);
    const e4 c = v_e4(2);
    const e4 dd = v_e4(3);
    e4 num, den;
    gkr_eval_lookup_pair(a, b, c, dd, num, den);
    store_e4(0, num);
    store_e4(1, den);
    break;
  }
  case PK_LOOKUP_BASE_PAIR: {
    const bf b = v_bf(0);
    const bf dd = v_bf(1);
    e4 num, den;
    gkr_eval_lookup_base_pair_v2(b, dd, lookup_gamma(), lookup_gamma_sq(), lookup_two_gamma(), num, den);
    store_e4(0, num);
    store_e4(1, den);
    break;
  }
  case PK_LOOKUP_EXT_PAIR: {
    const e4 b = v_e4(0);
    const e4 dd = v_e4(1);
    e4 num, den;
    gkr_eval_lookup_ext_pair(b, dd, lookup_gamma(), num, den);
    store_e4(0, num);
    store_e4(1, den);
    break;
  }
  case PK_LOOKUP_BASE_MINUS_MULT: {
    // Lanes [input(b), setup0(c), setup1(d)] — flat_plan.rs:318-358.
    const bf b = v_bf(0);
    const bf c = v_bf(1);
    const bf dd = v_bf(2);
    e4 num, den;
    gkr_eval_lookup_base_minus_multiplicity_v2(b, c, dd, lookup_gamma(), lookup_gamma_sq(), num, den);
    store_e4(0, num);
    store_e4(1, den);
    break;
  }
  case PK_LOOKUP_EXT_MINUS_MULT: {
    // Lanes [input(b) e4, setup0(c) bf, setup1(d) e4] — flat.cuh:451-460.
    const e4 b = v_e4(0);
    const bf c = v_bf(1);
    const e4 dd = v_e4(2);
    e4 num, den;
    gkr_eval_lookup_base_minus_multiplicity(b, c, dd, lookup_gamma(), num, den);
    store_e4(0, num);
    store_e4(1, den);
    break;
  }
  case PK_LOOKUP_CACHED_DENS: {
    // Lanes [input0(a) bf, input1(b) e4, setup0(c) bf, setup1(d) e4]
    // — flat_plan.rs:223-260.
    const bf a = v_bf(0);
    const e4 b = v_e4(1);
    const bf c = v_bf(2);
    const e4 dd = v_e4(3);
    e4 num, den;
    gkr_eval_lookup_cached_dens_and_setup(a, b, c, dd, lookup_gamma(), num, den);
    store_e4(0, num);
    store_e4(1, den);
    break;
  }
  case PK_LOOKUP_UNBALANCED_BASE:
  case PK_LOOKUP_UNBALANCED_EXT: {
    // Lanes [input0(a), input1(b), remainder(d)]; routine takes (d, a, b)
    // — flat.cuh:463-484. The base variant's remainder is a bf lane.
    const e4 a = v_e4(0);
    const e4 b = v_e4(1);
    const e4 dd = kind == PK_LOOKUP_UNBALANCED_BASE ? e4::from_scalar(v_bf(2)) : v_e4(2);
    e4 num, den;
    gkr_eval_lookup_unbalanced(dd, a, b, lookup_gamma(), num, den);
    store_e4(0, num);
    store_e4(1, den);
    break;
  }
  case PK_VEC_LOOKUP_GATE: {
    store_e4(0, eval_affine_e4());
    break;
  }
  case PK_MAX_QUADRATIC: {
    // Factored flat form: out = sum_q lane_a_q * (sum_s c_qs * lane_b_qs)
    //                         + sum_l c_l * lane_l + constant, all bf.
    // The lane cursor pairs with the coefficient stream in payload_operands
    // order (fwd_operand_nodes = max_quad_flat_nodes, expr lane dropped).
    const u8 *t = tail;
    const u32 n_quad = rec_u32(t);
    const u32 n_lin = rec_u32(t + 4);
    bf acc = rec_bf(t + 8);
    t += 12;
    u32 lane = 0;
    for (u32 q = 0; q < n_quad; q++) {
      const bf a = v_bf(lane++);
      const u32 n_sub = rec_u32(t);
      t += 4;
      bf inner = bf::ZERO();
      for (u32 s = 0; s < n_sub; s++) {
        inner = bf::fma(rec_bf(t), v_bf(lane++), inner);
        t += 4;
      }
      acc = bf::fma(a, inner, acc);
    }
    for (u32 s = 0; s < n_lin; s++) {
      acc = bf::fma(rec_bf(t), v_bf(lane++), acc);
      t += 4;
    }
    if (lane != cnt)
      return INTERP_ERR_PAYLOAD_SHAPE | err;
    store_bf(0, acc);
    break;
  }
  case PK_CACHE_SINGLE_COLUMN: {
    // bf lincomb over the lookup input columns (emit_lincomb_base's math).
    const u8 *t = tail;
    bf acc = rec_bf(t);
    t += 4;
    for (u32 k = 0; k < cnt; k++) {
      acc = bf::fma(rec_bf(t), v_bf(k), acc);
      t += 4;
    }
    store_bf(0, acc);
    cache_val = e4::from_scalar(acc);
    is_cache_kind = true;
    break;
  }
  case PK_CACHE_VECTORIZED_LOOKUP:
  case PK_CACHE_MEMORY_TUPLE: {
    const e4 v = eval_affine_e4();
    store_e4(0, v);
    cache_val = v;
    is_cache_kind = true;
    break;
  }
  case PK_CACHE_LOOKUP_SETUP: {
    const e4 *table = reinterpret_cast<const e4 *>(rec_u64(tail));
    const u32 len = rec_u32(tail + 8);
    const e4 v = gkr_forward_lookup_setup_value(table, len, gid);
    store_e4(0, v);
    cache_val = v;
    is_cache_kind = true;
    break;
  }
  default:
    return INTERP_ERR_UNSUPPORTED_PAYLOAD;
  }
  if (err)
    return err;

  // Alias-cell write: the REAL value where the CPU interpreter writes the
  // caller-provided sentinel (interp.rs:95-101). lower.rs pins Slot-dst
  // <=> cache payload, so dst_class 0 only occurs for cache kinds.
  if (dst_class == 0) {
    if (!is_cache_kind)
      return INTERP_ERR_UNSUPPORTED_DST;
    cell_base[dst_idx * blockDim.x] = cache_val.base_coefficient_from_flat_idx(0);
    if (e4_result) {
      cell_base[(dst_idx + 1) * blockDim.x] = cache_val.base_coefficient_from_flat_idx(1);
      cell_base[(dst_idx + 2) * blockDim.x] = cache_val.base_coefficient_from_flat_idx(2);
      cell_base[(dst_idx + 3) * blockDim.x] = cache_val.base_coefficient_from_flat_idx(3);
    }
  }
  return 0;
}

template <bool LDC> DEVICE_FORCEINLINE void interp_body(const interp_desc d) {
  extern __shared__ u32 interp_smem[];
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= d.count)
    return;
  // Cell file: bf granularity, column-per-thread layout; e4 = 4 consecutive
  // cell INDICES (quad-aligned by the compiler), i.e. blockDim.x-strided here.
  bf *cell_base = reinterpret_cast<bf *>(interp_smem) + threadIdx.x;
  auto cell = [&](const u32 c) -> bf & { return cell_base[c * blockDim.x]; };
  // CPU zero-initializes the slot file (interp.rs:60); smem is undefined.
  // TIMING NOTE (Task 6): fixed per-thread cost a production kernel might
  // elide; measure with and without before reading absolute numbers.
  for (u32 c = 0; c < d.budget_cells; c++)
    cell(c) = bf::ZERO();

  u32 i = 0; // lane cursor — warp-uniform: every thread decodes the same lanes
  u32 native_fired = 0;
  u32 err = 0;
  for (u32 k = 0; k < d.n_instr && err == 0; k++) {
    // Header u16 = op:2 | e4_result:1 | dst_class:2 | arity:5 | dst_lo:6
    // (isa.rs:126-131); dst_lo == 63 spends a sentinel lane (isa.rs:100,133-135).
    const u16 h = program_lane<LDC>(d, i++);
    const u32 op = h & 0b11;                    // isa.rs:127 (ins.op as u16)
    const bool e4_result = ((h >> 2) & 1) != 0; // isa.rs:128
    const u32 dst_class = (h >> 3) & 0b11;      // isa.rs:129
    const u32 arity = (h >> 5) & 0b11111;       // isa.rs:130
    u32 dst_idx = (h >> 10) & 0x3F;             // isa.rs:131
    if (dst_idx == 63)
      dst_idx = program_lane<LDC>(d, i++);

    if (op == 3) { // NativeK: payload lane + operand-count lane + operand lanes (isa.rs:136-139)
      const u32 payload_idx = program_lane<LDC>(d, i++);
      const u32 cnt = program_lane<LDC>(d, i++);
      const u32 op_base = i;
      i += cnt;
      err = fire_payload<LDC>(d, cell_base, gid, payload_idx, op_base, cnt, dst_class, dst_idx, e4_result);
      native_fired++;
      continue;
    }
    if (op != 0 || arity != 1) {
      // Forward purity contract: SumK arity-1 + NativeK only (fwd.rs:5-9).
      err = INTERP_ERR_UNSUPPORTED_OP;
      break;
    }

    // SumK arity-1 == identity copy of the single operand lane.
    const e4 v = operand_value_e4<LDC>(d, cell_base, gid, i++, err);
    if (err)
      break;

    // Dst per interp.rs:131-141.
    switch (dst_class) {
    case 0: // Dst::Slot — write_cells (interp.rs:49-61)
      cell(dst_idx) = v.base_coefficient_from_flat_idx(0);
      if (e4_result) {
        cell(dst_idx + 1) = v.base_coefficient_from_flat_idx(1);
        cell(dst_idx + 2) = v.base_coefficient_from_flat_idx(2);
        cell(dst_idx + 3) = v.base_coefficient_from_flat_idx(3);
      }
      break;
    case 2: { // Dst::Output — store at gid, width per slot (interp.rs:138)
      const bool slot_e4 = ((d.output_e4[dst_idx >> 5] >> (dst_idx & 31)) & 1) != 0;
      if (slot_e4 != e4_result) {
        err = INTERP_ERR_OUTPUT_WIDTH;
        break;
      }
      void *const out = d.outputs[dst_idx];
      if (out == nullptr) {
        err = INTERP_ERR_NULL_OUTPUT;
        break;
      }
      if (e4_result)
        reinterpret_cast<e4 *>(out)[gid] = v;
      else
        reinterpret_cast<bf *>(out)[gid] = v.base_coefficient_from_flat_idx(0);
      break;
    }
    default: // 1 = Dst::FixedReg, 3 = Dst::GateIn — never emitted by the fwd compiler
      err = INTERP_ERR_UNSUPPORTED_DST;
      break;
    }
  }

  if (err == 0 && i != d.program_lanes)
    err = INTERP_ERR_TRAILING_LANES; // mirror of decode's trailing-lanes assert (isa.rs:216)
  // Parity-test cell-file dump: unconditional on err so failures stay debuggable.
  if (d.debug_cells != nullptr)
    for (u32 c = 0; c < d.budget_cells; c++)
      d.debug_cells[c * d.count + gid] = cell(c);
  if (err != 0)
    atomicOr(d.error_flag, err);
  // TIMING NOTE (Task 6): one atomicAdd per thread to a single global counter
  // is contended serialization in the kernel tail — timing runs must pass
  // native_fired = nullptr (guarded here), like debug_cells.
  if (native_fired != 0 && d.native_fired != nullptr)
    atomicAdd(d.native_fired, native_fired); // test expects n_native_instrs * count total
}

EXTERN __launch_bounds__(128, 4) __global__ void ab_gkr_bench_fwd_interp_ldg_kernel(const interp_desc desc) { interp_body<false>(desc); }

EXTERN __launch_bounds__(128, 4) __global__ void ab_gkr_bench_fwd_interp_ldc_kernel(const interp_desc desc) { interp_body<true>(desc); }

} // namespace airbender::prover::gkr::bench
