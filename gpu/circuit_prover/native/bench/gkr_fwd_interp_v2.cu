// GKR eval-ISA **v2** forward interpreter (Phase 5.1).
//
// A fused single-pass interpreter over the v2 lane stream
// (`gkr_eval_isa::isa_v2::encode2`). One thread = one row (`gid`). The decode
// MIRRORS `decode2` exactly (header family bit -> arith op/arity OR macro
// routine/n_operands; then the operand region; then footer dsts); the per-row
// math MIRRORS `gkr_eval_isa::interp_v2::execute2` (the CPU golden model, itself
// transcribed from the production per-row primitives in `flat.cuh` /
// `lookup_helpers.cuh` / `gkr_forward_generation.cuh`). No opaque payload table
// (the v1 NativeK reform, spec §1): every datum rides a typed lane.
//
// ABI mirror: `bench_interp::interp_v2_gpu::InterpDesc2` (keep field-for-field).
// Compiled only under -DAB_GKR_BENCH (feature `bench`), same as the v1 kernel.

#include "../prover/gkr/forward/flat.cuh"

// The LDC variant REUSES the v1 bench program __constant__ array (defined in
// gkr_fwd_interp.cu). The `__constant__` budget is 64 KB total and the
// production banks + the v1 28 KB array leave no room for a second 28 KB array
// (nvlink "too much global constant data"); v1 and v2 LDC runs never overlap,
// so they share one upload slot (Rust `upload_bench_program_to_constant`).
extern __constant__ u16 ab_gkr_bench_program[14336];

// All interpreter code lives in the crate's bench namespace (gpu/AGENTS.md C++
// namespace = owning crate) so unqualified lookup finds the production helpers
// in the parent `airbender::prover::gkr` (flat.cuh: flat_fwd_load_*, store, …).
namespace airbender::prover::gkr::bench {

// --- error bits (atomicOr'd into desc.error_flag; 0 = clean) ------------------
constexpr u32 INTERP2_ERR_TRAILING_LANES = 1; // decode != program_lanes
constexpr u32 INTERP2_ERR_UNSUPPORTED_ROUTINE = 2;
constexpr u32 INTERP2_ERR_NULL_COLUMN = 4;   // Affine/Materialize ptr null
constexpr u32 INTERP2_ERR_BAD_ASARM = 8;     // memtup as_arm out of 0..=3
constexpr u32 INTERP2_ERR_OUTPUT_COUNT = 16; // dst count != routine output

// --- v2 routine ids (mirror gkr_eval_isa::isa_v2::RoutineId / routine_from_u8)-
constexpr u32 R_GATE_OUTPUT_FOLD = 0;
constexpr u32 R_PRODUCT = 1;
constexpr u32 R_MASK_IDENTITY = 2;
constexpr u32 R_AGGREGATE_LOOKUP_PAIR = 3;
constexpr u32 R_LOOKUP_BASE_PAIR = 4;
constexpr u32 R_LOOKUP_EXT_PAIR = 5;
constexpr u32 R_LOOKUP_BASE_MINUS_MULT = 6;
constexpr u32 R_LOOKUP_EXT_MINUS_MULT = 7;
constexpr u32 R_LOOKUP_CACHED_DENS = 8;
constexpr u32 R_LOOKUP_UNBALANCED_BASE = 9;
constexpr u32 R_LOOKUP_UNBALANCED_EXT = 10;
constexpr u32 R_VECTOR_LOOKUP_GATE = 11;
constexpr u32 R_MATERIALIZE_SINGLE_LOOKUP = 12;
constexpr u32 R_LOOKUP_DECODER_DENS_SETUP = 13;
constexpr u32 R_GRAND_PRODUCT_WITHOUT_CACHES = 14;
constexpr u32 R_MATERIALIZE_GRAND_PRODUCT_TERM = 15;
constexpr u32 R_SINGLE_COLUMN_LOOKUP = 16;
constexpr u32 R_VECTORIZED_LOOKUP = 17;
constexpr u32 R_VECTORIZED_LOOKUP_SETUP = 18;
constexpr u32 R_MEMORY_TUPLE = 19;
constexpr u32 R_MEMORY_INIT_TEARDOWN_PAIR = 20;

// --- gather variants (mirror gkr_eval_isa::isa_v2::IndirectKind) --------------
constexpr u8 GK_MAPPED_VIRTUAL_BF = 0;
constexpr u8 GK_MAPPED_GENERIC_E4 = 1;
constexpr u8 GK_DECODER_MAPPED_E4 = 2;
constexpr u8 GK_ROW_INDEXED_SETUP_E4 = 3;
constexpr u8 GK_INITS_TEARDOWNS_HIGH_ADDR = 4;

// --- LdcSub (mirror gkr_eval_isa::isa_v2::LdcSub) -----------------------------
constexpr u32 LDC_CONST = 0;
constexpr u32 LDC_CONST_CHALLENGE = 1;
constexpr u32 LDC_ARG_CHALLENGE = 2;
constexpr u32 LDC_SPECIAL = 3;
constexpr u32 SPECIAL_ZERO = 0;
constexpr u32 SPECIAL_ONE = 1;
constexpr u32 SPECIAL_NEG_ONE = 2;

// --- memory-tuple role / const tags (mirror compiler_v2::macros + isa_v2) -----
constexpr u8 MEMTUP_VALUE_HIGH_EXTRA_TERM = 7;
constexpr u8 MT_CONST_ADDR_LOW = 64;
constexpr u8 MT_CONST_ADDR_LOW_OFFSET = 65;
constexpr u8 MT_CONST_ADDR_LOW_DYN_COEFF = 66;
constexpr u8 MT_CONST_TS_LOW_OFFSET = 67;
constexpr u8 MT_CONST_ADDR_HIGH = 68;
// perm-challenge role indices (cs constants.rs).
constexpr u32 R_PERM_ADDR_LOW = 0;
constexpr u32 R_PERM_ADDR_HIGH = 1;
constexpr u32 R_PERM_TS_LOW = 2;
constexpr u32 R_PERM_TS_HIGH = 3;
constexpr u32 R_PERM_VAL_LOW = 4;
constexpr u32 R_PERM_VAL_HIGH = 5;

// `challenge_scalars` layout (a single device e4[8], so the kernel-arg struct
// stays pointers+u32 only — no inline __align__(16) fields to match in Rust):
//   [0]      = gamma (lookup additive shift)
//   [1+role] = perm_challenges[role]  (role 0..5)
//   [7]      = perm_additive (memory-tuple seed)
constexpr u32 CS_GAMMA = 0;
constexpr u32 CS_PERM_BASE = 1;
constexpr u32 CS_PERM_ADDITIVE = 7;

// ABI mirror — keep field-for-field with InterpDesc2 in
// bench_interp/interp_v2_gpu.rs (Rust upload assembles this).
struct interp_desc2 {
  // Program lane stream in global memory (null for the LDC variant).
  const u16 *program_ldg;
  u32 program_lanes; // decode must consume exactly this many lanes
  u32 n_instr;

  // Matrix-slot columns. Flat pointer table indexed by `col_base[slot] + col`;
  // entry = device base of that column (bf 4B / e4 16B by slot field); a null
  // entry for an (slot,col) the program references is a hard error.
  const void *const *columns;
  const u32 *col_base; // per-slot prefix offset; len n_matrix_slots + 1
  u32 slot_is_e4;      // bitset over slots (<= 16): 1 = e4-field backing
  u32 n_matrix_slots;

  // Const banks.
  const bf *consts;          // LdcSub::Const, Montgomery
  const e4 *const_challenge; // LdcSub::ConstChallenge; [k] = alpha^k (k>0)
  u32 n_const_challenge;
  const e4 *arg_challenge; // LdcSub::ArgChallenge raw bank
  u32 n_arg_challenge;
  // e4[8]: [0] gamma, [1+role] perm_challenges, [7] perm_additive (CS_* above).
  const e4 *challenge_scalars;

  // Gather descriptors (indexed by the Indirect `desc` lane).
  u32 n_descs;
  const u8 *desc_kind;
  u32 desc_field_e4;              // bitset over descs: 1 = e4 value field
  const void *const *desc_n;      // value table base per desc
  const u32 *const *desc_mapping; // per-row mapping per desc (null if none)
  const u32 *desc_n_len;          // length guard per desc (0xFFFFFFFF = none)
  const bf *const *desc_mask;     // decoder predicate mask per desc (null=none)
  const u32 *desc_fill_alpha;     // decoder fill alpha-power index per desc
  const u32 *desc_table_id;       // decoder fill table id per desc

  // Materialize outputs. Flat (slot,col) table like `columns`; null = the
  // (slot,col) is never materialized by this program. Element width by slot.
  void *const *out_columns;
  const u32 *out_base;
  u32 out_is_e4;

  u32 budget_cells; // per-thread bf cells; dyn smem = budget*4*blockDim.x
  u32 count;        // rows
  u32 *error_flag;
};

// Read lane `i` from the program (LDC = __constant__, LDG = global).
template <bool LDC> DEVICE_FORCEINLINE u16 v2_lane(const interp_desc2 &d, const u32 i) {
  if constexpr (LDC)
    return ab_gkr_bench_program[i];
  else
    return d.program_ldg[i];
}

DEVICE_FORCEINLINE bool slot_e4(const interp_desc2 &d, const u32 slot) { return ((d.slot_is_e4 >> slot) & 1u) != 0; }
DEVICE_FORCEINLINE bool out_slot_e4(const interp_desc2 &d, const u32 slot) { return ((d.out_is_e4 >> slot) & 1u) != 0; }
DEVICE_FORCEINLINE bool desc_e4(const interp_desc2 &d, const u32 desc) { return ((d.desc_field_e4 >> desc) & 1u) != 0; }

// Load a matrix-slot column value at this row (Affine read).
DEVICE_FORCEINLINE e4 load_affine(const interp_desc2 &d, const u32 slot, const u32 col, const unsigned gid, u32 &err) {
  const void *ptr = d.columns[d.col_base[slot] + col];
  if (ptr == nullptr) {
    err |= INTERP2_ERR_NULL_COLUMN;
    return e4::ZERO();
  }
  return slot_e4(d, slot) ? flat_fwd_load_ext<e4>(ptr, gid) : e4::from_scalar(flat_fwd_load_bf(ptr, gid));
}

DEVICE_FORCEINLINE e4 read_ldc(const interp_desc2 &d, const u32 sub, const u32 idx) {
  switch (sub) {
  case LDC_CONST:
    return e4::from_scalar(d.consts[idx]);
  case LDC_CONST_CHALLENGE:
    return d.const_challenge[idx];
  case LDC_ARG_CHALLENGE:
    return d.arg_challenge[idx];
  default: // LDC_SPECIAL
    if (idx == SPECIAL_ZERO)
      return e4::ZERO();
    if (idx == SPECIAL_ONE)
      return e4::ONE();
    // SPECIAL_NEG_ONE
    return e4::sub(e4::ZERO(), e4::ONE());
  }
}

// e4 = 4 consecutive cell INDICES (blockDim.x-strided), matching write_cells.
DEVICE_FORCEINLINE e4 read_cell(bf *cell_base, const u32 cell, const bool is_e4) {
  if (is_e4) {
    const bf limbs[4] = {cell_base[cell * blockDim.x], cell_base[(cell + 1) * blockDim.x], cell_base[(cell + 2) * blockDim.x],
                         cell_base[(cell + 3) * blockDim.x]};
    return e4(limbs);
  }
  return e4::from_scalar(cell_base[cell * blockDim.x]);
}
DEVICE_FORCEINLINE void write_cell(bf *cell_base, const u32 cell, const bool is_e4, const e4 v) {
  cell_base[cell * blockDim.x] = v.base_coefficient_from_flat_idx(0);
  if (is_e4) {
    cell_base[(cell + 1) * blockDim.x] = v.base_coefficient_from_flat_idx(1);
    cell_base[(cell + 2) * blockDim.x] = v.base_coefficient_from_flat_idx(2);
    cell_base[(cell + 3) * blockDim.x] = v.base_coefficient_from_flat_idx(3);
  }
}

// resolve_gather mirror (interp_v2.rs resolve_gather).
DEVICE_FORCEINLINE e4 resolve_gather(const interp_desc2 &d, const u32 desc, const unsigned gid) {
  const u8 kind = d.desc_kind[desc];
  const bool is_e4 = desc_e4(d, desc);
  const void *table = d.desc_n[desc];
  auto load_at = [&](const u32 row) -> e4 {
    return is_e4 ? reinterpret_cast<const e4 *>(table)[row] : e4::from_scalar(reinterpret_cast<const bf *>(table)[row]);
  };
  switch (kind) {
  case GK_MAPPED_VIRTUAL_BF:
  case GK_MAPPED_GENERIC_E4: {
    const u32 row = d.desc_mapping[desc][gid];
    return load_at(row);
  }
  case GK_DECODER_MAPPED_E4: {
    const u32 row = d.desc_mapping[desc][gid];
    const e4 mapped = load_at(row);
    const bf *mask = d.desc_mask[desc];
    if (mask != nullptr && mask[gid].limb == 0) {
      // fill = alpha^fill_alpha_power * table_id  (recomputed, interp_v2.rs:276)
      e4 fill = d.const_challenge[d.desc_fill_alpha[desc]];
      return e4::mul(fill, bf(d.desc_table_id[desc]));
    }
    return mapped;
  }
  case GK_ROW_INDEXED_SETUP_E4: {
    const u32 len = d.desc_n_len[desc];
    if (len != 0xFFFFFFFFu && gid >= len)
      return e4::ZERO();
    return load_at(gid);
  }
  default: // GK_INITS_TEARDOWNS_HIGH_ADDR: per-set, row-independent scalar (row 0)
    return load_at(0);
  }
}

// Read one operand lane (already-fetched `l`) to an e4 value.
DEVICE_FORCEINLINE e4 read_operand(const interp_desc2 &d, bf *cell_base, const unsigned gid, const u16 l, u32 &err) {
  switch (l & 0b11) {
  case 0b00: { // Affine { slot, col }
    const u32 slot = (l >> 2) & 0xF;
    const u32 col = l >> 6;
    return load_affine(d, slot, col, gid, err);
  }
  case 0b01: { // Slot { e4, cell }
    const bool is_e4 = ((l >> 2) & 1) != 0;
    const u32 cell = l >> 3;
    return read_cell(cell_base, cell, is_e4);
  }
  case 0b10: { // Ldc { sub, idx }
    const u32 sub = (l >> 2) & 0b11;
    const u32 idx = l >> 4;
    return read_ldc(d, sub, idx);
  }
  default: { // 0b11 Indirect { e4, desc }
    const u32 desc = l >> 3;
    return resolve_gather(d, desc, gid);
  }
  }
}

DEVICE_FORCEINLINE e4 sh(const interp_desc2 &d, const e4 x) { return e4::add(x, d.challenge_scalars[CS_GAMMA]); }

// perm-challenge role for a memory-tuple TERM slot (perm_role_for_memtup_term).
DEVICE_FORCEINLINE u32 perm_role_for_term(const u8 term) {
  switch (term) {
  case 0:
    return R_PERM_ADDR_LOW;
  case 1:
    return R_PERM_ADDR_HIGH;
  case 2:
    return R_PERM_TS_LOW;
  case 3:
    return R_PERM_TS_HIGH;
  case 4:
    return R_PERM_VAL_LOW;
  default:
    return R_PERM_VAL_HIGH; // term 6
  }
}

// Decode + evaluate ONE memory-tuple block at `pos` (mirror decode_memtup +
// tuple_value). `n_roles` is the role count (header n_operands for single-tuple
// routines; the block's own leading lane for two-tuple routines). Advances pos.
// Residency-templated so the LDC/LDG lane source is a compile-time constant.
template <bool LDC> DEVICE_FORCEINLINE e4 eval_memtup_t(const interp_desc2 &d, bf *cell_base, const unsigned gid, u32 &pos, const u32 n_roles, u32 &err) {
#define LANE(i) v2_lane<LDC>(d, (i))
  e4 acc = d.challenge_scalars[CS_PERM_ADDITIVE];
  const u32 as_arm = LANE(pos) & 0x3;
  pos += 1;

  // roles: n_roles (role, operand) pairs.
  // Collect into local arrays so the as_payload + consts ordering matches
  // decode_memtup (roles, then optional payload, then consts block).
  // n_roles <= 8 (encode asserts).
  u8 role_tag[8];
  u16 role_lane[8];
  for (u32 r = 0; r < n_roles; r++) {
    role_tag[r] = (u8)(LANE(pos) & 0xFF);
    pos += 1;
    role_lane[r] = LANE(pos);
    pos += 1;
  }

  // as_payload (present iff as_arm != 0).
  e4 payload = e4::ZERO();
  bool have_payload = (as_arm != 0);
  if (have_payload) {
    payload = read_operand(d, cell_base, gid, LANE(pos), err);
    pos += 1;
  }

  // consts block: count lane, then (role, operand) pairs.
  const u32 n_consts = LANE(pos);
  pos += 1;
  u8 const_tag[16];
  u16 const_lane[16];
  for (u32 c = 0; c < n_consts; c++) {
    const_tag[c] = (u8)(LANE(pos) & 0xFF);
    pos += 1;
    const_lane[c] = LANE(pos);
    pos += 1;
  }

  // --- value (tuple_value) ---
  // address-space arm.
  switch (as_arm) {
  case 0:
    break; // Empty
  case 1:
    acc = e4::add(acc, payload);
    break; // Constant: + c
  case 2:
    acc = e4::add(e4::sub(acc, payload), bf::ONE());
    break; // IsRegister: + (1 - col)
  case 3:
    acc = e4::add(acc, payload);
    break; // IsRam: + col
  default:
    err |= INTERP2_ERR_BAD_ASARM;
    break;
  }

  // pre-scan consts for the special-indirect dyn-offset coefficient.
  e4 dyn_coeff = e4::ZERO();
  bool have_dyn = false;
  for (u32 c = 0; c < n_consts; c++) {
    if (const_tag[c] == MT_CONST_ADDR_LOW_DYN_COEFF) {
      dyn_coeff = read_operand(d, cell_base, gid, const_lane[c], err);
      have_dyn = true;
    }
  }

  // dynamic role-tagged linear terms: acc += chal(role) * col.
  for (u32 r = 0; r < n_roles; r++) {
    const e4 col = read_operand(d, cell_base, gid, role_lane[r], err);
    e4 chal;
    if (role_tag[r] == MEMTUP_VALUE_HIGH_EXTRA_TERM) {
      chal = e4::mul(d.challenge_scalars[CS_PERM_BASE + R_PERM_ADDR_LOW], have_dyn ? dyn_coeff : e4::ZERO());
    } else {
      chal = d.challenge_scalars[CS_PERM_BASE + perm_role_for_term(role_tag[r])];
    }
    acc = e4::add(acc, e4::mul(chal, col));
  }

  // folded-constant terms: acc += chal(role) * value (dyn-coeff already used).
  for (u32 c = 0; c < n_consts; c++) {
    const u8 role = const_tag[c];
    if (role == MT_CONST_ADDR_LOW_DYN_COEFF)
      continue;
    u32 chal_role;
    if (role == MT_CONST_ADDR_LOW || role == MT_CONST_ADDR_LOW_OFFSET)
      chal_role = R_PERM_ADDR_LOW;
    else if (role == MT_CONST_TS_LOW_OFFSET)
      chal_role = R_PERM_TS_LOW;
    else // MT_CONST_ADDR_HIGH
      chal_role = R_PERM_ADDR_HIGH;
    const e4 val = read_operand(d, cell_base, gid, const_lane[c], err);
    acc = e4::add(acc, e4::mul(d.challenge_scalars[CS_PERM_BASE + chal_role], val));
  }
  return acc;
#undef LANE
}

template <bool LDC> DEVICE_FORCEINLINE void interp2_body(const interp_desc2 d) {
#define LANE(i) v2_lane<LDC>(d, (i))
  extern __shared__ u32 interp2_smem[];
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= d.count)
    return;
  bf *cell_base = reinterpret_cast<bf *>(interp2_smem) + threadIdx.x;
  for (u32 c = 0; c < d.budget_cells; c++)
    cell_base[c * blockDim.x] = bf::ZERO();

  u32 i = 0; // lane cursor (warp-uniform)
  u32 err = 0;

  for (u32 k = 0; k < d.n_instr && err == 0; k++) {
    const u16 h = LANE(i++);
    // out[0..2] hold up to two routine outputs (num/den); single value in out0.
    e4 out0 = e4::ZERO();
    e4 out1 = e4::ZERO();
    u32 n_out = 1;

    if ((h & 1) == 0) {
      // --- Arith: op:2 (bits1-2), arity:7 (bits3-9). ---
      const u32 op = (h >> 1) & 0b11;
      const u32 arity = (h >> 3) & 0x7F;
      switch (op) {
      case 0: { // Sum
        e4 a = e4::ZERO();
        for (u32 t = 0; t < arity; t++)
          a = e4::add(a, read_operand(d, cell_base, gid, LANE(i++), err));
        out0 = a;
        break;
      }
      case 1: { // Prod
        e4 a = e4::ONE();
        for (u32 t = 0; t < arity; t++)
          a = e4::mul(a, read_operand(d, cell_base, gid, LANE(i++), err));
        out0 = a;
        break;
      }
      case 2: { // Dot: arity pairs, accumulate operands[2t]*operands[2t+1]
        e4 a = e4::ZERO();
        for (u32 t = 0; t < arity; t++) {
          const e4 x = read_operand(d, cell_base, gid, LANE(i++), err);
          const e4 y = read_operand(d, cell_base, gid, LANE(i++), err);
          a = e4::add(a, e4::mul(x, y));
        }
        out0 = a;
        break;
      }
      default: // Fma — not emitted by the v2 compiler (interp_v2 todo!)
        err |= INTERP2_ERR_UNSUPPORTED_ROUTINE;
        break;
      }
    } else {
      // --- Macro: routine:7 (bits1-7), n_operands:7 (bits8-14). ---
      const u32 routine = (h >> 1) & 0x7F;
      const u32 n_operands = (h >> 8) & 0x7F;

      // helper to read operand k of a plain macro at cursor.
      auto plain = [&](const u32 idx) -> e4 { return read_operand(d, cell_base, gid, LANE(i + idx), err); };

      switch (routine) {
      case R_GATE_OUTPUT_FOLD: { // acc = sum_k alpha^k * col_k (alpha^0 = 1)
        e4 a = e4::ZERO();
        for (u32 t = 0; t < n_operands; t++) {
          const e4 col = plain(t);
          a = (t == 0) ? e4::add(a, col) : e4::add(a, e4::mul(col, d.const_challenge[t]));
        }
        i += n_operands;
        out0 = a;
        break;
      }
      case R_PRODUCT: { // a * b
        out0 = e4::mul(plain(0), plain(1));
        i += n_operands;
        break;
      }
      case R_MASK_IDENTITY: { // (v-1)*m + 1
        const e4 v = plain(0);
        const e4 m = plain(1);
        out0 = e4::add(e4::mul(e4::sub(v, e4::ONE()), m), e4::ONE());
        i += n_operands;
        break;
      }
      case R_AGGREGATE_LOOKUP_PAIR: { // num = a*d + c*b, den = b*d
        const e4 a = plain(0), b = plain(1), c = plain(2), dd = plain(3);
        out0 = e4::add(e4::mul(a, dd), e4::mul(c, b));
        out1 = e4::mul(b, dd);
        n_out = 2;
        i += n_operands;
        break;
      }
      case R_LOOKUP_BASE_PAIR:
      case R_LOOKUP_EXT_PAIR: { // num = sh(b)+sh(d), den = sh(b)*sh(d)
        const e4 b = sh(d, plain(0));
        const e4 dd = sh(d, plain(1));
        out0 = e4::add(b, dd);
        out1 = e4::mul(b, dd);
        n_out = 2;
        i += n_operands;
        break;
      }
      case R_LOOKUP_BASE_MINUS_MULT:
      case R_LOOKUP_EXT_MINUS_MULT: { // num = sh(d) - c*sh(b), den = sh(b)*sh(d)
        const e4 b = sh(d, plain(0));
        const e4 c = plain(1);
        const e4 dd = sh(d, plain(2));
        out0 = e4::sub(dd, e4::mul(c, b));
        out1 = e4::mul(b, dd);
        n_out = 2;
        i += n_operands;
        break;
      }
      case R_LOOKUP_CACHED_DENS:
      case R_LOOKUP_DECODER_DENS_SETUP: { // num = a*sh(d) - c*sh(b), den = sh(b)*sh(d)
        const e4 a = plain(0);
        const e4 b = sh(d, plain(1));
        const e4 c = plain(2);
        const e4 dd = sh(d, plain(3));
        out0 = e4::sub(e4::mul(a, dd), e4::mul(c, b));
        out1 = e4::mul(b, dd);
        n_out = 2;
        i += n_operands;
        break;
      }
      case R_LOOKUP_UNBALANCED_BASE:
      case R_LOOKUP_UNBALANCED_EXT: { // num = a*sh(d) + b, den = b*sh(d)
        const e4 a = plain(0);
        const e4 b = plain(1);
        const e4 dd = sh(d, plain(2));
        out0 = e4::add(e4::mul(a, dd), b);
        out1 = e4::mul(b, dd);
        n_out = 2;
        i += n_operands;
        break;
      }
      case R_VECTOR_LOOKUP_GATE:
      case R_VECTORIZED_LOOKUP: { // sum_k alpha^k * (const_k + sum coeff*col)
        e4 acc = e4::ZERO();
        u32 p = 0;     // operand cursor within this instr's operand region
        u32 col_k = 0; // column ordinal == alpha-power index
        while (p < n_operands) {
          // term_count lane VALUE (base scalar in low limb).
          const e4 tc = read_operand(d, cell_base, gid, LANE(i + p), err);
          p += 1;
          const u32 term_count = bf::into_canonical_u32(tc.base_coefficient_from_flat_idx(0));
          e4 col_val = read_operand(d, cell_base, gid, LANE(i + p), err); // const_k
          p += 1;
          for (u32 t = 0; t < term_count; t++) {
            const e4 coeff = read_operand(d, cell_base, gid, LANE(i + p), err);
            const e4 col = read_operand(d, cell_base, gid, LANE(i + p + 1), err);
            col_val = e4::add(col_val, e4::mul(coeff, col));
            p += 2;
          }
          acc = (col_k == 0) ? e4::add(acc, col_val) : e4::add(acc, e4::mul(col_val, d.const_challenge[col_k]));
          col_k += 1;
        }
        i += n_operands;
        out0 = acc;
        break;
      }
      case R_MATERIALIZE_SINGLE_LOOKUP:
      case R_SINGLE_COLUMN_LOOKUP: { // const + sum_j coeff_j * col_j
        e4 acc = plain(0);
        u32 j = 1;
        while (j < n_operands) {
          acc = e4::add(acc, e4::mul(plain(j), plain(j + 1)));
          j += 2;
        }
        i += n_operands;
        out0 = acc;
        break;
      }
      case R_VECTORIZED_LOOKUP_SETUP: { // single RowIndexedSetupE4 gather
        out0 = plain(0);
        i += n_operands;
        break;
      }
      case R_MATERIALIZE_GRAND_PRODUCT_TERM:
      case R_MEMORY_TUPLE: { // single memory tuple
        // single-tuple: primary role count = header n_operands.
        out0 = eval_memtup_t<LDC>(d, cell_base, gid, i, n_operands, err);
        // presence lane for memtup2 (always emitted; 0 for single-tuple).
        const u32 has_two = LANE(i++);
        if (has_two) {
          // Shouldn't happen for single-tuple routines; consume defensively.
          const u32 n2 = LANE(i++);
          (void)eval_memtup_t<LDC>(d, cell_base, gid, i, n2, err);
        }
        break;
      }
      case R_GRAND_PRODUCT_WITHOUT_CACHES:
      case R_MEMORY_INIT_TEARDOWN_PAIR: { // tuple(t0) * tuple(t1)
        // two-tuple: primary role count rides a leading lane.
        const u32 n_roles0 = LANE(i++);
        const e4 t0 = eval_memtup_t<LDC>(d, cell_base, gid, i, n_roles0, err);
        const u32 has_two = LANE(i++);
        e4 t1 = e4::ONE();
        if (has_two) {
          const u32 n_roles1 = LANE(i++);
          t1 = eval_memtup_t<LDC>(d, cell_base, gid, i, n_roles1, err);
        }
        out0 = e4::mul(t0, t1);
        break;
      }
      default:
        err |= INTERP2_ERR_UNSUPPORTED_ROUTINE;
        break;
      }
    }

    if (err)
      break;

    // --- footer dsts ---
    // n_out values map to n_dst footer lanes (broadcast when n_out == 1).
    // The footer count equals the routine output_count (1 or 2); arith = 1.
    const u32 n_dst = n_out;
    for (u32 dj = 0; dj < n_dst; dj++) {
      const u16 dl = LANE(i++);
      const e4 v = (dj == 0) ? out0 : out1;
      if ((dl & 1) == 0) {
        // Dst::Slot { e4, cell }
        const bool is_e4 = ((dl >> 1) & 1) != 0;
        const u32 cell = dl >> 2;
        write_cell(cell_base, cell, is_e4, v);
      } else {
        // Dst::Materialize { slot, col }
        const u32 slot = (dl >> 1) & 0xF;
        const u32 col = dl >> 5;
        void *ptr = d.out_columns[d.out_base[slot] + col];
        if (ptr == nullptr) {
          err |= INTERP2_ERR_NULL_COLUMN;
          break;
        }
        if (out_slot_e4(d, slot))
          store<e4, st_modifier::cs>(reinterpret_cast<e4 *>(ptr), v, gid);
        else
          store<bf, st_modifier::cs>(reinterpret_cast<bf *>(ptr), v.base_coefficient_from_flat_idx(0), gid);
      }
    }
  }

  if (err == 0 && i != d.program_lanes)
    err |= INTERP2_ERR_TRAILING_LANES;
  if (err != 0)
    atomicOr(d.error_flag, err);
#undef LANE
}

EXTERN __launch_bounds__(128, 4) __global__ void ab_gkr_bench_fwd_interp_v2_ldg_kernel(const interp_desc2 desc) { interp2_body<false>(desc); }
EXTERN __launch_bounds__(128, 4) __global__ void ab_gkr_bench_fwd_interp_v2_ldc_kernel(const interp_desc2 desc) { interp2_body<true>(desc); }
EXTERN __launch_bounds__(256, 2) __global__ void ab_gkr_bench_fwd_interp_v2_ldg256_kernel(const interp_desc2 desc) { interp2_body<false>(desc); }
EXTERN __launch_bounds__(256, 2) __global__ void ab_gkr_bench_fwd_interp_v2_ldc256_kernel(const interp_desc2 desc) { interp2_body<true>(desc); }

} // namespace airbender::prover::gkr::bench
