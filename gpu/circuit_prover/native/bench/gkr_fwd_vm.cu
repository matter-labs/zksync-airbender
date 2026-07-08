// fwd-VM CUDA interpreter (Task 4): a row-per-thread interpreter over the
// gkr_eval_isa fwd-VM 16-bit-lane wire format (`gkr_eval_isa::fwd::encode`).
// One thread = one row (`gid`), a SINGLE e4 accumulator in registers, and a
// per-thread bf cell file in dynamic shared memory (`budget` u32 lanes,
// interleaved `smem[c * blockDim.x + threadIdx.x]`; Base = 1 lane, Ext = 4
// lanes 4-aligned, `gkr_eval_isa/src/fwd/compile/place.rs`).
//
// Semantics mirror the CPU golden model `gkr_eval_isa::fwd::interp::
// interpret_layer_row_impl` (interp.rs:59-107): Add accumulates +/- per the
// header sign; Mul multiply-accumulates with the unary `Mul Special(NegOne)`
// = negate special case; Fma accumulates +/- sum of L*R pairs (canonical
// (Base,Ext) mixed order only); Mov has 3 directions (AccFromSrc /
// DstFromAcc / DstFromSrc). Special operands mirror the four peek legs the
// G-CPU gate validated (`bench_interp/fwd_vm/resolvers.rs::peek`).
//
// Fail-closed (codex plan-F3): any OOB Ldc/column/bank/special index, bad
// header, or null pointer atomicOr's an FWDVM_ERR_* bit into
// `desc.error_flag` and bails; the host asserts the flag is 0 after launch.
//
// ABI mirror: `bench_interp::fwd_vm::lower::InterpDesc3` (keep
// field-for-field). Compiled only under -DAB_GKR_BENCH (feature `bench`).

#include "../prover/gkr/forward/flat.cuh"

// The LDC variant REUSES the v1 bench program __constant__ array (defined in
// gkr_fwd_interp.cu, uploaded by Rust `upload_bench_program_to_constant`).
// The 64 KB __constant__ budget has no room for another 28 KB array, and the
// bench variants never run concurrently, so they share one upload slot.
extern __constant__ u16 ab_gkr_bench_program[14336];

namespace airbender::prover::gkr::bench {

// --- error bits (atomicOr'd into desc.error_flag; 0 = clean) -----------------
constexpr u32 FWDVM_ERR_TRAILING_LANES = 1; // decode != program_lanes
constexpr u32 FWDVM_ERR_BAD_HEADER = 2;     // reserved bits set / bad Mov dir / zero arity
constexpr u32 FWDVM_ERR_COL_OOB = 4;        // col >= col_base[slot+1]-col_base[slot]
constexpr u32 FWDVM_ERR_NULL_COLUMN = 8;    // read/write column entry is null
constexpr u32 FWDVM_ERR_LDC_OOB = 16;       // Ldc idx >= its bank length
constexpr u32 FWDVM_ERR_BAD_SPECIAL = 32;   // inline special idx > 2 / desc kind > 4 / bad virtual-setup kind code
constexpr u32 FWDVM_ERR_DESC_OOB = 64;      // Special desc >= n_descs
constexpr u32 FWDVM_ERR_TABLE_OOB = 128;    // mapped lookup index >= table_len
constexpr u32 FWDVM_ERR_CELL_OOB = 256;     // cell + width > budget

// --- operand / dst wire tags (mirror gkr_eval_isa::fwd::encode) --------------
// operand: [payload:14][tag:2]; tag 00=Global{[col:10][slot:4]} 01=Smem{[cell:14]}
//          10=Ldc{[idx:12][sub:2]} 11=Special{[desc:14]}
// dst: [payload][kind:1]; kind 0=Smem{[cell:14]} 1=GlobalMaterialize{[col:10][slot:4]}
constexpr u32 LDC_CONST = 0;
constexpr u32 LDC_CONST_CHALLENGE = 1;
constexpr u32 LDC_ARG_CHALLENGE = 2;
constexpr u32 LDC_SPECIAL = 3;
constexpr u32 SPECIAL_ZERO = 0;
constexpr u32 SPECIAL_ONE = 1;
constexpr u32 SPECIAL_NEG_ONE = 2;

// --- special-descriptor strategy kinds (mirror lower.rs desc_kind) -----------
constexpr u8 SD_SINGLE_COLUMN = 0; // PeekSingleColumn: lift(mapping[row])
constexpr u8 SD_AGGREGATE = 1;     // PeekAggregate: table[mapping[row]]
constexpr u8 SD_SETUP = 2;         // PeekSetup: row < table_len ? table[row] : 0
constexpr u8 SD_DECODER = 3;       // PeekDecoder: mask[row] != 0 ? table[mapping[row]] : fill
constexpr u8 SD_VIRTUAL = 4;       // VirtualSetup: lift(n(kind, gid)); KIND_ORDER code in desc_param[desc]

// ABI mirror — keep field-for-field with InterpDesc3 in
// bench_interp/fwd_vm/lower.rs (Rust upload assembles this).
struct interp_desc3 {
  // program
  const u16 *program_ldg; // null when LDC
  u32 program_lanes;
  u32 n_instr;
  // per-(slot,col) column table: entry for (slot,col) is col_base[slot] + col;
  // col_base[16] is the end sentinel (total). The kernel bounds-checks
  // col < col_base[slot+1] - col_base[slot] and errors instead of reading a
  // neighbor slot's region.
  u32 col_base[17];
  const void *const *col_read_ptr;
  const u8 *col_is_e4;        // 0 = bf column, 1 = e4 column
  void *const *col_write_ptr; // null unless (slot,col) materialized this layer
  // banks — lengths REQUIRED: fail closed on an out-of-range Ldc index.
  const bf *consts; // Montgomery
  u32 n_consts;
  const e4 *const_challenge;
  u32 n_const_challenge;
  const e4 *arg_challenge;
  u32 n_arg_challenge;
  // specials (parallel arrays; value channel is e4)
  u32 n_descs;
  const u8 *desc_kind; // SD_* above
  const u32 *const *desc_mapping;
  const e4 *const *desc_table;
  const u32 *desc_table_len;
  const bf *const *desc_mask;
  const e4 *desc_fill;
  const u32 *desc_param; // width/set params + SD_VIRTUAL kind code (KIND_ORDER index)
  // smem-rooted outputs written in the epilogue
  u32 n_outs;
  const u16 *out_cell;
  void *const *out_ptr;
  const u8 *out_is_e4;
  // geometry
  u32 budget; // per-thread bf cell lanes; dyn smem = budget * 4 * blockDim.x
  u32 count;  // rows
  u32 *error_flag;
};

static_assert(sizeof(interp_desc3) == 264, "InterpDesc3/interp_desc3 ABI size drift");

// Read lane `i` from the program (LDC = __constant__, LDG = global).
template <bool LDC> DEVICE_FORCEINLINE u16 vm_lane(const interp_desc3 &d, const u32 i) {
  if constexpr (LDC)
    return ab_gkr_bench_program[i];
  else
    return d.program_ldg[i];
}

// e4 = 4 consecutive cell indices (blockDim.x-strided), 4-aligned by the
// compiler's placement (place.rs); bf = 1 lane.
DEVICE_FORCEINLINE e4 read_cells(const bf *cell_base, const u32 cell, const bool is_e4) {
  if (is_e4) {
    const bf limbs[4] = {cell_base[cell * blockDim.x], cell_base[(cell + 1) * blockDim.x], cell_base[(cell + 2) * blockDim.x],
                         cell_base[(cell + 3) * blockDim.x]};
    return e4(limbs);
  }
  return e4::from_scalar(cell_base[cell * blockDim.x]);
}

DEVICE_FORCEINLINE void write_cells(bf *cell_base, const u32 cell, const bool is_e4, const e4 v) {
  cell_base[cell * blockDim.x] = v.base_coefficient_from_flat_idx(0);
  if (is_e4) {
    cell_base[(cell + 1) * blockDim.x] = v.base_coefficient_from_flat_idx(1);
    cell_base[(cell + 2) * blockDim.x] = v.base_coefficient_from_flat_idx(2);
    cell_base[(cell + 3) * blockDim.x] = v.base_coefficient_from_flat_idx(3);
  }
}

// Global{slot,col} read: column entry at col_base[slot] + col, width per
// col_is_e4 (bf lifted to e4). Materialized (slot,col)s read the interp-owned
// overlay column their own GlobalMaterialize write produced (read-before-write
// is statically excluded by the lowering, lower.rs::assert_read_before_write).
DEVICE_FORCEINLINE e4 load_global(const interp_desc3 &d, const u32 slot, const u32 col, const unsigned gid, u32 &err) {
  const u32 base = d.col_base[slot];
  if (col >= d.col_base[slot + 1] - base) {
    err |= FWDVM_ERR_COL_OOB;
    return e4::ZERO();
  }
  const u32 entry = base + col;
  const void *ptr = d.col_read_ptr[entry];
  if (ptr == nullptr) {
    err |= FWDVM_ERR_NULL_COLUMN;
    return e4::ZERO();
  }
  if (d.col_is_e4[entry] != 0)
    return load<e4, ld_modifier::ca>(reinterpret_cast<const e4 *>(ptr), gid);
  return e4::from_scalar(load<bf, ld_modifier::ca>(reinterpret_cast<const bf *>(ptr), gid));
}

// Ldc{sub,idx}: consts / challenge banks / inline specials. Fail closed on an
// out-of-range index (mirrors ConstBank::get / ChallengeBanks::get bounds and
// the interp UnknownConst/UnknownChallenge/MalformedInstr errors).
DEVICE_FORCEINLINE e4 read_ldc(const interp_desc3 &d, const u32 sub, const u32 idx, u32 &err) {
  switch (sub) {
  case LDC_CONST:
    if (idx >= d.n_consts) {
      err |= FWDVM_ERR_LDC_OOB;
      return e4::ZERO();
    }
    return e4::from_scalar(d.consts[idx]);
  case LDC_CONST_CHALLENGE:
    if (idx >= d.n_const_challenge) {
      err |= FWDVM_ERR_LDC_OOB;
      return e4::ZERO();
    }
    return d.const_challenge[idx];
  case LDC_ARG_CHALLENGE:
    if (idx >= d.n_arg_challenge) {
      err |= FWDVM_ERR_LDC_OOB;
      return e4::ZERO();
    }
    return d.arg_challenge[idx];
  default: // LDC_SPECIAL: constructed constants, no memory
    if (idx == SPECIAL_ZERO)
      return e4::ZERO();
    if (idx == SPECIAL_ONE)
      return e4::ONE();
    if (idx == SPECIAL_NEG_ONE)
      return e4::sub(e4::ZERO(), e4::ONE());
    err |= FWDVM_ERR_BAD_SPECIAL;
    return e4::ZERO();
  }
}

// KIND_ORDER (gkr_eval_isa::fwd::source) index -> gkr_base_source_kind, the SAME
// enum the flat forward codegen feeds `gkr_virtual_base_value` (the shared `n()`).
// KIND_ORDER is the single source of truth (mirrored on the Rust side by
// `virtual_setup_kind_code`; drift-guarded in fwd_vm/lower.rs). This switch tracks
// it explicitly, so a future 5th kind fails visibly rather than misrouting.
// Callers MUST fail-closed on codes >= KIND_ORDER.len() (== 4) before dispatching.
DEVICE_FORCEINLINE gkr_base_source_kind virtual_kind_from_code(const u32 code) {
  switch (code) {
  case 0: // RangeCheck16Bits
    return GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS;
  case 1: // RangeCheckTimestamp
    return GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_TIMESTAMP;
  case 2: // InitsAndTeardownsLow
    return GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_LOW;
  default: // 3: InitsAndTeardownsHigh (caller guarantees code < 4)
    return GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_HIGH;
  }
}

// Special{desc}: the four peek legs + VirtualSetup, mirroring resolvers.rs::peek
// exactly (the G-CPU-validated single reference). Values are e4.
DEVICE_FORCEINLINE e4 read_special(const interp_desc3 &d, const u32 desc, const unsigned gid, u32 &err) {
  if (desc >= d.n_descs) {
    err |= FWDVM_ERR_DESC_OOB;
    return e4::ZERO();
  }
  switch (d.desc_kind[desc]) {
  case SD_SINGLE_COLUMN: {
    // lift(Bf::from_u32_with_reduction(mapping[row])) — the mapping value is a
    // raw index, so it enters the field via the Montgomery conversion.
    const u32 idx = load<u32, ld_modifier::ca>(d.desc_mapping[desc], gid);
    return e4::from_scalar(bf::from_u32_with_reduction(idx));
  }
  case SD_AGGREGATE: {
    const u32 row = load<u32, ld_modifier::ca>(d.desc_mapping[desc], gid);
    if (row >= d.desc_table_len[desc]) {
      err |= FWDVM_ERR_TABLE_OOB;
      return e4::ZERO();
    }
    return load<e4, ld_modifier::ca>(d.desc_table[desc], row);
  }
  case SD_SETUP:
    // Zero-padded tail past the real table length.
    return gid < d.desc_table_len[desc] ? load<e4, ld_modifier::ca>(d.desc_table[desc], gid) : e4::ZERO();
  case SD_DECODER: {
    const bf mask = load<bf, ld_modifier::ca>(d.desc_mask[desc], gid);
    if (mask.limb == 0)
      return d.desc_fill[desc];
    const u32 row = load<u32, ld_modifier::ca>(d.desc_mapping[desc], gid);
    if (row >= d.desc_table_len[desc]) {
      err |= FWDVM_ERR_TABLE_OOB;
      return e4::ZERO();
    }
    return load<e4, ld_modifier::ca>(d.desc_table[desc], row);
  }
  case SD_VIRTUAL: {
    // VirtualSetup: resolver-computed, reads NO memory. The kind rides desc_param
    // as a KIND_ORDER code (0..3). Fail closed on a bad code — `gkr_virtual_base_value`
    // returns 0 for an unknown kind, which would silently corrupt instead of erroring.
    const u32 code = d.desc_param[desc];
    if (code >= 4) { // KIND_ORDER.len()
      err |= FWDVM_ERR_BAD_SPECIAL;
      return e4::ZERO();
    }
    return e4::from_scalar(gkr_virtual_base_value(virtual_kind_from_code(code), gid));
  }
  default:
    err |= FWDVM_ERR_BAD_SPECIAL;
    return e4::ZERO();
  }
}

// Read one operand lane to an e4 value. `field_e4` is the INSTRUCTION's operand
// field — the Smem tag carries no width bit, so the cell width comes from the
// consuming instruction (interp.rs `instr_operand_fields` convention; for Fma
// the per-side field applies). Global width comes from the column table.
DEVICE_FORCEINLINE e4 read_operand(const interp_desc3 &d, const bf *cell_base, const unsigned gid, const u16 l, const bool field_e4, u32 &err) {
  switch (l & 0b11) {
  case 0b00: { // Global { slot, col }
    const u32 slot = (l >> 2) & 0xF;
    const u32 col = l >> 6;
    return load_global(d, slot, col, gid, err);
  }
  case 0b01: { // Smem { cell }
    const u32 cell = l >> 2;
    if (cell + (field_e4 ? 4u : 1u) > d.budget) {
      err |= FWDVM_ERR_CELL_OOB;
      return e4::ZERO();
    }
    return read_cells(cell_base, cell, field_e4);
  }
  case 0b10: { // Ldc { sub, idx }
    const u32 sub = (l >> 2) & 0b11;
    const u32 idx = l >> 4;
    return read_ldc(d, sub, idx, err);
  }
  default: { // 0b11 Special { desc }
    const u32 desc = l >> 2;
    return read_special(d, desc, gid, err);
  }
  }
}

// Write a dst lane: Smem cells (width per the Mov's field) or GlobalMaterialize
// (interp-owned overlay column; width per the column table entry).
DEVICE_FORCEINLINE void write_dst(const interp_desc3 &d, bf *cell_base, const unsigned gid, const u16 dl, const bool field_e4, const e4 v, u32 &err) {
  if ((dl & 1) == 0) {
    // Smem { cell }
    const u32 cell = dl >> 1;
    if (cell + (field_e4 ? 4u : 1u) > d.budget) {
      err |= FWDVM_ERR_CELL_OOB;
      return;
    }
    write_cells(cell_base, cell, field_e4, v);
  } else {
    // GlobalMaterialize { slot, col }
    const u32 slot = (dl >> 1) & 0xF;
    const u32 col = dl >> 5;
    const u32 base = d.col_base[slot];
    if (col >= d.col_base[slot + 1] - base) {
      err |= FWDVM_ERR_COL_OOB;
      return;
    }
    const u32 entry = base + col;
    void *ptr = d.col_write_ptr[entry];
    if (ptr == nullptr) {
      err |= FWDVM_ERR_NULL_COLUMN;
      return;
    }
    // Plain (default) store: the program legitimately reads this column back
    // later in the same thread (materialize-then-consume), so no streaming hint.
    if (d.col_is_e4[entry] != 0)
      store<e4>(reinterpret_cast<e4 *>(ptr), v, gid);
    else
      store<bf>(reinterpret_cast<bf *>(ptr), v.base_coefficient_from_flat_idx(0), gid);
  }
}

// Core program execution over a pre-zeroed per-thread cell file. Decode mirrors
// `gkr_eval_isa::fwd::encode::decode`; math mirrors `interp.rs:59-107`.
template <bool LDC> DEVICE_FORCEINLINE void vm_core(const interp_desc3 &d, bf *cell_base, const unsigned gid) {
#define LANE(i) vm_lane<LDC>(d, (i))
  u32 i = 0; // lane cursor (warp-uniform)
  u32 err = 0;
  e4 acc = e4::ZERO(); // the single accumulator, persistent across instructions

  for (u32 k = 0; k < d.n_instr && err == 0; k++) {
    const u16 h = LANE(i++);
    const u32 op = h & 0b11;

    if (op == 0b11) {
      // --- Mov: [field:1@4][dir:2@2][op=3:2]; bits 5+ reserved (must be 0). ---
      if ((h >> 5) != 0) {
        err |= FWDVM_ERR_BAD_HEADER;
        break;
      }
      const u32 dir = (h >> 2) & 0b11;
      const bool fe4 = ((h >> 4) & 1) != 0;
      switch (dir) {
      case 0: // AccFromSrc
        acc = read_operand(d, cell_base, gid, LANE(i++), fe4, err);
        break;
      case 1: // DstFromAcc
        write_dst(d, cell_base, gid, LANE(i++), fe4, acc, err);
        break;
      case 2: { // DstFromSrc: dst lane, then src lane (encode.rs order)
        const u16 dl = LANE(i++);
        const e4 v = read_operand(d, cell_base, gid, LANE(i++), fe4, err);
        write_dst(d, cell_base, gid, dl, fe4, v, err);
        break;
      }
      default: // dir 3 reserved
        err |= FWDVM_ERR_BAD_HEADER;
        break;
      }
      continue;
    }

    // --- Arith: [rsvd:3][sign:1@12][promote:1@11][f1:1@10][f0:1@9][arity:7@2][op:2]. ---
    const u32 arity = (h >> 2) & 0x7F;
    const bool f0 = ((h >> 9) & 1) != 0;
    const bool f1 = ((h >> 10) & 1) != 0;
    const bool promote = ((h >> 11) & 1) != 0;
    const bool minus = ((h >> 12) & 1) != 0;
    if (promote || (h >> 13) != 0 || arity == 0) {
      err |= FWDVM_ERR_BAD_HEADER;
      break;
    }

    if (op == 0) {
      // Add: acc +/-= each operand.
      for (u32 t = 0; t < arity; t++) {
        const e4 v = read_operand(d, cell_base, gid, LANE(i++), f0, err);
        acc = minus ? e4::sub(acc, v) : e4::add(acc, v);
      }
    } else if (op == 1) {
      // Mul: unary Mul Special(NegOne) = negate acc (interp.rs:82-91);
      // otherwise acc *= each operand.
      if (arity == 1) {
        const u16 l = LANE(i++);
        if ((l & 0b11) == 0b10 && ((l >> 2) & 0b11) == LDC_SPECIAL && (l >> 4) == SPECIAL_NEG_ONE)
          acc = e4::sub(e4::ZERO(), acc);
        else
          acc = e4::mul(acc, read_operand(d, cell_base, gid, l, f0, err));
      } else {
        for (u32 t = 0; t < arity; t++)
          acc = e4::mul(acc, read_operand(d, cell_base, gid, LANE(i++), f0, err));
      }
    } else {
      // Fma: acc +/-= sum of L*R pairs; per-side operand fields (canonical
      // (Base,Ext) mixed order — encode rejects (Ext,Base)).
      for (u32 t = 0; t < arity; t++) {
        const e4 lv = read_operand(d, cell_base, gid, LANE(i++), f0, err);
        const e4 rv = read_operand(d, cell_base, gid, LANE(i++), f1, err);
        const e4 p = e4::mul(lv, rv);
        acc = minus ? e4::sub(acc, p) : e4::add(acc, p);
      }
    }
  }

  if (err == 0 && i != d.program_lanes)
    err |= FWDVM_ERR_TRAILING_LANES;

  // --- Epilogue: write smem-rooted outputs to their interp-owned columns. ---
  if (err == 0) {
    for (u32 o = 0; o < d.n_outs; o++) {
      const u32 cell = d.out_cell[o];
      const bool is_e4 = d.out_is_e4[o] != 0;
      if (cell + (is_e4 ? 4u : 1u) > d.budget) {
        err |= FWDVM_ERR_CELL_OOB;
        break;
      }
      void *ptr = d.out_ptr[o];
      if (ptr == nullptr) {
        err |= FWDVM_ERR_NULL_COLUMN;
        break;
      }
      const e4 v = read_cells(cell_base, cell, is_e4);
      if (is_e4)
        store<e4, st_modifier::cs>(reinterpret_cast<e4 *>(ptr), v, gid);
      else
        store<bf, st_modifier::cs>(reinterpret_cast<bf *>(ptr), v.base_coefficient_from_flat_idx(0), gid);
    }
  }

  if (err != 0)
    atomicOr(d.error_flag, err);
#undef LANE
}

// Dynamic shared memory: the smem byte count is a launch parameter, so its
// footprint is OPAQUE to ptxas — the compiler cannot fold it into occupancy or
// __launch_bounds__, and real occupancy is silently capped at launch time.
template <bool LDC> DEVICE_FORCEINLINE void vm_body(const interp_desc3 &d) {
  extern __shared__ u32 fwd_vm_smem[];
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= d.count)
    return;
  bf *cell_base = reinterpret_cast<bf *>(fwd_vm_smem) + threadIdx.x;
  for (u32 c = 0; c < d.budget; c++)
    cell_base[c * blockDim.x] = bf::ZERO();
  vm_core<LDC>(d, cell_base, gid);
}

// Static shared memory: N_CELLS is a compile-time constant, so the __shared__
// footprint is visible to ptxas — it feeds the occupancy calculator and the
// __launch_bounds__ register sizing (unlike the dynamic-smem body above). 128
// threads only. Macro pattern: gkr_fwd_interp_v2.cu `interp2_body_static` /
// `INTERP2_STATIC_LDG_KERNEL`. The `d.budget` bounds checks inside `vm_core`
// remain valid: the host asserts `desc.budget == N_CELLS` before launching this
// variant, so the cell file the checks bound against matches the static array.
template <bool LDC, u32 N_CELLS> DEVICE_FORCEINLINE void vm_body_static(const interp_desc3 &d) {
  __shared__ bf fwd_vm_cells_s[N_CELLS * 128];
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= d.count)
    return;
  bf *cell_base = fwd_vm_cells_s + threadIdx.x;
  for (u32 c = 0; c < N_CELLS; c++)
    cell_base[c * 128] = bf::ZERO();
  vm_core<LDC>(d, cell_base, gid);
}

EXTERN __launch_bounds__(128, 4) __global__ void ab_gkr_bench_fwd_vm_ldg_kernel(const __grid_constant__ interp_desc3 desc) { vm_body<false>(desc); }
EXTERN __launch_bounds__(128, 4) __global__ void ab_gkr_bench_fwd_vm_ldc_kernel(const __grid_constant__ interp_desc3 desc) { vm_body<true>(desc); }

// --- Static-smem LDC variant (128 threads, BUDGET=16 only) -----------------
// minBlocks is the occupancy the static smem permits: SM shared capacity
// (~100 KB on sm_120) / per-block footprint (N*128*4 B + ~1 KB driver), clamped
// to the 12-block warp limit (4 warps/block). ptxas then sizes registers to
// that smem-permitted occupancy instead of the dynamic body's hardcoded 4.
// Only the committed budget-16 LDC form is instantiated: every corpus program
// fits the __constant__ array (Task 1 probe: max 10911/14336 lanes), so an s16
// LDC variant is the right static form. Mirrors INTERP2_STATIC_LDG_KERNEL.
#define FWDVM_SMEM_BLOCKS(N) ((102400u / ((N) * 512u + 1024u)) > 12u ? 12u : ((102400u / ((N) * 512u + 1024u)) < 1u ? 1u : (102400u / ((N) * 512u + 1024u))))
#define FWDVM_STATIC_LDC_KERNEL(N)                                                                                                                             \
  EXTERN __launch_bounds__(128, FWDVM_SMEM_BLOCKS(N)) __global__ void ab_gkr_bench_fwd_vm_ldc_s##N##_kernel(const interp_desc3 desc) {                         \
    vm_body_static<true, N>(desc);                                                                                                                             \
  }
FWDVM_STATIC_LDC_KERNEL(16)

} // namespace airbender::prover::gkr::bench
