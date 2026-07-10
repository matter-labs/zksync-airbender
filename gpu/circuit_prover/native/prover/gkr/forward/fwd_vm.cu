// fwd-VM v2 CUDA interpreter (Task 8): a row-per-thread interpreter over the
// gkr_eval_isa fwd-VM v2 16-bit-lane wire format (`gkr_eval_isa::fwd::encode`).
// One thread = one row (`gid`), a SINGLE e4 accumulator in registers whose
// limb 0 IS the bf accumulator (limbs 1-3 zero while the acc is in base
// domain), and a WARP-PARTITIONED cell file in shared memory addressed in
// BUCKETS (one 512-B chunk per bucket inside each warp's private contiguous
// partition; no warp touches another warp's partition): an ext cell is a whole
// bucket chunk viewed as 32 per-lane 16-B slices (one lds.128/sts.128); bf
// cell c is word `lane` of line `c % 4` of bucket `c / 4`'s chunk. Both views
// are bank-conflict-free and all cross-view aliasing is warp-contained — see
// the cell-file section below for the layout + the issue-order safety
// invariant. The instruction's field bit selects the view.
//
// Dispatch follows the design spec's SS1.3 table on a warp-uniform acc-domain
// flag (set by Mov AccFromSrc's field bit, flipped base->ext by the `promote`
// header bit); every row maps onto an EXISTING field primitive (bf / e4 /
// mixed) - this file dispatches, it does not implement arithmetic. Mul's sign
// bit means NEGATE-ACC-FIRST (typed by the domain flag: limb-0 vs 4-limb neg);
// zero-arity Mul is legal iff that bit is set (pure negation).
//
// Semantics mirror the CPU golden model
// `gkr_eval_isa::fwd::interp::interpret_layer_row_impl`.
//
// The release instantiation (`ab_gkr_fwd_vm_s<BUCKETS>_kernel`, static smem so
// ptxas sees the footprint) compiles out ALL validation - the Rust
// compiler+validator guarantee well-formed programs. The VALIDATE
// instantiation (`ab_gkr_fwd_vm_validate_kernel`, dynamic smem) carries the
// v1-style fail-closed checks and atomicOr's FWDVM_ERR_* bits into
// `error_flag`; it is launched only by the test/parity harness.

#include "fwd_vm.cuh"

// Runtime-produced challenge bank (`LdcSub::ConstChallenge`) - the one
// legitimately runtime-late input. Rust binds this symbol and uploads it with
// `memcpyToSymbolAsync` on `exec_stream` (Task 9); all uploads and all
// launches that read it are ordered on `exec_stream`, and the bank is
// per-proof-instance state. `fwd_vm_desc::n_const_challenge` carries the used
// length so VALIDATE can bounds-check indices.
__device__ __constant__ e4 ab_gkr_fwd_vm_const_challenge[airbender::prover::gkr::FWD_VM_CONST_CHALLENGE_CAP];

namespace airbender::prover::gkr {

// --- error bits (VALIDATE only; atomicOr'd into error_flag; 0 = clean) ------
constexpr u32 FWDVM_ERR_TRAILING_LANES = 1;   // decoded lanes != program_lanes
constexpr u32 FWDVM_ERR_BAD_HEADER = 2;       // reserved bits / bad Mov dir / bad arity / non-canonical fields
constexpr u32 FWDVM_ERR_NULL_COLUMN = 8;      // base[slot] is null on a Global access
constexpr u32 FWDVM_ERR_LDC_OOB = 16;         // Ldc idx >= its bank length
constexpr u32 FWDVM_ERR_BAD_SPECIAL = 32;     // bad inline special / desc kind / arena / vkind
constexpr u32 FWDVM_ERR_DESC_OOB = 64;        // Special desc >= n_descs
constexpr u32 FWDVM_ERR_TABLE_OOB = 128;      // mapped lookup index >= table_len
constexpr u32 FWDVM_ERR_CELL_OOB = 256;       // cell (bf lane / ext bucket) exceeds the smem budget
constexpr u32 FWDVM_ERR_FIELD_MISMATCH = 512; // bf-field read of an e4-intrinsic bank/desc, or Base DstFromAcc off an ext acc
constexpr u32 FWDVM_ERR_NULL_POINTER = 1024;  // null mapping arena / table / mask / fill

// --- wire tags (mirror gkr_eval_isa::fwd::encode; UNCHANGED from v1) ---------
// operand: [payload:14][tag:2]; tag 00=Global{[col:10][slot:4]} 01=Smem{[cell:14]}
//          10=Ldc{[idx:12][sub:2]} 11=Special{[desc:14]}
// dst: [payload][kind:1]; kind 0=Smem{[cell:14]} 1=GlobalMaterialize{[col:10][slot:4]}
constexpr u32 LDC_CONST = 0;
constexpr u32 LDC_CONST_CHALLENGE = 1;
constexpr u32 LDC_ARG_CHALLENGE = 2;
constexpr u32 LDC_SPECIAL = 3;
constexpr u32 SPECIAL_ZERO = 0; // never emitted (elided upstream); VALIDATE rejects it
constexpr u32 SPECIAL_ONE = 1;
constexpr u32 SPECIAL_NEG_ONE = 2;

// Inline specials come from field CONSTANTS - never computed as sub(0, 1) at
// runtime. `bf::neg` / `e4::from_scalar` are constexpr, so these fold to
// immediates at compile time.
DEVICE_FORCEINLINE bf bf_minus_one() {
  constexpr bf v = bf::neg(bf::ONE());
  return v;
}

DEVICE_FORCEINLINE e4 e4_minus_one() {
  constexpr e4 v = e4::from_scalar(bf::neg(bf::ONE()));
  return v;
}

// Read lane `i` from the program: the inline `__grid_constant__` array
// (kernel-param/const memory) or the LDG fallback (`program_ldg`), selected
// once per launch by the kernel wrapper.
template <bool LDG> DEVICE_FORCEINLINE u16 vm_lane(const fwd_vm_desc &d, const u32 i) {
  if constexpr (LDG)
    return d.program_ldg[i];
  else
    return d.program[i];
}

// --- warp-partitioned bucket smem cell file (SS3) ------------------------------
// The block's cell file is partitioned into per-WARP partitions of contiguous
// smem, `budget_buckets * 512 B` each (512 B = 32 lanes x 16 B); warp w's
// partition starts at `w * budget_buckets * 512` bytes from the file base. No
// warp ever touches another warp's partition, so inter-warp races are
// structurally impossible. Within a partition, bucket b owns the contiguous
// 512-B chunk at `b * 512`. The instruction's field bit selects one of two
// views of a chunk (wire encoding unchanged: a bf cell index c is a lane index
// with bucket c >> 2 and sub-index c & 3; an ext cell index IS the bucket
// index):
//   - e4 view: lane t owns bytes [t*16, t*16+16) of the chunk -> a single
//     lds.128/sts.128. The warp accesses 512 contiguous bytes = four 128-B
//     subtransactions, each covering all 32 banks exactly once -> conflict-free.
//   - 4xbf view: the chunk is 4 lines of 32 bf values; bf cell c lives in line
//     c & 3 at word t for lane t -> `chunk + (c & 3)*128 + lane*4`, a regular
//     .32 access. The warp accesses 128 contiguous bytes = all 32 banks
//     exactly once -> conflict-free.
//
// SAFETY INVARIANT (cross-view aliasing): cross-view reuse of a bucket — the
// compiler's allocator time-multiplexes a quad between the two views over
// disjoint lifetimes (the CPU model's `cells` file aliases them) —
// redistributes bytes ACROSS LANES OF THE SAME WARP: lane t's bf words overlap
// OTHER lanes' e4 slices. This is safe because (a) all aliasing is
// warp-contained (the partition), and (b) a converged warp issues instructions
// in program order and the smem/MIO pipeline processes a warp's wavefronts in
// issue order — and the interpreter's control flow is warp-uniform (program
// lanes are grid-constant broadcasts; the only divergence is the
// `gid >= count` early-exit, which only removes writers). Formally the PTX
// memory model calls unsynchronized cross-lane conflicting access a race; the
// in-order-per-warp hardware argument is load-bearing and holds only under
// warp-uniform control flow.
//
// `cells` is the block's file reinterpreted as bf lanes (u32 words);
// `budget_buckets` is the bucket budget (a compile-time constant in the static
// release body, so all the index math folds). blockDim.x must be a multiple
// of 32 (both kernels launch at 128).

DEVICE_FORCEINLINE u32 smem_warp_base(const u32 budget_buckets) { return (threadIdx.x >> 5) * budget_buckets * 128; }

DEVICE_FORCEINLINE u32 smem_bf_unit(const u32 cell, const u32 budget_buckets) {
  return smem_warp_base(budget_buckets) + (cell >> 2) * 128 + (cell & 3) * 32 + (threadIdx.x & 31);
}

DEVICE_FORCEINLINE bf smem_ld_bf(const bf *cells, const u32 cell, const u32 budget_buckets) { return cells[smem_bf_unit(cell, budget_buckets)]; }

DEVICE_FORCEINLINE void smem_st_bf(bf *cells, const u32 cell, const u32 budget_buckets, const bf v) { cells[smem_bf_unit(cell, budget_buckets)] = v; }

// Ext cell = the lane's 16-B slice of the bucket chunk: a single
// lds.128/sts.128 via uint4 (the file base is 16-B aligned and the word offset
// is a multiple of 4, so the vector access is legal).
DEVICE_FORCEINLINE e4 smem_ld_e4(const bf *cells, const u32 bucket, const u32 budget_buckets) {
  const uint4 v = *reinterpret_cast<const uint4 *>(cells + smem_warp_base(budget_buckets) + bucket * 128 + (threadIdx.x & 31) * 4);
  return *reinterpret_cast<const e4 *>(&v);
}

DEVICE_FORCEINLINE void smem_st_e4(bf *cells, const u32 bucket, const u32 budget_buckets, const e4 v) {
  *reinterpret_cast<uint4 *>(cells + smem_warp_base(budget_buckets) + bucket * 128 + (threadIdx.x & 31) * 4) = *reinterpret_cast<const uint4 *>(&v);
}

// --- Global{slot,col}: one field-qualified homogeneous matrix per slot -------
// Column c of slot s lives at base[s] + c * stride_bytes[s], for load and
// store alike; the instruction's field bit AGREES with the slot's field by
// construction (validated Rust-side), so it directly types the access width.
DEVICE_FORCEINLINE const char *global_col(const fwd_vm_desc &d, const u32 slot, const u32 col) {
  return d.base[slot] + static_cast<size_t>(col) * d.stride_bytes[slot];
}

// --- special descriptors ------------------------------------------------------

struct fwd_vm_special {
  u32 kind;
  u32 arena;
  u32 set_index;
  u32 vkind;
};

DEVICE_FORCEINLINE fwd_vm_special unpack_special(const u32 w) {
  fwd_vm_special s;
  s.kind = (w >> FWD_VM_DESC_KIND_SHIFT) & FWD_VM_DESC_KIND_MASK;
  s.arena = (w >> FWD_VM_DESC_ARENA_SHIFT) & FWD_VM_DESC_ARENA_MASK;
  s.set_index = (w >> FWD_VM_DESC_SET_INDEX_SHIFT) & FWD_VM_DESC_SET_INDEX_MASK;
  s.vkind = (w >> FWD_VM_DESC_VKIND_SHIFT) & FWD_VM_DESC_VKIND_MASK;
  return s;
}

// Mapping = one COLUMN of a contiguous u32 arena (column-major, stride = count).
DEVICE_FORCEINLINE const u32 *special_mapping(const fwd_vm_desc &d, const fwd_vm_special &s) {
  return d.mapping_arena[s.arena] + static_cast<size_t>(s.set_index) * d.count;
}

template <bool VALIDATE> DEVICE_FORCEINLINE bool special_common_checks(const fwd_vm_desc &d, const u32 desc, u32 &err) {
  if constexpr (VALIDATE) {
    if (desc >= d.n_descs) {
      err |= FWDVM_ERR_DESC_OOB;
      return false;
    }
    const fwd_vm_special s = unpack_special(d.descs[desc]);
    if (s.kind > SD_VIRTUAL) {
      err |= FWDVM_ERR_BAD_SPECIAL;
      return false;
    }
    if ((s.kind == SD_SINGLE_COLUMN || s.kind == SD_AGGREGATE || s.kind == SD_DECODER) &&
        (s.arena >= FWD_VM_MAPPING_ARENA_COUNT || d.mapping_arena[s.arena] == nullptr)) {
      err |= (s.arena >= FWD_VM_MAPPING_ARENA_COUNT) ? FWDVM_ERR_BAD_SPECIAL : FWDVM_ERR_NULL_POINTER;
      return false;
    }
    if ((s.kind == SD_AGGREGATE || s.kind == SD_SETUP || s.kind == SD_DECODER) && d.table == nullptr) {
      err |= FWDVM_ERR_NULL_POINTER;
      return false;
    }
    if (s.kind == SD_DECODER && (d.mask == nullptr || d.fill == nullptr)) {
      err |= FWDVM_ERR_NULL_POINTER;
      return false;
    }
    if (s.kind == SD_VIRTUAL && (s.vkind < GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS || s.vkind > GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_HIGH)) {
      err |= FWDVM_ERR_BAD_SPECIAL;
      return false;
    }
  }
  return true;
}

// Special{desc}, ext view: the four peek legs + VirtualSetup, mirroring the v1
// resolver semantics but sourced from the header arenas. `vkind` is the native
// `gkr_base_source_kind` value VERBATIM - no translation switch.
template <bool VALIDATE> DEVICE_FORCEINLINE e4 read_special_e4(const fwd_vm_desc &d, const u32 desc, const unsigned gid, u32 &err) {
  if (!special_common_checks<VALIDATE>(d, desc, err))
    return e4::ZERO();
  const fwd_vm_special s = unpack_special(d.descs[desc]);
  switch (s.kind) {
  case SD_SINGLE_COLUMN: {
    // lift(Bf::from_u32_with_reduction(mapping[row])) - the mapping value is a
    // raw index, so it enters the field via the Montgomery conversion.
    const u32 idx = load<u32, ld_modifier::ca>(special_mapping(d, s), gid);
    return e4::from_scalar(bf::from_u32_with_reduction(idx));
  }
  case SD_AGGREGATE: {
    const u32 row = load<u32, ld_modifier::ca>(special_mapping(d, s), gid);
    if constexpr (VALIDATE) {
      if (row >= d.table_len) {
        err |= FWDVM_ERR_TABLE_OOB;
        return e4::ZERO();
      }
    }
    return load<e4, ld_modifier::ca>(d.table, row);
  }
  case SD_SETUP:
    // Zero-padded tail past the real table length.
    return gid < d.table_len ? load<e4, ld_modifier::ca>(d.table, gid) : e4::ZERO();
  case SD_DECODER: {
    const bf mask = load<bf, ld_modifier::ca>(d.mask, gid);
    if (mask.limb == 0)
      return load<e4, ld_modifier::ca>(d.fill, 0); // challenge-dependent, read through the pointer
    const u32 row = load<u32, ld_modifier::ca>(special_mapping(d, s), gid);
    if constexpr (VALIDATE) {
      if (row >= d.table_len) {
        err |= FWDVM_ERR_TABLE_OOB;
        return e4::ZERO();
      }
    }
    return load<e4, ld_modifier::ca>(d.table, row);
  }
  default: // SD_VIRTUAL: resolver-computed, reads NO memory
    return e4::from_scalar(gkr_virtual_base_value(static_cast<gkr_base_source_kind>(s.vkind), gid));
  }
}

// Special{desc}, bf view: only the two bf-intrinsic kinds are legal here
// (SingleColumn / VirtualSetup); the e4-intrinsic kinds fail closed under
// VALIDATE and cannot appear in validated programs.
template <bool VALIDATE> DEVICE_FORCEINLINE bf read_special_bf(const fwd_vm_desc &d, const u32 desc, const unsigned gid, u32 &err) {
  if (!special_common_checks<VALIDATE>(d, desc, err))
    return bf::ZERO();
  const fwd_vm_special s = unpack_special(d.descs[desc]);
  switch (s.kind) {
  case SD_SINGLE_COLUMN:
    return bf::from_u32_with_reduction(load<u32, ld_modifier::ca>(special_mapping(d, s), gid));
  case SD_VIRTUAL:
    return gkr_virtual_base_value(static_cast<gkr_base_source_kind>(s.vkind), gid);
  default:
    if constexpr (VALIDATE)
      err |= FWDVM_ERR_FIELD_MISMATCH;
    return bf::ZERO();
  }
}

// --- Ldc{sub,idx}: consts / challenge banks / inline specials ----------------

template <bool VALIDATE> DEVICE_FORCEINLINE bf read_ldc_bf(const fwd_vm_desc &d, const u32 sub, const u32 idx, u32 &err) {
  switch (sub) {
  case LDC_CONST:
    if constexpr (VALIDATE) {
      if (idx >= d.n_consts) {
        err |= FWDVM_ERR_LDC_OOB;
        return bf::ZERO();
      }
    }
    return d.consts[idx];
  case LDC_SPECIAL:
    if (idx == SPECIAL_ONE)
      return bf::ONE();
    if (idx == SPECIAL_NEG_ONE)
      return bf_minus_one();
    if constexpr (VALIDATE)
      err |= FWDVM_ERR_BAD_SPECIAL; // Zero is never emitted; > NegOne is malformed
    return bf::ZERO();
  default: // challenge banks are e4 by definition - a bf-field read is malformed
    if constexpr (VALIDATE)
      err |= FWDVM_ERR_FIELD_MISMATCH;
    return bf::ZERO();
  }
}

template <bool VALIDATE> DEVICE_FORCEINLINE e4 read_ldc_e4(const fwd_vm_desc &d, const u32 sub, const u32 idx, u32 &err) {
  switch (sub) {
  case LDC_CONST_CHALLENGE:
    if constexpr (VALIDATE) {
      if (idx >= d.n_const_challenge) {
        err |= FWDVM_ERR_LDC_OOB;
        return e4::ZERO();
      }
    }
    return ::ab_gkr_fwd_vm_const_challenge[idx];
  case LDC_ARG_CHALLENGE:
    if constexpr (VALIDATE) {
      if (idx >= d.n_arg_challenge) {
        err |= FWDVM_ERR_LDC_OOB;
        return e4::ZERO();
      }
    }
    return d.arg_challenge[idx];
  case LDC_SPECIAL:
    if (idx == SPECIAL_ONE)
      return e4::ONE();
    if (idx == SPECIAL_NEG_ONE)
      return e4_minus_one();
    if constexpr (VALIDATE)
      err |= FWDVM_ERR_BAD_SPECIAL;
    return e4::ZERO();
  default: // consts are bf by definition - an e4-field read is malformed
    if constexpr (VALIDATE)
      err |= FWDVM_ERR_FIELD_MISMATCH;
    return e4::ZERO();
  }
}

// --- typed operand reads ------------------------------------------------------
// The consuming instruction's field bit selects the width (Fma: per side).
// Global loads are single typed loads - a bf column is loaded as bf and lifted
// only when the op's semantics need e4; an e4 column is one vectorized
// load<e4>. Smem: the field bit selects the view (bf lane vs ext bucket).

template <bool VALIDATE>
DEVICE_FORCEINLINE bf read_operand_bf(const fwd_vm_desc &d, const bf *cells, const u32 budget_buckets, const u32 budget_lanes, const unsigned gid, const u16 l,
                                      u32 &err) {
  switch (l & 0b11) {
  case 0b00: { // Global { slot, col }
    const u32 slot = (l >> 2) & 0xF;
    const u32 col = l >> 6;
    if constexpr (VALIDATE) {
      if (d.base[slot] == nullptr) {
        err |= FWDVM_ERR_NULL_COLUMN;
        return bf::ZERO();
      }
    }
    return load<bf, ld_modifier::ca>(reinterpret_cast<const bf *>(global_col(d, slot, col)), gid);
  }
  case 0b01: { // Smem { cell }: bf -> 4-B lane index
    const u32 cell = l >> 2;
    if constexpr (VALIDATE) {
      if (cell >= budget_lanes) {
        err |= FWDVM_ERR_CELL_OOB;
        return bf::ZERO();
      }
    }
    return smem_ld_bf(cells, cell, budget_buckets);
  }
  case 0b10: // Ldc { sub, idx }
    return read_ldc_bf<VALIDATE>(d, (l >> 2) & 0b11, l >> 4, err);
  default: // 0b11 Special { desc }
    return read_special_bf<VALIDATE>(d, l >> 2, gid, err);
  }
}

template <bool VALIDATE>
DEVICE_FORCEINLINE e4 read_operand_e4(const fwd_vm_desc &d, const bf *cells, const u32 budget_buckets, const u32 budget_lanes, const unsigned gid, const u16 l,
                                      u32 &err) {
  switch (l & 0b11) {
  case 0b00: { // Global { slot, col }: one vectorized 16-B load
    const u32 slot = (l >> 2) & 0xF;
    const u32 col = l >> 6;
    if constexpr (VALIDATE) {
      if (d.base[slot] == nullptr) {
        err |= FWDVM_ERR_NULL_COLUMN;
        return e4::ZERO();
      }
    }
    return load<e4, ld_modifier::ca>(reinterpret_cast<const e4 *>(global_col(d, slot, col)), gid);
  }
  case 0b01: { // Smem { cell }: ext -> BUCKET index
    const u32 bucket = l >> 2;
    if constexpr (VALIDATE) {
      if (bucket * 4 + 4 > budget_lanes) {
        err |= FWDVM_ERR_CELL_OOB;
        return e4::ZERO();
      }
    }
    return smem_ld_e4(cells, bucket, budget_buckets);
  }
  case 0b10: // Ldc { sub, idx }
    return read_ldc_e4<VALIDATE>(d, (l >> 2) & 0b11, l >> 4, err);
  default: // 0b11 Special { desc }
    return read_special_e4<VALIDATE>(d, l >> 2, gid, err);
  }
}

// --- typed dst writes ---------------------------------------------------------
// GlobalMaterialize (and DstFromAcc to global) is the only DRAM write path.
// st.cs (streaming): the current lowering never re-reads a stored value
// (post-F7, cache roots flow through the acc, not back through DRAM).

template <bool VALIDATE>
DEVICE_FORCEINLINE void write_dst_bf(const fwd_vm_desc &d, bf *cells, const u32 budget_buckets, const u32 budget_lanes, const unsigned gid, const u16 dl,
                                     const bf v, u32 &err) {
  if ((dl & 1) == 0) { // Smem { cell }: bf lane
    const u32 cell = dl >> 1;
    if constexpr (VALIDATE) {
      if (cell >= budget_lanes) {
        err |= FWDVM_ERR_CELL_OOB;
        return;
      }
    }
    smem_st_bf(cells, cell, budget_buckets, v);
  } else { // GlobalMaterialize { slot, col }
    const u32 slot = (dl >> 1) & 0xF;
    const u32 col = dl >> 5;
    if constexpr (VALIDATE) {
      if (d.base[slot] == nullptr) {
        err |= FWDVM_ERR_NULL_COLUMN;
        return;
      }
    }
    store<bf, st_modifier::cs>(reinterpret_cast<bf *>(const_cast<char *>(global_col(d, slot, col))), v, gid);
  }
}

template <bool VALIDATE>
DEVICE_FORCEINLINE void write_dst_e4(const fwd_vm_desc &d, bf *cells, const u32 budget_buckets, const u32 budget_lanes, const unsigned gid, const u16 dl,
                                     const e4 v, u32 &err) {
  if ((dl & 1) == 0) { // Smem { cell }: ext bucket
    const u32 bucket = dl >> 1;
    if constexpr (VALIDATE) {
      if (bucket * 4 + 4 > budget_lanes) {
        err |= FWDVM_ERR_CELL_OOB;
        return;
      }
    }
    smem_st_e4(cells, bucket, budget_buckets, v);
  } else { // GlobalMaterialize { slot, col }
    const u32 slot = (dl >> 1) & 0xF;
    const u32 col = dl >> 5;
    if constexpr (VALIDATE) {
      if (d.base[slot] == nullptr) {
        err |= FWDVM_ERR_NULL_COLUMN;
        return;
      }
    }
    store<e4, st_modifier::cs>(reinterpret_cast<e4 *>(const_cast<char *>(global_col(d, slot, col))), v, gid);
  }
}

// --- interpreter core ---------------------------------------------------------
// SS1.3 dispatch on (opcode, f0/f1, warp-uniform acc-domain flag). The release
// instantiation (VALIDATE=false) has ZERO checks: no error flag, no bounds, no
// header validity - `err` and every `if constexpr (VALIDATE)` branch compile
// away.
template <bool VALIDATE, bool LDG>
DEVICE_FORCEINLINE void vm_core(const fwd_vm_desc &d, bf *cells, const u32 budget_buckets, const u32 budget_lanes, const unsigned gid, u32 *error_flag) {
#define FWDVM_LANE() vm_lane<LDG>(d, i++)
#define FWDVM_READ_BF() read_operand_bf<VALIDATE>(d, cells, budget_buckets, budget_lanes, gid, FWDVM_LANE(), err)
#define FWDVM_READ_E4() read_operand_e4<VALIDATE>(d, cells, budget_buckets, budget_lanes, gid, FWDVM_LANE(), err)
  u32 i = 0;   // lane cursor (warp-uniform)
  u32 err = 0; // dead in release (never written, checks compiled out)
  e4 acc = e4::ZERO();
  bool acc_ext = false; // warp-uniform acc-domain flag (SS1.1)

  for (u32 k = 0; k < d.n_instr; k++) {
    if constexpr (VALIDATE) {
      if (err != 0)
        break;
    }
    const u16 h = FWDVM_LANE();
    const u32 op = h & 0b11;

    if (op == 0b11) {
      // --- Mov: [field:1@4][dir:2@2][op=3:2]; bits 5+ reserved. The field bit
      // types the transfer width (bf = limb 0 / 1 lane; ext = 16 B).
      const u32 dir = (h >> 2) & 0b11;
      const bool fe4 = ((h >> 4) & 1) != 0;
      if constexpr (VALIDATE) {
        if ((h >> 5) != 0 || dir == 3) {
          err |= FWDVM_ERR_BAD_HEADER;
          break;
        }
      }
      switch (dir) {
      case 0: // AccFromSrc: sets the acc domain from the field bit
        if (fe4) {
          acc = FWDVM_READ_E4();
        } else {
          acc = e4::from_scalar(FWDVM_READ_BF()); // zeroes limbs 1-3: the base-domain invariant
        }
        acc_ext = fe4;
        break;
      case 1: { // DstFromAcc
        if constexpr (VALIDATE) {
          if (!fe4 && acc_ext) { // no implicit truncation
            err |= FWDVM_ERR_FIELD_MISMATCH;
            break;
          }
        }
        const u16 dl = FWDVM_LANE();
        if (fe4)
          write_dst_e4<VALIDATE>(d, cells, budget_buckets, budget_lanes, gid, dl, acc, err);
        else
          write_dst_bf<VALIDATE>(d, cells, budget_buckets, budget_lanes, gid, dl, acc[0][0], err);
        break;
      }
      default: { // 2 = DstFromSrc: dst lane, then src lane (encode order)
        const u16 dl = FWDVM_LANE();
        if (fe4) {
          const e4 v = FWDVM_READ_E4();
          write_dst_e4<VALIDATE>(d, cells, budget_buckets, budget_lanes, gid, dl, v, err);
        } else {
          const bf v = FWDVM_READ_BF();
          write_dst_bf<VALIDATE>(d, cells, budget_buckets, budget_lanes, gid, dl, v, err);
        }
        break;
      }
      }
      continue;
    }

    // --- Arith: [rsvd:3][sign:1@12][promote:1@11][f1:1@10][f0:1@9][arity:7@2][op:2]
    const u32 arity = (h >> 2) & 0x7F;
    const bool f0 = ((h >> 9) & 1) != 0;
    const bool minus = ((h >> 12) & 1) != 0;
    if constexpr (VALIDATE) {
      const bool f1v = ((h >> 10) & 1) != 0;
      const bool zero_arity_ok = op == 0b01 && minus; // zero-arity Mul-minus = pure negation
      if ((h >> 13) != 0 || (op != 0b10 && f1v) || (arity == 0 && !zero_arity_ok) || (op == 0b10 && f0 && !f1v) /* (Ext,Base) FMA is non-canonical */) {
        err |= FWDVM_ERR_BAD_HEADER;
        break;
      }
    }
    // promote (bit 11): the base->ext acc lift. Representationally free (limbs
    // 1-3 are already zero); it flips the domain flag BEFORE the op executes.
    acc_ext |= ((h >> 11) & 1) != 0;

    if (op == 0b00) {
      // Add: limb-0 bf add/sub for {Base} (identical in both domains - a
      // lifted bf only touches limb 0), full e4 add/sub for {Ext}.
      if (f0) {
        for (u32 t = 0; t < arity; t++) {
          const e4 v = FWDVM_READ_E4();
          acc = minus ? e4::sub(acc, v) : e4::add(acc, v);
        }
      } else {
        for (u32 t = 0; t < arity; t++) {
          const bf v = FWDVM_READ_BF();
          acc = minus ? e4::sub(acc, v) : e4::add(acc, v); // e4 +/- bf = limb-0 only
        }
      }
    } else if (op == 0b01) {
      // Mul: sign bit = NEGATE ACC FIRST, typed by the (post-promote) domain.
      if (minus) {
        if (acc_ext)
          acc = e4::neg(acc);
        else
          acc[0][0] = bf::neg(acc[0][0]);
      }
      if (f0) {
        // Mul{Ext}: full e4 mul (requires an ext acc - promote guarantees it).
        for (u32 t = 0; t < arity; t++)
          acc = e4::mul(acc, FWDVM_READ_E4());
      } else if (acc_ext) {
        // Mul{Base} on an ext acc: 4-limb scale (4 bf muls).
        for (u32 t = 0; t < arity; t++)
          acc = e4::mul(acc, FWDVM_READ_BF());
      } else {
        // Mul{Base} on a base acc: bf mul on limb 0.
        for (u32 t = 0; t < arity; t++)
          acc[0][0] = bf::mul(acc[0][0], FWDVM_READ_BF());
      }
    } else {
      // Fma: acc +/-= sum of L*R pairs; per-side fields, canonical (Base,Ext)
      // mixed order only.
      const bool f1 = ((h >> 10) & 1) != 0;
      if (!f0 && !f1) {
        // Fma{B,B}: bf mul + limb-0 add/sub (identical in both domains).
        for (u32 t = 0; t < arity; t++) {
          const bf l = FWDVM_READ_BF();
          const bf r = FWDVM_READ_BF();
          acc[0][0] = minus ? bf::sub(acc[0][0], bf::mul(l, r)) : bf::fma(l, r, acc[0][0]);
        }
      } else if (!f0) {
        // Fma{B,E}: scale product (4 bf muls) + full e4 add/sub.
        for (u32 t = 0; t < arity; t++) {
          const bf l = FWDVM_READ_BF();
          const e4 r = FWDVM_READ_E4();
          acc = minus ? e4::sub(acc, e4::mul(r, l)) : e4::fma(r, l, acc);
        }
      } else {
        // Fma{E,E}: full product + full e4 add/sub.
        for (u32 t = 0; t < arity; t++) {
          const e4 l = FWDVM_READ_E4();
          const e4 r = FWDVM_READ_E4();
          acc = minus ? e4::sub(acc, e4::mul(l, r)) : e4::fma(l, r, acc);
        }
      }
    }
  }

  if constexpr (VALIDATE) {
    if (err == 0 && i != d.program_lanes)
      err |= FWDVM_ERR_TRAILING_LANES;
    if (err != 0)
      atomicOr(error_flag, err);
  }
#undef FWDVM_READ_E4
#undef FWDVM_READ_BF
#undef FWDVM_LANE
}

// --- kernel bodies -------------------------------------------------------------

// Dynamic-smem body (VALIDATE): the launch sizes the file, so the bucket
// budget is recovered from %dynamic_smem_size for the fail-closed cell-bounds
// checks. Occupancy is opaque to ptxas here - fine for a harness-only kernel.
template <bool LDG> DEVICE_FORCEINLINE void vm_body_validate(const fwd_vm_desc &d, u32 *error_flag) {
  extern __shared__ e4 fwd_vm_cells_dyn[]; // e4-typed for the 16-B base alignment
  u32 smem_bytes;
  asm("mov.u32 %0, %%dynamic_smem_size;" : "=r"(smem_bytes));
  // Bucket-granular recovery: the launcher sizes the file as a whole number of
  // buckets; flooring keeps the fail-closed lane bound consistent with the
  // warp-partitioned addressing (a lane past the last whole bucket would cross
  // into the next warp's partition).
  const u32 budget_buckets = smem_bytes / (blockDim.x * static_cast<u32>(sizeof(bf))) / 4;
  const u32 budget_lanes = budget_buckets * 4;
  bf *cells = reinterpret_cast<bf *>(fwd_vm_cells_dyn);
  // Zero-init BEFORE the row early-exit: in the warp-partitioned layout a
  // lane's e4 slices cover OTHER lanes' bf zero-init words, so an exited lane
  // must still zero its words for a partial tail warp to read zeros from
  // never-written cells (matching the CPU model's zeroed cell file).
  for (u32 c = 0; c < budget_lanes; c++)
    smem_st_bf(cells, c, budget_buckets, bf::ZERO());
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= d.count)
    return;
  vm_core<true, LDG>(d, cells, budget_buckets, budget_lanes, gid, error_flag);
}

// Static-smem body (release, 128 threads): BUCKETS is a compile-time constant.
// The __shared__ cell file is declared ONCE in the kernel and passed in - if it
// lived here, the two LDG instantiations would each get their own copy and
// ptxas would allocate the static smem twice, halving occupancy.
template <bool LDG, u32 BUCKETS> DEVICE_FORCEINLINE void vm_body_static(const fwd_vm_desc &d, e4 *cell_file) {
  bf *cells = reinterpret_cast<bf *>(cell_file);
  // Zero-init BEFORE the row early-exit (see vm_body_validate): an exited
  // lane's zero-init words are covered by surviving lanes' e4 slices.
  for (u32 c = 0; c < BUCKETS * 4; c++)
    smem_st_bf(cells, c, BUCKETS, bf::ZERO());
  const unsigned gid = blockIdx.x * 128 + threadIdx.x;
  if (gid >= d.count)
    return;
  vm_core<false, LDG>(d, cells, BUCKETS, BUCKETS * 4, gid, nullptr);
}

// minBlocks = the occupancy the static smem permits: SM shared capacity
// (~100 KB) / per-block footprint (BUCKETS * 16 B * 128 threads + ~1 KB driver
// overhead), clamped to the 12-block warp limit (4 warps/block). ptxas then
// sizes registers to the smem-permitted occupancy.
#define FWDVM_SMEM_BLOCKS(B) ((102400u / ((B) * 2048u + 1024u)) > 12u ? 12u : ((102400u / ((B) * 2048u + 1024u)) < 1u ? 1u : (102400u / ((B) * 2048u + 1024u))))

// Release kernel per bucket budget. `program_ldg` selects the LDG fallback
// once per launch (warp-uniform grid-constant read); the inline-program path
// is the expected one for the whole committed corpus. The single kernel-scope
// __shared__ cell file (e4-typed for the 16-B base alignment) is shared by
// both residency paths, keeping the static smem footprint at one file so the
// FWDVM_SMEM_BLOCKS occupancy target holds.
#define FWDVM_STATIC_KERNEL(B)                                                                                                                                 \
  EXTERN __launch_bounds__(128, FWDVM_SMEM_BLOCKS(B)) __global__ void ab_gkr_fwd_vm_s##B##_kernel(const __grid_constant__ fwd_vm_desc desc) {                  \
    __shared__ e4 fwd_vm_cells_s[(B) * 128];                                                                                                                   \
    if (desc.program_ldg != nullptr)                                                                                                                           \
      vm_body_static<true, B>(desc, fwd_vm_cells_s);                                                                                                           \
    else                                                                                                                                                       \
      vm_body_static<false, B>(desc, fwd_vm_cells_s);                                                                                                          \
  }

// 4 buckets == the committed corpus's budget-16 bf lanes.
FWDVM_STATIC_KERNEL(4)

EXTERN __launch_bounds__(128, 4) __global__ void ab_gkr_fwd_vm_validate_kernel(const __grid_constant__ fwd_vm_desc desc, u32 *error_flag) {
  if (desc.program_ldg != nullptr)
    vm_body_validate<true>(desc, error_flag);
  else
    vm_body_validate<false>(desc, error_flag);
}

} // namespace airbender::prover::gkr
