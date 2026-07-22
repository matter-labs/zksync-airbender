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

#include "../eval_vm_exec.cuh"
#include "fwd_vm.cuh"

// Runtime-produced derived-e4 bank (`LdcSub::ConstDerivedE4`) - the one
// legitimately runtime-late input. Rust binds this symbol and uploads it with
// `memcpyToSymbolAsync` on `exec_stream` (Task 9); all uploads and all
// launches that read it are ordered on `exec_stream`, and the bank is
// per-proof-instance state. `fwd_vm_desc::n_const_derived_e4` carries the used
// length so VALIDATE can bounds-check indices. The bank ALSO hosts the decoder
// fill value (same class: one runtime challenge-dependent e4 per layer) at
// `fwd_vm_desc::fill_bank_idx`, appended after the real ConstDerivedE4 entries
// by the Rust lowering + upload (`vm/lower.rs`).
__device__ __constant__ e4 ab_gkr_fwd_vm_const_derived_e4[airbender::prover::gkr::FWD_VM_CONST_DERIVED_E4_CAP];

namespace airbender::prover::gkr {

// --- error bits (VALIDATE only; atomicOr'd into error_flag; 0 = clean) ------
constexpr u32 FWDVM_ERR_NULL_COLUMN = 8;     // base[slot] is null on a Global access
constexpr u32 FWDVM_ERR_LDC_OOB = 16;        // Ldc idx (or decoder fill_bank_idx) >= its bank length
constexpr u32 FWDVM_ERR_BAD_SPECIAL = 32;    // bad inline special / desc kind / arena / vkind
constexpr u32 FWDVM_ERR_DESC_OOB = 64;       // Special desc >= n_descs
constexpr u32 FWDVM_ERR_TABLE_OOB = 128;     // mapped lookup index >= table_len
constexpr u32 FWDVM_ERR_CELL_OOB = 256;      // cell (bf lane / ext bucket) exceeds the smem budget
constexpr u32 FWDVM_ERR_NULL_POINTER = 1024; // null mapping arena / table / mask

// --- Ldc sub-source / inline-special payload values ---------------------------
// (mirror gkr_eval_isa::fwd::isa::{LdcSub, Special}; UNCHANGED from v1). The
// lane-layout shifts/masks/tags themselves are the FWD_VM_* block in fwd_vm.cuh.
constexpr u32 LDC_CONST = 0;
constexpr u32 LDC_CONST_DERIVED_E4 = 1;
constexpr u32 LDC_ARG_DERIVED_E4 = 2;
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
// of FWD_VM_WARP_LANES (both kernels launch at 128).

constexpr u32 FWD_VM_WARP_LANES = 32;                                    // hardware warp size
constexpr u32 FWD_VM_WARP_SHIFT = 5;                                     // log2(FWD_VM_WARP_LANES)
constexpr u32 FWD_VM_LANE_MASK = FWD_VM_WARP_LANES - 1;                  // threadIdx.x & mask -> lane
constexpr u32 FWD_VM_E4_WORDS = 4;                                       // u32 words per e4 limb vector
constexpr u32 FWD_VM_BUCKET_WORDS = FWD_VM_WARP_LANES * FWD_VM_E4_WORDS; // 128 words = one 512-B chunk
constexpr u32 FWD_VM_BF_PER_BUCKET = FWD_VM_E4_WORDS;                    // bf cells per bucket (4 lines of 32)
constexpr u32 FWD_VM_BF_SUB_MASK = FWD_VM_BF_PER_BUCKET - 1;             // bf cell & mask -> line in bucket
constexpr u32 FWD_VM_BF_BUCKET_SHIFT = 2;                                // log2(FWD_VM_BF_PER_BUCKET); bf cell >> shift -> bucket
static_assert(1u << FWD_VM_WARP_SHIFT == FWD_VM_WARP_LANES, "warp shift/size drift");
static_assert(1u << FWD_VM_BF_BUCKET_SHIFT == FWD_VM_BF_PER_BUCKET, "bf bucket shift/size drift");

DEVICE_FORCEINLINE u32 smem_warp_base(const u32 budget_buckets) { return (threadIdx.x >> FWD_VM_WARP_SHIFT) * budget_buckets * FWD_VM_BUCKET_WORDS; }

DEVICE_FORCEINLINE u32 smem_bf_unit(const u32 cell, const u32 budget_buckets) {
  return smem_warp_base(budget_buckets) + (cell >> FWD_VM_BF_BUCKET_SHIFT) * FWD_VM_BUCKET_WORDS + (cell & FWD_VM_BF_SUB_MASK) * FWD_VM_WARP_LANES +
         (threadIdx.x & FWD_VM_LANE_MASK);
}

DEVICE_FORCEINLINE bf smem_ld_bf(const bf *cells, const u32 cell, const u32 budget_buckets) { return cells[smem_bf_unit(cell, budget_buckets)]; }

DEVICE_FORCEINLINE void smem_st_bf(bf *cells, const u32 cell, const u32 budget_buckets, const bf v) { cells[smem_bf_unit(cell, budget_buckets)] = v; }

// Ext cell = the lane's 16-B slice of the bucket chunk: a single
// lds.128/sts.128 via uint4 (the file base is 16-B aligned and the word offset
// is a multiple of 4, so the vector access is legal).
DEVICE_FORCEINLINE e4 smem_ld_e4(const bf *cells, const u32 bucket, const u32 budget_buckets) {
  const uint4 v = *reinterpret_cast<const uint4 *>(cells + smem_warp_base(budget_buckets) + bucket * FWD_VM_BUCKET_WORDS +
                                                   (threadIdx.x & FWD_VM_LANE_MASK) * FWD_VM_E4_WORDS);
  return *reinterpret_cast<const e4 *>(&v);
}

DEVICE_FORCEINLINE void smem_st_e4(bf *cells, const u32 bucket, const u32 budget_buckets, const e4 v) {
  *reinterpret_cast<uint4 *>(cells + smem_warp_base(budget_buckets) + bucket * FWD_VM_BUCKET_WORDS + (threadIdx.x & FWD_VM_LANE_MASK) * FWD_VM_E4_WORDS) =
      *reinterpret_cast<const uint4 *>(&v);
}

DEVICE_FORCEINLINE const char *source_col(const fwd_vm_desc &d, const u32 window, const u32 col) {
  return d.source_base[window] + static_cast<size_t>(col) * d.source_stride_bytes[window];
}

DEVICE_FORCEINLINE const char *dst_col(const fwd_vm_desc &d, const u32 slot, const u32 col) {
  return d.dst_base[slot] + static_cast<size_t>(col) * d.dst_stride_bytes[slot];
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
    if (s.kind == SD_DECODER) {
      if (d.mask == nullptr) {
        err |= FWDVM_ERR_NULL_POINTER;
        return false;
      }
      // Fail-closed fill_bank_idx bound: the lowering appends the fill AFTER
      // the real ConstDerivedE4 entries, so a valid index is < n_const_derived_e4
      // (and a fortiori < the cap); the FWD_VM_FILL_BANK_NONE sentinel of a
      // decoder-free layer trips this loudly if a decoder desc sneaks in.
      if (d.fill_bank_idx >= FWD_VM_CONST_DERIVED_E4_CAP || d.fill_bank_idx >= d.n_const_derived_e4) {
        err |= FWDVM_ERR_LDC_OOB;
        return false;
      }
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
      // Challenge-dependent fill from the __constant__ bank: the index is
      // warp-uniform (grid-constant desc), only the mask predicate is
      // per-lane, so this is a constant-cache broadcast.
      return ::ab_gkr_fwd_vm_const_derived_e4[d.fill_bank_idx];
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
      err |= EVAL_VM_ERR_FIELD_MISMATCH;
    return bf::ZERO();
  }
}

// --- Ldc{sub,idx}: consts / derived-e4 banks / inline specials ---------------

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
  default: // derived-e4 banks are e4 by definition - a bf-field read is malformed
    if constexpr (VALIDATE)
      err |= EVAL_VM_ERR_FIELD_MISMATCH;
    return bf::ZERO();
  }
}

template <bool VALIDATE> DEVICE_FORCEINLINE e4 read_ldc_e4(const fwd_vm_desc &d, const u32 sub, const u32 idx, u32 &err) {
  switch (sub) {
  case LDC_CONST_DERIVED_E4:
    if constexpr (VALIDATE) {
      if (idx >= d.n_const_derived_e4) {
        err |= FWDVM_ERR_LDC_OOB;
        return e4::ZERO();
      }
    }
    return ::ab_gkr_fwd_vm_const_derived_e4[idx];
  case LDC_ARG_DERIVED_E4:
    if constexpr (VALIDATE) {
      if (idx >= d.n_arg_derived_e4) {
        err |= FWDVM_ERR_LDC_OOB;
        return e4::ZERO();
      }
    }
    return d.arg_derived_e4[idx];
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
      err |= EVAL_VM_ERR_FIELD_MISMATCH;
    return e4::ZERO();
  }
}

// --- typed operand reads ------------------------------------------------------
// The consuming instruction's field bit selects the width (Fma: per side).
// Source loads are single typed loads - a bf column is loaded as bf and lifted
// only when the op's semantics need e4; an e4 column is one vectorized
// load<e4>. Smem: the field bit selects the view (bf lane vs ext bucket).

template <bool VALIDATE>
DEVICE_FORCEINLINE bf read_operand_bf(const fwd_vm_desc &d, const bf *cells, const u32 budget_buckets, const u32 budget_lanes, const unsigned gid, const u16 l,
                                      u32 &err) {
  switch (l & FWD_VM_OPERAND_TAG_MASK) {
  case FWD_VM_OPERAND_SOURCE: {
    const u32 window = (l >> FWD_VM_SOURCE_WINDOW_SHIFT) & FWD_VM_SOURCE_WINDOW_MASK;
    const u32 col = (l >> FWD_VM_SOURCE_COLUMN_SHIFT) & FWD_VM_SOURCE_COLUMN_MASK;
    if constexpr (VALIDATE) {
      if (d.source_base[window] == nullptr) {
        err |= FWDVM_ERR_NULL_COLUMN;
        return bf::ZERO();
      }
    }
    return load<bf, ld_modifier::ca>(reinterpret_cast<const bf *>(source_col(d, window, col)), gid);
  }
  case FWD_VM_OPERAND_SMEM: { // Smem { cell }: bf -> 4-B lane index
    const u32 cell = l >> FWD_VM_OPERAND_CELL_SHIFT;
    if constexpr (VALIDATE) {
      if (cell >= budget_lanes) {
        err |= FWDVM_ERR_CELL_OOB;
        return bf::ZERO();
      }
    }
    return smem_ld_bf(cells, cell, budget_buckets);
  }
  case FWD_VM_OPERAND_LDC: // Ldc { sub, idx }
    return read_ldc_bf<VALIDATE>(d, (l >> FWD_VM_LDC_SUB_SHIFT) & FWD_VM_LDC_SUB_MASK, l >> FWD_VM_LDC_IDX_SHIFT, err);
  default: // FWD_VM_OPERAND_SPECIAL: Special { desc }
    return read_special_bf<VALIDATE>(d, l >> FWD_VM_OPERAND_DESC_SHIFT, gid, err);
  }
}

template <bool VALIDATE>
DEVICE_FORCEINLINE e4 read_operand_e4(const fwd_vm_desc &d, const bf *cells, const u32 budget_buckets, const u32 budget_lanes, const unsigned gid, const u16 l,
                                      u32 &err) {
  switch (l & FWD_VM_OPERAND_TAG_MASK) {
  case FWD_VM_OPERAND_SOURCE: {
    const u32 window = (l >> FWD_VM_SOURCE_WINDOW_SHIFT) & FWD_VM_SOURCE_WINDOW_MASK;
    const u32 col = (l >> FWD_VM_SOURCE_COLUMN_SHIFT) & FWD_VM_SOURCE_COLUMN_MASK;
    if constexpr (VALIDATE) {
      if (d.source_base[window] == nullptr) {
        err |= FWDVM_ERR_NULL_COLUMN;
        return e4::ZERO();
      }
    }
    return load<e4, ld_modifier::ca>(reinterpret_cast<const e4 *>(source_col(d, window, col)), gid);
  }
  case FWD_VM_OPERAND_SMEM: { // Smem { cell }: ext -> BUCKET index
    const u32 bucket = l >> FWD_VM_OPERAND_CELL_SHIFT;
    if constexpr (VALIDATE) {
      if (bucket * FWD_VM_BF_PER_BUCKET + FWD_VM_BF_PER_BUCKET > budget_lanes) {
        err |= FWDVM_ERR_CELL_OOB;
        return e4::ZERO();
      }
    }
    return smem_ld_e4(cells, bucket, budget_buckets);
  }
  case FWD_VM_OPERAND_LDC: // Ldc { sub, idx }
    return read_ldc_e4<VALIDATE>(d, (l >> FWD_VM_LDC_SUB_SHIFT) & FWD_VM_LDC_SUB_MASK, l >> FWD_VM_LDC_IDX_SHIFT, err);
  default: // FWD_VM_OPERAND_SPECIAL: Special { desc }
    return read_special_e4<VALIDATE>(d, l >> FWD_VM_OPERAND_DESC_SHIFT, gid, err);
  }
}

// --- typed dst writes ---------------------------------------------------------
// GlobalMaterialize (and DstFromAcc to global) is the only DRAM write path.
// st.cs (streaming): the current lowering never re-reads a stored value
// (post-F7, cache roots flow through the acc, not back through DRAM).

template <bool VALIDATE>
DEVICE_FORCEINLINE void write_dst_bf(const fwd_vm_desc &d, bf *cells, const u32 budget_buckets, const u32 budget_lanes, const unsigned gid, const u16 dl,
                                     const bf v, u32 &err) {
  if ((dl & FWD_VM_DST_TAG_MASK) == FWD_VM_DST_SMEM) { // Smem { cell }: bf lane
    const u32 cell = dl >> FWD_VM_DST_CELL_SHIFT;
    if constexpr (VALIDATE) {
      if (cell >= budget_lanes) {
        err |= FWDVM_ERR_CELL_OOB;
        return;
      }
    }
    smem_st_bf(cells, cell, budget_buckets, v);
  } else { // GlobalMaterialize { slot, col }
    const u32 slot = (dl >> FWD_VM_DST_SLOT_SHIFT) & FWD_VM_DST_SLOT_MASK;
    const u32 col = dl >> FWD_VM_DST_COL_SHIFT;
    if constexpr (VALIDATE) {
      if (d.dst_base[slot] == nullptr) {
        err |= FWDVM_ERR_NULL_COLUMN;
        return;
      }
    }
    store<bf, st_modifier::cs>(reinterpret_cast<bf *>(const_cast<char *>(dst_col(d, slot, col))), v, gid);
  }
}

template <bool VALIDATE>
DEVICE_FORCEINLINE void write_dst_e4(const fwd_vm_desc &d, bf *cells, const u32 budget_buckets, const u32 budget_lanes, const unsigned gid, const u16 dl,
                                     const e4 v, u32 &err) {
  if ((dl & FWD_VM_DST_TAG_MASK) == FWD_VM_DST_SMEM) { // Smem { cell }: ext bucket
    const u32 bucket = dl >> FWD_VM_DST_CELL_SHIFT;
    if constexpr (VALIDATE) {
      if (bucket * FWD_VM_BF_PER_BUCKET + FWD_VM_BF_PER_BUCKET > budget_lanes) {
        err |= FWDVM_ERR_CELL_OOB;
        return;
      }
    }
    smem_st_e4(cells, bucket, budget_buckets, v);
  } else { // GlobalMaterialize { slot, col }
    const u32 slot = (dl >> FWD_VM_DST_SLOT_SHIFT) & FWD_VM_DST_SLOT_MASK;
    const u32 col = dl >> FWD_VM_DST_COL_SHIFT;
    if constexpr (VALIDATE) {
      if (d.dst_base[slot] == nullptr) {
        err |= FWDVM_ERR_NULL_COLUMN;
        return;
      }
    }
    store<e4, st_modifier::cs>(reinterpret_cast<e4 *>(const_cast<char *>(dst_col(d, slot, col))), v, gid);
  }
}

// --- forward adapter ----------------------------------------------------------

template <bool VALIDATE, bool LDG> struct FwdVmAdapter {
  const fwd_vm_desc &desc;
  bf *cells;
  u32 budget_buckets;
  u32 budget_lanes;
  unsigned gid;

  DEVICE_FORCEINLINE u16 lane(const u32 index) const { return vm_lane<LDG>(desc, index); }

  DEVICE_FORCEINLINE bf read_bf(const u16 lane, u32 &error) { return read_operand_bf<VALIDATE>(desc, cells, budget_buckets, budget_lanes, gid, lane, error); }

  DEVICE_FORCEINLINE e4 read_e4(const u16 lane, u32 &error) { return read_operand_e4<VALIDATE>(desc, cells, budget_buckets, budget_lanes, gid, lane, error); }

  DEVICE_FORCEINLINE void write_bf(const u16 dst, const bf value, u32 &error) {
    write_dst_bf<VALIDATE>(desc, cells, budget_buckets, budget_lanes, gid, dst, value, error);
  }

  DEVICE_FORCEINLINE void write_e4(const u16 dst, const e4 value, u32 &error) {
    write_dst_e4<VALIDATE>(desc, cells, budget_buckets, budget_lanes, gid, dst, value, error);
  }
};

template <bool VALIDATE, bool LDG>
DEVICE_FORCEINLINE eval_vm_result execute_fwd_vm(const fwd_vm_desc &desc, bf *cells, const u32 budget_buckets, const u32 budget_lanes, const unsigned gid) {
  FwdVmAdapter<VALIDATE, LDG> adapter{desc, cells, budget_buckets, budget_lanes, gid};
  return eval_vm_execute<VALIDATE, FwdVmAdapter<VALIDATE, LDG>>(adapter, desc.n_instr, desc.program_lanes);
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
  const u32 budget_buckets = smem_bytes / (blockDim.x * static_cast<u32>(sizeof(bf))) / FWD_VM_E4_WORDS;
  const u32 budget_lanes = budget_buckets * FWD_VM_BF_PER_BUCKET;
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
  const eval_vm_result result = execute_fwd_vm<true, LDG>(d, cells, budget_buckets, budget_lanes, gid);
  if (result.error != 0)
    atomicOr(error_flag, result.error);
}

// Static-smem body (release, 128 threads): BUCKETS is a compile-time constant.
// The __shared__ cell file is declared ONCE in the kernel and passed in - if it
// lived here, the two LDG instantiations would each get their own copy and
// ptxas would allocate the static smem twice, halving occupancy.
template <bool LDG, u32 BUCKETS> DEVICE_FORCEINLINE void vm_body_static(const fwd_vm_desc &d, e4 *cell_file) {
  bf *cells = reinterpret_cast<bf *>(cell_file);
  // Zero-init BEFORE the row early-exit (see vm_body_validate): an exited
  // lane's zero-init words are covered by surviving lanes' e4 slices.
  for (u32 c = 0; c < BUCKETS * FWD_VM_BF_PER_BUCKET; c++)
    smem_st_bf(cells, c, BUCKETS, bf::ZERO());
  const unsigned gid = blockIdx.x * 128 + threadIdx.x;
  if (gid >= d.count)
    return;
  execute_fwd_vm<false, LDG>(d, cells, BUCKETS, BUCKETS * FWD_VM_BF_PER_BUCKET, gid);
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
