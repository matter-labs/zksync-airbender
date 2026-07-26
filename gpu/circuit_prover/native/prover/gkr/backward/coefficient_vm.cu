// Backward coefficient-term ISA executor (design sections 10, 11).
//
// SCOPE OF THIS FILE AT THIS POINT IN THE PLAN. Task 9 established the ABI, the
// launch geometry and the specialization set. Task 10 added the typed source
// resolvers (section 10) plus the validation-only probe kernel that tests them.
// The u16 HEADER decode and the arithmetic loop (Task 11) are NOT here yet:
// `coefficient_body` sets up the private cell file, initializes the two
// accumulators exactly as section 11 specifies, and writes the contribution
// pair. `desc.program` is not walked by the release executors, so they still
// publish the `c_init`-only value of `acc_c0`. They are launchable and correct
// for a zero-word program; they are not yet the executor.
//
// What is deliberately absent, and must stay absent (section 11): a T0/T2
// split, warp shuffles, a general accumulator, an accumulator stash, a
// batch-accumulate destination, an `AccInit` operand, validation work in a
// release kernel, and any extra launch.
//
// ENDPOINT LAYOUT. A source at target depth is `2 * logical_rows` values with
// the two endpoints in SPLIT HALVES: `s0 = V[row]`, `s1 = V[logical_rows + row]`.
// That is the incumbent production layout (`gkr_get_initial_delta` and
// `flat_cont_fold_and_load` in `continuation.cuh` read `index` and
// `this_layer_size + index`), and the lazy fold below inherits it. The retired
// generic backward VM used the interleaved `(2*row, 2*row+1)` convention of
// `gkr_eval_isa::bwd::interp::sumcheck_fold_point` instead; the fold WEIGHTS are
// identical between the two conventions, only the backing offsets differ, which
// is why the transcript-derived prelude is reused unchanged.

#include <cassert>

#include "../support/eq_inline.cuh"
#include "coefficient_vm.cuh"

__device__ __constant__ e4 ab_gkr_bwd_coeff_fold_factors[airbender::prover::gkr::BWD_COEFF_FOLD_FACTOR_CAP];

namespace airbender::prover::gkr {

// Coefficient banks (section 9.3). The bank is selected launch-wide; no term or
// value operand carries an address-space tag.
//
// Index 0 is `+1` and index 1 is `-1` — reserved literals that let the executor
// use add/FMA or subtract/FMS with no E4 coefficient multiplication at all. A
// bank entry `i` is index `BWD_COEFF_INDEX_RESERVED + i`.

// Reads the incumbent stream-ordered `__constant__` bank. Direct symbol access
// is required for LDC emission, so this loader is not templated.
struct coeff_bank_constant {
  DEVICE_FORCEINLINE e4 operator[](const u16 index) const { return ::ab_gkr_flat_coefficients[index - BWD_COEFF_INDEX_RESERVED]; }
};

// Reads the descriptor's single coefficient pointer. The constant
// specialization ignores that pointer entirely.
struct coeff_bank_pointer {
  const e4 *base;
  DEVICE_FORCEINLINE e4 operator[](const u16 index) const { return load<e4, ld_modifier::ca>(base, index - BWD_COEFF_INDEX_RESERVED); }
};

// The one place a coefficient index becomes a value: the two reserved literals
// never touch a bank.
template <typename Bank> DEVICE_FORCEINLINE e4 coefficient_value(const Bank &bank, const u16 index) {
  if (index == BWD_COEFF_INDEX_ONE)
    return e4::ONE();
  if (index == BWD_COEFF_INDEX_NEG_ONE) {
    constexpr e4 minus_one = e4::from_scalar(bf::neg(bf::ONE()));
    return minus_one;
  }
  return bank[index];
}

// Each thread owns a private cell file of `cell_budget` E4 cells. Within a warp
// the file is transposed so a typed access is one stride-32 index in the typed
// array: `thread_bf[bf_lane << 5]` and `thread_e4[e4_bucket << 5]`. An E4 cell
// is four consecutive BF lanes, so `e4_bucket = bf_lane >> 2` and an E4 lane
// must be four-aligned.
struct cell_file {
  bf *bf_lanes;
  e4 *e4_cells;
};

DEVICE_FORCEINLINE cell_file thread_cell_file(e4 *dynamic_cells, const u32 cell_budget) {
  const u32 lane = threadIdx.x & BWD_COEFF_LANE_INDEX_MASK;
  const u32 warp = threadIdx.x >> BWD_COEFF_WARP_SHIFT;
  e4 *warp_base = dynamic_cells + static_cast<size_t>(warp) * cell_budget * BWD_COEFF_WARP_LANES;
  return cell_file{reinterpret_cast<bf *>(warp_base) + lane, warp_base + lane};
}

// The two views are different addressings of the same bytes, NOT aliases of each
// other: BF lane `4k + j` and E4 cell `k` are one storage location in the
// ENCODING's index space, but here BF lane L sits at `L * 32 + lane` BF slots
// while E4 cell k sits at `k * 32 + lane` E4 slots. Both views cover exactly the
// warp's `cell_budget * 32` E4 slots, so neither can leave the block's dynamic
// shared memory, and the difference is unobservable because the warp decodes ONE
// warp-uniform stream: a lane is live at exactly one width for every thread at
// the same time, and the host placer plus `check_lane` never let a value be
// written at one width and read at the other.
DEVICE_FORCEINLINE bf cell_read_bf(const cell_file &cells, const u32 lane) { return cells.bf_lanes[lane << BWD_COEFF_WARP_SHIFT]; }

DEVICE_FORCEINLINE void cell_write_bf(const cell_file &cells, const u32 lane, const bf value) { cells.bf_lanes[lane << BWD_COEFF_WARP_SHIFT] = value; }

// Four-lane alignment is REQUIRED, not assumed. A misaligned lane would silently
// resolve to the containing cell and read a neighbouring value, so it is
// rejected on the host (`gkr_eval_isa`'s `check_lane`) and reported by the probe
// kernel below; this assertion is the last line of defence for a hand-built
// descriptor in any build that keeps assertions enabled.
DEVICE_FORCEINLINE u32 cell_e4_bucket(const u32 lane) {
  assert((lane & (BWD_COEFF_LANES_PER_CELL - 1)) == 0);
  return lane >> BWD_COEFF_LANES_PER_CELL_LOG2;
}

// ONE 16-byte vector access, never four limb accesses.
DEVICE_FORCEINLINE e4 cell_read_e4(const cell_file &cells, const u32 lane) { return load<e4>(cells.e4_cells, cell_e4_bucket(lane) << BWD_COEFF_WARP_SHIFT); }

DEVICE_FORCEINLINE void cell_write_e4(const cell_file &cells, const u32 lane, const e4 &value) {
  store<e4>(cells.e4_cells, value, cell_e4_bucket(lane) << BWD_COEFF_WARP_SHIFT);
}

// ── Typed source resolution (section 10) ────────────────────────────────────
//
// The BF and E4 resolvers are genuinely separate: nothing on the BF path
// constructs, holds or returns an E4. That is the whole point of section 10.1's
// "BF helpers never carry E4 temporaries" — a BF R0 term must cost four bytes of
// traffic and a BF subtract, not a lift.

// The two RAW endpoints of one source at target depth (section 4: `S(X) = s0 +
// X * ds`). Kept raw because section 10.3 publishes endpoints, not projections.
struct bf_endpoints {
  bf s0;
  bf s1;
};

struct e4_endpoints {
  e4 s0;
  e4 s1;
};

// One resolved operand slot, at the operand's OWN width. Only the projections
// the term's role consumes are meaningful.
struct bf_value {
  bf endpoint0;
  bf delta;
};

struct e4_value {
  e4 endpoint0;
  e4 delta;
};

DEVICE_FORCEINLINE const bf *window_bf_column(const bwd_coeff_source_window &window, const u32 column) {
  return reinterpret_cast<const bf *>(window.read_base + static_cast<size_t>(column) * window.read_stride_bytes);
}

DEVICE_FORCEINLINE const e4 *window_e4_column(const bwd_coeff_source_window &window, const u32 column) {
  return reinterpret_cast<const e4 *>(window.read_base + static_cast<size_t>(column) * window.read_stride_bytes);
}

DEVICE_FORCEINLINE e4 *window_publish_column(const bwd_coeff_source_window &window, const u32 column) {
  return reinterpret_cast<e4 *>(window.publish_base + static_cast<size_t>(column) * window.publish_stride_bytes);
}

// One raw BF element of the window's backing.
//
// A procedural (virtual-setup) window has no matrix: its value is produced from
// the backing INDEX, which is what keeps virtual sources row-dependent
// (section 10.3). Scratch is an ordinary read-only witness-generation backing
// and takes the matrix path like any other read.
DEVICE_FORCEINLINE bf window_backing_bf(const bwd_coeff_source_window &window, const u32 column, const u32 index) {
  if (window.origin == BWD_COEFF_ORIGIN_PROCEDURAL)
    return gkr_virtual_base_value(bwd_coeff_procedural_source_kind(window.procedural_kind), index);
  return load<bf, ld_modifier::cs>(window_bf_column(window, column), index);
}

// The two backing shapes a lazy fold can accumulate over. Each contributes ONE
// weighted element to the running E4 accumulator, so the fold loop below never
// learns which backing it is walking.
struct bf_backing {
  const bwd_coeff_source_window &window;
  u32 column;
  DEVICE_FORCEINLINE e4 accumulate(const e4 factor, const u32 index, const e4 acc) const {
    return e4::fma(factor, window_backing_bf(window, column, index), acc);
  }
};

struct e4_backing {
  const bwd_coeff_source_window &window;
  u32 column;
  DEVICE_FORCEINLINE e4 accumulate(const e4 factor, const u32 index, const e4 acc) const {
    return e4::fma(factor, load<e4, ld_modifier::cs>(window_e4_column(window, column), index), acc);
  }
};

// The backing offset of fold leaf `leaf` at catch-up distance `delta`.
//
// Leaf bit k weights `round_challenges[backing_depth + k]`
// (`ab_gkr_bwd_coeff_build_fold_factors_kernel`), and fold step k halves the
// level it starts from, so bit k moves by `(2 * rows) << (delta - 1 - k)` — i.e.
// the leaf's BIT-REVERSED value times the target-depth span. This is the
// incumbent split-halves layout, not an interleaving.
DEVICE_FORCEINLINE u32 fold_leaf_offset(const u32 leaf, const u32 delta, const u32 span) { return (__brev(leaf) >> (32u - delta)) * span; }

DEVICE_FORCEINLINE u32 fold_factor_base(const u32 delta) { return delta == 1 ? BWD_COEFF_FOLD_FACTOR_SHALLOW_BASE : BWD_COEFF_FOLD_FACTOR_DEEP_BASE; }

// Catch ONE endpoint up from the window's backing to target depth.
//
// This is the bounded lazy resolver, and it is a LOOP over the runtime
// fold-factor table — never an expanded pairwise fold tree. Exactly one E4
// accumulator is register-live at any depth, so D3 costs D0's registers plus a
// compile-time-bounded loop. `lower_bwd_coeff` guarantees `delta <= FOLD_DEPTH`.
template <u32 FOLD_DEPTH, typename Backing> DEVICE_FORCEINLINE e4 fold_endpoint(const Backing &backing, const u32 index, const u32 rows, const u32 delta) {
  const u32 leaves = 1u << delta;
  const u32 base = fold_factor_base(delta);
  const u32 span = rows << 1;
  e4 acc = e4::ZERO();
#pragma unroll
  for (u32 leaf = 0; leaf < (1u << FOLD_DEPTH); leaf++) {
    if (leaf >= leaves)
      break;
    acc = backing.accumulate(::ab_gkr_bwd_coeff_fold_factors[base + leaf], index + fold_leaf_offset(leaf, delta, span), acc);
  }
  return acc;
}

// Both endpoints in ONE pass, so the leaf weight is fetched once per leaf.
template <u32 FOLD_DEPTH, typename Backing>
DEVICE_FORCEINLINE e4_endpoints fold_endpoint_pair(const Backing &backing, const u32 row, const u32 rows, const u32 delta) {
  const u32 leaves = 1u << delta;
  const u32 base = fold_factor_base(delta);
  const u32 span = rows << 1;
  e4 s0 = e4::ZERO();
  e4 s1 = e4::ZERO();
#pragma unroll
  for (u32 leaf = 0; leaf < (1u << FOLD_DEPTH); leaf++) {
    if (leaf >= leaves)
      break;
    const e4 factor = ::ab_gkr_bwd_coeff_fold_factors[base + leaf];
    const u32 offset = fold_leaf_offset(leaf, delta, span);
    s0 = backing.accumulate(factor, row + offset, s0);
    s1 = backing.accumulate(factor, rows + row + offset, s1);
  }
  return e4_endpoints{s0, s1};
}

// ── R0 BF resolution (section 10.1) ─────────────────────────────────────────
//
// A BF operand only ever exists in R0, where `bwd_coeff_fold_depth(0) == 0`
// pins the backing AT the target depth and section 10.2's static policy never
// publishes (`target_depth 0 < 3`). So: no fold, no publication, no E4.

DEVICE_FORCEINLINE bf bf_endpoint(const bwd_coeff_source_window &window, const u32 column, const u32 row, const u32 rows, const u32 which) {
  return window_backing_bf(window, column, row + which * rows);
}

DEVICE_FORCEINLINE bf_endpoints bf_endpoint_pair(const bwd_coeff_source_window &window, const u32 column, const u32 row, const u32 rows) {
  return bf_endpoints{bf_endpoint(window, column, row, rows, 0), bf_endpoint(window, column, row, rows, 1)};
}

// ── E4 resolution (sections 10.1, 10.2, 10.3) ───────────────────────────────

// One raw target-depth E4 endpoint out of a backing that is ALREADY at target
// depth. An extension backing is one 16-byte vector load; a base backing at
// distance zero is the deliberate BF -> E4 lift.
DEVICE_FORCEINLINE e4 e4_direct_endpoint(const bwd_coeff_source_window &window, const u32 column, const u32 index) {
  if (window.origin == BWD_COEFF_ORIGIN_READ_EXT)
    return load<e4, ld_modifier::cs>(window_e4_column(window, column), index);
  return e4::from_scalar(window_backing_bf(window, column, index));
}

// ONE raw target-depth endpoint.
//
// PRECONDITION: this access does not publish — either the source does not
// materialize, or this is not its marked first access. A first access publishes
// BOTH endpoints (section 10.3), so it must go through `e4_endpoint_pair`.
template <u32 FOLD_DEPTH>
DEVICE_FORCEINLINE e4 e4_endpoint(const bwd_coeff_source_window &window, const u32 column, const u32 row, const u32 rows, const u32 which) {
  const u32 index = row + which * rows;
  if (window.materialize != 0)
    return load<e4, ld_modifier::cs>(window_publish_column(window, column), index);
  const u32 delta = window.target_depth - window.backing_depth;
  if (delta == 0)
    return e4_direct_endpoint(window, column, index);
  if (window.origin == BWD_COEFF_ORIGIN_READ_EXT)
    return fold_endpoint<FOLD_DEPTH>(e4_backing{window, column}, index, rows, delta);
  return fold_endpoint<FOLD_DEPTH>(bf_backing{window, column}, index, rows, delta);
}

// Both raw target-depth endpoints, honouring section 10.3's first access: the
// marked physical resolution catches up and PUBLISHES both, and every later
// access reads the published backing instead of folding again.
template <u32 FOLD_DEPTH>
DEVICE_FORCEINLINE e4_endpoints e4_endpoint_pair(const bwd_coeff_source_window &window, const u32 column, const u32 row, const u32 rows,
                                                 const bool first_access) {
  const bool materialize = window.materialize != 0;
  if (materialize && !first_access) {
    const e4 *published = window_publish_column(window, column);
    return e4_endpoints{load<e4, ld_modifier::cs>(published, row), load<e4, ld_modifier::cs>(published, rows + row)};
  }
  const u32 delta = window.target_depth - window.backing_depth;
  e4_endpoints out;
  if (delta == 0)
    out = e4_endpoints{e4_direct_endpoint(window, column, row), e4_direct_endpoint(window, column, rows + row)};
  else if (window.origin == BWD_COEFF_ORIGIN_READ_EXT)
    out = fold_endpoint_pair<FOLD_DEPTH>(e4_backing{window, column}, row, rows, delta);
  else
    out = fold_endpoint_pair<FOLD_DEPTH>(bf_backing{window, column}, row, rows, delta);
  if (materialize) {
    // Each thread owns one logical row and exactly one resolution is marked
    // first, so the two stores have a single writer. `wb` keeps them in L1 for
    // the later same-thread direct reads above.
    e4 *published = window_publish_column(window, column);
    store<e4, st_modifier::wb>(published, out.s0, row);
    store<e4, st_modifier::wb>(published, out.s1, rows + row);
  }
  return out;
}

// ── Typed value-use resolution (section 8) ──────────────────────────────────

// BF value use. R0 only; see the BF resolution note above for why there is no
// fold path and no publication here.
DEVICE_FORCEINLINE bf_value resolve_use_bf(const bwd_coeff_desc &desc, const bwd_coeff_input &in, const u32 role, const u32 row, const cell_file &cells) {
  const u32 rows = desc.logical_rows;
  if (in.mode == BWD_COEFF_MODE_CELL) {
    // The single form carries the ROLE's projection, whichever it is. A BF
    // operand is never a native dual factor, so there is no packed pair here.
    const bf value = cell_read_bf(cells, in.endpoint0_lane);
    return role == BWD_COEFF_ROLE_ENDPOINT0 ? bf_value{value, bf::ZERO()} : bf_value{bf::ZERO(), value};
  }
  const bwd_coeff_source_window &window = desc.source_windows[in.window];
  if (in.mode == BWD_COEFF_MODE_PLANNED_SOURCE) {
    const bool resident_endpoint0 = in.endpoint0_action == BWD_COEFF_ACTION_USE_RESIDENT;
    const bool resident_delta = in.delta_action == BWD_COEFF_ACTION_USE_RESIDENT;
    // Read phase, strictly before the write phase: that is what lets a delta
    // overwrite the endpoint lane it was computed from.
    bf endpoint0 = resident_endpoint0 ? cell_read_bf(cells, in.endpoint0_lane) : bf::ZERO();
    bf delta = resident_delta ? cell_read_bf(cells, in.delta_lane) : bf::ZERO();
    if (!resident_endpoint0 || !resident_delta) {
      if (resident_endpoint0) {
        // Section 10.2: a resident Endpoint0 means loading only endpoint one.
        delta = bf::sub(bf_endpoint(window, in.column, row, rows, 1), endpoint0);
      } else {
        const bf_endpoints endpoints = bf_endpoint_pair(window, in.column, row, rows);
        endpoint0 = endpoints.s0;
        if (!resident_delta)
          delta = bf::sub(endpoints.s1, endpoints.s0);
      }
    }
    if (in.endpoint0_action == BWD_COEFF_ACTION_FILL)
      cell_write_bf(cells, in.endpoint0_lane, endpoint0);
    if (in.delta_action == BWD_COEFF_ACTION_FILL)
      cell_write_bf(cells, in.delta_lane, delta);
    return bf_value{endpoint0, delta};
  }
  bf_value out;
  if (role == BWD_COEFF_ROLE_ENDPOINT0) {
    // Section 10.1: an Endpoint0 use loads exactly ONE native-width value.
    out = bf_value{bf_endpoint(window, in.column, row, rows, 0), bf::ZERO()};
  } else {
    const bf_endpoints endpoints = bf_endpoint_pair(window, in.column, row, rows);
    out = bf_value{endpoints.s0, bf::sub(endpoints.s1, endpoints.s0)};
  }
  if (in.mode == BWD_COEFF_MODE_FILL_SOURCE)
    cell_write_bf(cells, in.dst_lane, role == BWD_COEFF_ROLE_ENDPOINT0 ? out.endpoint0 : out.delta);
  return out;
}

// E4 value use, with the bounded D0..D3 lazy fold and section 10.3's first
// access behind `e4_endpoint` / `e4_endpoint_pair`.
template <u32 FOLD_DEPTH>
DEVICE_FORCEINLINE e4_value resolve_use_e4(const bwd_coeff_desc &desc, const bwd_coeff_input &in, const u32 role, const u32 row, const cell_file &cells) {
  const u32 rows = desc.logical_rows;
  if (in.mode == BWD_COEFF_MODE_CELL) {
    const e4 value = cell_read_e4(cells, in.endpoint0_lane);
    if (role == BWD_COEFF_ROLE_PAIR)
      return e4_value{value, cell_read_e4(cells, in.delta_lane)};
    return role == BWD_COEFF_ROLE_ENDPOINT0 ? e4_value{value, e4::ZERO()} : e4_value{e4::ZERO(), value};
  }
  const bwd_coeff_source_window &window = desc.source_windows[in.window];
  const bool publish_here = in.first_access && window.materialize != 0;
  if (in.mode == BWD_COEFF_MODE_PLANNED_SOURCE) {
    const bool resident_endpoint0 = in.endpoint0_action == BWD_COEFF_ACTION_USE_RESIDENT;
    const bool resident_delta = in.delta_action == BWD_COEFF_ACTION_USE_RESIDENT;
    e4 endpoint0 = resident_endpoint0 ? cell_read_e4(cells, in.endpoint0_lane) : e4::ZERO();
    e4 delta = resident_delta ? cell_read_e4(cells, in.delta_lane) : e4::ZERO();
    if (!resident_endpoint0 || !resident_delta) {
      if (resident_endpoint0 && !publish_here) {
        delta = e4::sub(e4_endpoint<FOLD_DEPTH>(window, in.column, row, rows, 1), endpoint0);
      } else {
        const e4_endpoints endpoints = e4_endpoint_pair<FOLD_DEPTH>(window, in.column, row, rows, in.first_access);
        if (!resident_endpoint0)
          endpoint0 = endpoints.s0;
        if (!resident_delta)
          delta = e4::sub(endpoints.s1, endpoints.s0);
      }
    }
    if (in.endpoint0_action == BWD_COEFF_ACTION_FILL)
      cell_write_e4(cells, in.endpoint0_lane, endpoint0);
    if (in.delta_action == BWD_COEFF_ACTION_FILL)
      cell_write_e4(cells, in.delta_lane, delta);
    return e4_value{endpoint0, delta};
  }
  e4_value out;
  if (role == BWD_COEFF_ROLE_ENDPOINT0 && !publish_here) {
    out = e4_value{e4_endpoint<FOLD_DEPTH>(window, in.column, row, rows, 0), e4::ZERO()};
  } else {
    const e4_endpoints endpoints = e4_endpoint_pair<FOLD_DEPTH>(window, in.column, row, rows, in.first_access);
    out = e4_value{endpoints.s0, e4::sub(endpoints.s1, endpoints.s0)};
  }
  if (in.mode == BWD_COEFF_MODE_FILL_SOURCE)
    cell_write_e4(cells, in.dst_lane, role == BWD_COEFF_ROLE_ENDPOINT0 ? out.endpoint0 : out.delta);
  return out;
}

// REGIME_IS_R0 and FOLD_DEPTH are the section 11 specialization axes; the cell
// budget is runtime launch metadata, so one instantiation covers c2..c16.
template <bool REGIME_IS_R0, u32 FOLD_DEPTH, typename Bank> DEVICE_FORCEINLINE void coefficient_body(const bwd_coeff_desc &desc, const Bank &bank) {
  static_assert(FOLD_DEPTH <= BWD_COEFF_MAX_FOLD_DEPTH, "fold depth outside D0..D3");
  static_assert(!REGIME_IS_R0 || FOLD_DEPTH == 0, "R0 never folds: FoldDepth is a continuation-only axis");

  extern __shared__ e4 bwd_coeff_cells_dyn[];
  const cell_file cells = thread_cell_file(bwd_coeff_cells_dyn, desc.cell_budget);

  // One thread per logical row; BWD_COEFF_ROWS_PER_BLOCK rows per block.
  const size_t logical_row = static_cast<size_t>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (logical_row >= desc.logical_rows)
    return;

  e4 acc_c0 = desc.c_init == BWD_COEFF_C_INIT_NONE ? e4::ZERO() : coefficient_value(bank, desc.c_init);
  e4 acc_c2 = e4::ZERO();

  // TASK 11 inserts the sequential u16 decode loop over
  // `desc.program[0 .. desc.num_words)` here — warp-uniform and never randomly
  // accessed. `cells` is its private file; `resolve_use_bf` and
  // `resolve_use_e4<FOLD_DEPTH>` above are its typed source resolvers, and
  // `bwd_coeff_role` / `bwd_coeff_arity` / `bwd_coeff_operand_is_e4` turn a
  // decoded header opcode into the shape they need.
  (void)cells;

  // `lower_bwd_coeff` rejects a null `contributions` or `eq_low`
  // (BwdCoeffLowerError::NullRuntimePointer), so this is defence in depth
  // against a hand-built descriptor, NOT a supported "evaluate but do not
  // store" mode. Silently producing nothing is the safest response a release
  // kernel can give: it has no error channel.
  if (desc.contributions == nullptr || desc.eq_low == nullptr)
    return;
  const e4 eq = gkr_compute_eq_inline<e4>(desc.eq_low, desc.eq_sizes, static_cast<u32>(logical_row));
  store<e4, st_modifier::cs>(desc.contributions, e4::mul(eq, acc_c0), logical_row);
  store<e4, st_modifier::cs>(desc.contributions + desc.logical_rows, e4::mul(eq, acc_c2), logical_row);
}

template <bool REGIME_IS_R0, u32 FOLD_DEPTH> DEVICE_FORCEINLINE void coefficient_body_constant(const bwd_coeff_desc &desc) {
  coefficient_body<REGIME_IS_R0, FOLD_DEPTH>(desc, coeff_bank_constant{});
}

template <bool REGIME_IS_R0, u32 FOLD_DEPTH> DEVICE_FORCEINLINE void coefficient_body_pointer(const bwd_coeff_desc &desc) {
  coefficient_body<REGIME_IS_R0, FOLD_DEPTH>(desc, coeff_bank_pointer{desc.coefficients});
}

// ── Validation-only source probe (sections 10, 12) ──────────────────────────
//
// This is the ONLY place in this file that validates anything. Release kernels
// trust validated artifacts (section 12), so every check below stays here.

DEVICE_FORCEINLINE u32 probe_lane_flags(const u32 lane, const bool operand_is_e4, const u32 lanes) {
  u32 flags = 0;
  if (operand_is_e4 && (lane & (BWD_COEFF_LANES_PER_CELL - 1)) != 0)
    flags |= BWD_COEFF_PROBE_ERR_MISALIGNED_E4_LANE;
  if (lane + (operand_is_e4 ? BWD_COEFF_LANES_PER_CELL : 1u) > lanes)
    flags |= BWD_COEFF_PROBE_ERR_LANE_OUT_OF_BUDGET;
  return flags;
}

DEVICE_FORCEINLINE u32 probe_plan_action_flags(const u16 action, const u16 lane, const bool operand_is_e4, const u32 lanes) {
  if (action == BWD_COEFF_ACTION_INVALID)
    return BWD_COEFF_PROBE_ERR_PLAN_ACTION_INVALID;
  if (action == BWD_COEFF_ACTION_DIRECT)
    return 0;
  return probe_lane_flags(lane, operand_is_e4, lanes);
}

// Everything a release resolver is allowed to assume about ONE input record.
template <u32 FOLD_DEPTH>
DEVICE_FORCEINLINE u32 probe_input_flags(const bwd_coeff_desc &desc, const bwd_coeff_input &in, const u32 role, const bool operand_is_e4, const u32 lanes) {
  if (in.mode == BWD_COEFF_MODE_CELL) {
    u32 flags = probe_lane_flags(in.endpoint0_lane, operand_is_e4, lanes);
    if (role == BWD_COEFF_ROLE_PAIR)
      flags |= probe_lane_flags(in.delta_lane, operand_is_e4, lanes);
    return flags;
  }
  if (in.window >= desc.n_source_windows)
    return BWD_COEFF_PROBE_ERR_WINDOW_OUT_OF_RANGE;
  const bwd_coeff_source_window &window = desc.source_windows[in.window];
  u32 flags = 0;
  // The runtime factor bank holds exactly the depth-1 pair and one depth-D table
  // (section 10.2), so those plus "already at target depth" are the only legal
  // catch-up distances.
  if (window.target_depth < window.backing_depth) {
    flags |= BWD_COEFF_PROBE_ERR_UNSUPPORTED_FOLD_DELTA;
  } else {
    const u32 delta = window.target_depth - window.backing_depth;
    if (delta != 0 && delta != 1 && delta != FOLD_DEPTH)
      flags |= BWD_COEFF_PROBE_ERR_UNSUPPORTED_FOLD_DELTA;
    if (delta > FOLD_DEPTH)
      flags |= BWD_COEFF_PROBE_ERR_UNSUPPORTED_FOLD_DELTA;
  }
  if (in.mode == BWD_COEFF_MODE_FILL_SOURCE) {
    if (role == BWD_COEFF_ROLE_PAIR)
      flags |= BWD_COEFF_PROBE_ERR_MODE_ILLEGAL_FOR_ROLE;
    flags |= probe_lane_flags(in.dst_lane, operand_is_e4, lanes);
  } else if (in.mode == BWD_COEFF_MODE_PLANNED_SOURCE) {
    if (role == BWD_COEFF_ROLE_ENDPOINT0)
      flags |= BWD_COEFF_PROBE_ERR_MODE_ILLEGAL_FOR_ROLE;
    flags |= probe_plan_action_flags(in.endpoint0_action, in.endpoint0_lane, operand_is_e4, lanes);
    flags |= probe_plan_action_flags(in.delta_action, in.delta_lane, operand_is_e4, lanes);
  }
  return flags;
}

template <bool REGIME_IS_R0, u32 FOLD_DEPTH>
DEVICE_FORCEINLINE void source_probe_body(const bwd_coeff_desc &desc, const bwd_coeff_probe_record *records, const u32 n_records, e4 *endpoint0_out,
                                          e4 *delta_out, u32 *error) {
  extern __shared__ e4 bwd_coeff_cells_dyn[];
  const cell_file cells = thread_cell_file(bwd_coeff_cells_dyn, desc.cell_budget);
  const u32 row = blockIdx.x * blockDim.x + threadIdx.x;
  if (row >= desc.logical_rows)
    return;
  const u32 lanes = desc.cell_budget * BWD_COEFF_LANES_PER_CELL;

  for (u32 index = 0; index < n_records; index++) {
    const u16 opcode = records[index].opcode;
    const u32 pc = records[index].word;
    u32 flags = 0;
    if (!bwd_coeff_opcode_is_live(REGIME_IS_R0, opcode))
      flags |= BWD_COEFF_PROBE_ERR_DEAD_OPCODE;
    else if (bwd_coeff_is_move(REGIME_IS_R0, opcode))
      flags |= BWD_COEFF_PROBE_ERR_MOVE_OPCODE;
    // Four words is the longest operand list any live opcode has, so this bounds
    // every `desc.program` read the decode below performs.
    if (pc + 4 > BWD_COEFF_PROGRAM_WORD_CAP)
      flags |= BWD_COEFF_PROBE_ERR_PROGRAM_OUT_OF_RANGE;
    if (flags != 0) {
      atomicOr(error, flags);
      continue;
    }

    const u32 role = bwd_coeff_role(REGIME_IS_R0, opcode);
    const u32 arity = bwd_coeff_arity(REGIME_IS_R0, opcode);
    const bool pair_form = bwd_coeff_cell_word_is_pair_form(REGIME_IS_R0, opcode);
    const bwd_coeff_input first = bwd_coeff_decode_input(desc.program, pc, pair_form);
    bwd_coeff_input second = first;
    bool squared = false;
    u32 words = first.words;
    if (arity == 2) {
      second = bwd_coeff_decode_input(desc.program, pc + first.words, pair_form);
      words += second.words;
      // Section 9.1: byte-identical input records denote a SQUARED term. The
      // operand is resolved once and consumed twice; re-executing the second
      // copy is unsafe, not merely wasteful.
      squared = second.words == first.words;
      for (u32 word = 0; squared && word < first.words; word++)
        squared = desc.program[pc + word] == desc.program[pc + first.words + word];
    }
    if (pc + words > desc.num_words) {
      atomicOr(error, BWD_COEFF_PROBE_ERR_PROGRAM_OUT_OF_RANGE);
      continue;
    }

    e4 endpoint0[BWD_COEFF_PROBE_OPERANDS];
    e4 delta[BWD_COEFF_PROBE_OPERANDS];
    for (u32 position = 0; position < arity; position++) {
      if (position == 1 && squared) {
        endpoint0[1] = endpoint0[0];
        delta[1] = delta[0];
        break;
      }
      const bwd_coeff_input &in = position == 0 ? first : second;
      const bool operand_is_e4 = bwd_coeff_operand_is_e4(REGIME_IS_R0, opcode, position);
      const u32 input_flags = probe_input_flags<FOLD_DEPTH>(desc, in, role, operand_is_e4, lanes);
      if (input_flags != 0) {
        atomicOr(error, input_flags);
        flags |= input_flags;
        break;
      }
      if (operand_is_e4) {
        const e4_value value = resolve_use_e4<FOLD_DEPTH>(desc, in, role, row, cells);
        endpoint0[position] = value.endpoint0;
        delta[position] = value.delta;
      } else {
        const bf_value value = resolve_use_bf(desc, in, role, row, cells);
        // The lift is the PROBE's, for a uniform output buffer. The BF resolver
        // itself never sees an E4.
        endpoint0[position] = e4::from_scalar(value.endpoint0);
        delta[position] = e4::from_scalar(value.delta);
      }
    }
    if (flags != 0)
      continue;

    for (u32 position = 0; position < BWD_COEFF_PROBE_OPERANDS; position++) {
      const u32 source = position < arity ? position : arity - 1;
      const u32 slot = (index * BWD_COEFF_PROBE_OPERANDS + position) * desc.logical_rows + row;
      store<e4, st_modifier::cs>(endpoint0_out, endpoint0[source], slot);
      store<e4, st_modifier::cs>(delta_out, delta[source], slot);
    }
  }
}

} // namespace airbender::prover::gkr

EXTERN __global__ void ab_gkr_bwd_coeff_build_fold_factors_kernel(const e4 *round_challenges, const u32 target_depth, const u32 fold_depth, e4 *fold_factors) {
  using namespace airbender::primitives::field;
  const u32 slot = threadIdx.x;
  u32 delta;
  u32 leaf;
  if (slot < 2) {
    delta = 1;
    leaf = slot;
  } else {
    if (fold_depth < 2 || slot >= 2 + (1u << fold_depth))
      return;
    delta = fold_depth;
    leaf = slot - 2;
  }
  if (target_depth < delta)
    return;

  const u32 backing_depth = target_depth - delta;
  const e4 first_challenge = round_challenges[backing_depth];
  e4 factor = (leaf & 1u) != 0 ? first_challenge : e4::sub(e4::ONE(), first_challenge);
  for (u32 round = 1; round < delta; round++) {
    const e4 challenge = round_challenges[backing_depth + round];
    const e4 term = ((leaf >> round) & 1u) != 0 ? challenge : e4::sub(e4::ONE(), challenge);
    factor = e4::mul(factor, term);
  }
  fold_factors[slot] = factor;
}

#define AB_GKR_BWD_COEFF_KERNEL(symbol, regime_is_r0, fold_depth, body)                                                                                        \
  EXTERN __launch_bounds__(airbender::prover::gkr::BWD_COEFF_THREADS_PER_BLOCK)                                                                                \
      __global__ void symbol(const __grid_constant__ airbender::prover::gkr::bwd_coeff_desc desc) {                                                            \
    airbender::prover::gkr::body<regime_is_r0, fold_depth>(desc);                                                                                              \
  }

AB_GKR_BWD_COEFF_KERNEL(ab_gkr_bwd_coeff_r0_const_kernel, true, 0, coefficient_body_constant)
AB_GKR_BWD_COEFF_KERNEL(ab_gkr_bwd_coeff_r0_ptr_kernel, true, 0, coefficient_body_pointer)
AB_GKR_BWD_COEFF_KERNEL(ab_gkr_bwd_coeff_ext_d0_const_kernel, false, 0, coefficient_body_constant)
AB_GKR_BWD_COEFF_KERNEL(ab_gkr_bwd_coeff_ext_d0_ptr_kernel, false, 0, coefficient_body_pointer)
AB_GKR_BWD_COEFF_KERNEL(ab_gkr_bwd_coeff_ext_d1_const_kernel, false, 1, coefficient_body_constant)
AB_GKR_BWD_COEFF_KERNEL(ab_gkr_bwd_coeff_ext_d1_ptr_kernel, false, 1, coefficient_body_pointer)
AB_GKR_BWD_COEFF_KERNEL(ab_gkr_bwd_coeff_ext_d2_const_kernel, false, 2, coefficient_body_constant)
AB_GKR_BWD_COEFF_KERNEL(ab_gkr_bwd_coeff_ext_d2_ptr_kernel, false, 2, coefficient_body_pointer)
AB_GKR_BWD_COEFF_KERNEL(ab_gkr_bwd_coeff_ext_d3_const_kernel, false, 3, coefficient_body_constant)
AB_GKR_BWD_COEFF_KERNEL(ab_gkr_bwd_coeff_ext_d3_ptr_kernel, false, 3, coefficient_body_pointer)

#undef AB_GKR_BWD_COEFF_KERNEL

// The validation-only source probe. `regime_is_r0` and `fold_depth` are runtime
// parameters rather than a symbol-per-specialization matrix: the probe is off
// every hot path, and one symbol keeps the test side from mirroring the release
// launch table it is meant to be independent of.
EXTERN __launch_bounds__(airbender::prover::gkr::BWD_COEFF_THREADS_PER_BLOCK) __global__
    void ab_gkr_bwd_coeff_source_probe_kernel(const __grid_constant__ airbender::prover::gkr::bwd_coeff_desc desc, const u32 regime_is_r0, const u32 fold_depth,
                                              const airbender::prover::gkr::bwd_coeff_probe_record *records, const u32 n_records, e4 *endpoint0_out,
                                              e4 *delta_out, u32 *error) {
  using namespace airbender::prover::gkr;
  if (regime_is_r0 != 0) {
    // R0 never folds: `bwd_coeff_fold_depth(0) == 0` is the only legal pairing.
    if (fold_depth != 0) {
      atomicOr(error, BWD_COEFF_PROBE_ERR_UNSUPPORTED_FOLD_DELTA);
      return;
    }
    source_probe_body<true, 0>(desc, records, n_records, endpoint0_out, delta_out, error);
    return;
  }
  switch (fold_depth) {
  case 0:
    source_probe_body<false, 0>(desc, records, n_records, endpoint0_out, delta_out, error);
    break;
  case 1:
    source_probe_body<false, 1>(desc, records, n_records, endpoint0_out, delta_out, error);
    break;
  case 2:
    source_probe_body<false, 2>(desc, records, n_records, endpoint0_out, delta_out, error);
    break;
  case 3:
    source_probe_body<false, 3>(desc, records, n_records, endpoint0_out, delta_out, error);
    break;
  default:
    atomicOr(error, BWD_COEFF_PROBE_ERR_UNSUPPORTED_FOLD_DELTA);
    break;
  }
}
