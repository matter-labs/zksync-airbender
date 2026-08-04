//! Binding the backward VM's R0 sources to the production prover state.
//!
//! Every `ResolvedBwdCoeffSourceWindow` measured by the bench is synthetic:
//! [`seg_compile`]'s harness resolves windows against its own host storage
//! model (`upload_round_storage`). This module is the production half — the
//! same window geometry resolved against [`GpuGKRStorage`], through the SAME
//! accessors the flat path reads with (`try_get_base_poly` /
//! `try_get_ext_poly`, via the forward VM's
//! [`resolve_storage_column`]).
//!
//! # The add_sub L0 R0 source census
//!
//! Read off the compiled coordinate (`report_the_r0_source_census`): 8 windows,
//! 79 source slots over 79 referenced columns.
//!
//! | Family | windows | columns = slots |
//! |---|---|---|
//! | `BaseLayerWitness` | 1 | 22 |
//! | `BaseLayerMemory` | 1 | 17 |
//! | `LayerOutput` (ext) | 1 | 20 |
//! | `LayerOutput` (base) | 1 | 3 |
//! | `CacheOutput` (ext) | 1 | 10 |
//! | `CacheOutput` (base) | 1 | 5 |
//! | `VirtualSetup` (RangeCheck16Bits) | 1 | 1 |
//! | `VirtualSetup` (RangeCheckTimestamp) | 1 | 1 |
//!
//! `Setup` and `Scratch` do not occur — consistent with the corpus census
//! (`seg_publish_backing_census`: zero across all 114 coordinates), so
//! [`family_read_place`] maps them for totality but no binder behavior rests
//! on them. The two procedural windows are the corpus's usual pair; they bind
//! with no read pointer and the resolver synthesizes them from the row index.
//!
//! # Production storage is NOT window-contiguous — windows re-partition here
//!
//! The bench's host model backed each window with one contiguous allocation,
//! so window addressing (`base + column * stride`) held by construction.
//! Production storage breaks it two ways, both observed on the real add_sub
//! fixture:
//!
//!   * **Copy aliases.** A pure copy gate aliases its input:
//!     `InnerLayer { layer: 1, offset: 0 }` and `{ offset: 11 }` resolve INTO
//!     the base-layer memory matrix, while `{ offset: 20 }` is a real
//!     inner-layer write — one artifact window, three different matrices.
//!   * **Rank packing.** A consolidated per-(layer, class, field) matrix packs
//!     only the polys that exist in it, densely: `Cached { 0, offset: 7 }` and
//!     `{ offset: 14 }` sit ONE stride apart. The base-layer arenas are the
//!     opposite — absolute-indexed, holes physically present — so the SAME
//!     offset gap means a different pointer distance in each.
//!
//! So [`bind_r0_sources`] re-partitions and RENUMBERS: every referenced column
//! resolves independently, and each is assigned the dense offset its own
//! pointer implies ([`dense_step`]) rather than keeping the artifact's
//! numbering. A window needs a uniform stride, not a particular numbering, and
//! both layouts above are uniformly strided once the index comes from the
//! pointer — a rank-packed backing advances one offset per referenced column, an
//! arena advances by the physical gap, and neither has to split. add_sub L0 R0's
//! 8 artifact windows become 9 bound windows, the one extra being a genuinely
//! separate backing (a copy alias reading out of a different matrix).
//!
//! The program and its source SLOTS are untouched — the design spec's contract
//! is the source table ("slot ids into a per-launch source table; no
//! windows"), and the window partition was always a compression of it, so
//! re-forming windows against real geometry is a binder-local move with no ABI
//! or artifact-format change. The rebound coordinate
//! ([`BoundR0Sources::coord`]) is what `lower_bwd_seg` must be handed; the
//! original's windows no longer describe the bound pointers, and its columns are
//! dense offsets, not addresses — do not feed them back through
//! [`family_read_place`].
//!
//! # R0 publishes nothing
//!
//! At round 0 every window is at delta 0: [`assign_class`] gives
//! `(Bf, 0) -> BfDirect` and `(E4, 0) -> E4Direct`, both without a publish, and
//! a procedural window at delta 0 is `ProceduralInline`. So the publish plan is
//! structurally EMPTY, and [`bind_r0_sources`] asserts that
//! ([`BwdVmBindError::PublishPlanNotEmpty`]) rather than allocating a backing —
//! a non-empty plan at R0 means the depth wiring is wrong and must stop the
//! proof.
//!
//! # The closed-form `K` policy (moved from the bench)
//!
//! [`seg_policy_k`] and its two thresholds were `bench`-gated in `seg_report`;
//! the launcher needs them in production, so they moved here UNCHANGED. The
//! fit, the leave-one-circuit-out validation and every measured number backing
//! them stay in `seg_report` (bench-gated), which now imports the policy from
//! here so the fit and the shipped rule cannot drift apart.
//!
//! [`seg_compile`]: super::seg_compile
//! [`resolve_storage_column`]: crate::prover::gkr::forward::vm::production_bind::resolve_storage_column
//! [`assign_class`]: super::seg_lower::assign_class

use std::ptr::null_mut;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use gkr_eval_isa::bwd::coeff::lean_artifact::LeanCoordinateArtifact;
use gkr_eval_isa::bwd::coeff::lean_bind::{
    LeanBoundColumn, LeanBoundWindow, LeanSourceBinding, LeanSourceSlot,
};
use gkr_eval_isa::bwd::coeff::limits::SOURCE_WINDOW_COLUMNS;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::OnceLock;
use gkr_eval_isa::bwd::coeff::stats::WindowFamily;
use gkr_eval_isa::fwd::source::KIND_ORDER;

use super::production_program::CompiledSlice;
use super::seg::{
    bwd_seg_blocks_per_sm, bwd_seg_coeff_bank_device_ptr, launch_bwd_seg,
    launch_bwd_seg_build_fold_weights, BwdSegEpilogue,
};
use super::seg_coeff_eval::{
    build_seg_coeff_eval_tables, schedule_bwd_seg_coeff_bank_fill, SegCoeffEvalTables,
    BWD_SEG_CHALLENGE_CLAIM_BATCHING, BWD_SEG_CHALLENGE_LOOKUP_ADDITIVE,
    BWD_SEG_CHALLENGE_LOOKUP_MULTIPLICATIVE, BWD_SEG_CHALLENGE_PERM_LINEARIZATION_BASE,
    BWD_SEG_CHALLENGE_SLOTS,
};
use super::seg_desc::{
    BWD_COEFF_PUBLISH_TARGET_DEPTH, BWD_SEG_MAX_K, BWD_SEG_OUTPUT_PARTIALS, BWD_SEG_OUTPUT_ROWS,
    BWD_SEG_ADDR_SLOTS,
};
use super::seg_lower::{
    assign_class, lower_bwd_seg, plan_publish_scratch, BwdSegLowerError,
    BwdSegRoundBinding, BwdSegSetup, CoeffMode, D2Policy, ProgramMode, PublishScratchPlan,
    ResolvedAddrSlot, ResolvedPublishScratch, ResolvedSourceAddr, SourceClass, SourceOrigin,
};
use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::utils::WARP_SIZE;
use crate::primitives::context::DeviceAllocation;
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::backward::{make_eq_sizes, GkrEqSizes};
use crate::prover::gkr::forward::vm::lower::{read_place_to_gkr_address, ResolvedColumn};
use crate::prover::gkr::forward::vm::production_bind::resolve_storage_column;
use crate::prover::gkr::GpuGKRStorage;
use crate::prover::ProverContext;
use crate::upstream::{
    BwdRegime, Field, FieldKind, GKRAddress, ReadPlace, VirtualSetupKind, VirtualSetupPoly,
};

// ── The closed-form `K` policy (spec §12) ────────────────────────────────────

/// The `K` axis the corpus sweep ranked: the plan's set, minus `K = 24`.
///
/// Stage A extended its own axis DOWN to `{1, 2}` after the gate coordinate's
/// winner landed at the bottom of the named set. That is not repeated here and
/// the omission is a measurement, not an oversight: `K = 1` ran 4% behind the
/// incumbent on the gate coordinate (50% occupancy, no cross-warp amortization)
/// and `K = 2` lost to `K = 4` on every Stage-A cell it was launchable in.
///
/// `K = 24` is PRUNED (perf review P2): at the shipped 64-register band,
/// 768 threads × 64 regs = 49,152 keeps a second block (98,304) out of the 64K
/// register file, so K=24 runs 24 of 48 warp slots — 50% occupancy against 32
/// warps for each of its neighbors (2×16, 4×8, 1×32) — and every K=24 bench row
/// confirmed the 50% limit. The hole is geometric, not workload-dependent; the
/// entry returns only if the continuation band drops to ≤42 registers, where
/// two 768-thread blocks fit.
pub(crate) const SEG_CORPUS_K: [usize; 4] = [4, 8, 16, 32];

/// Below this per-row source footprint a coordinate takes the NARROW block.
///
/// 1,280 B/row is exactly 40 KiB per 32-row tile. **This is the scan optimum
/// ROUNDED, not the scan optimum.** `fit_policy_thresholds` (bench-gated, in
/// `seg_report`) over the corpus returns 1,248 B/row, which scores 78 points
/// over threshold at mean +0.6478% against this constant's 83 at +0.6784%. The
/// rounding is deliberate — a whole tile size is a number a reader can hold and
/// a launcher can justify, and the difference is five points out of 782, inside
/// the leave-one-circuit-out spread (`loco_validation`) — but it IS a
/// difference and the audit states it.
///
/// The neighbourhood is broad but not flat: 1,216–1,472 B/row all score 81–84.
pub(crate) const SEG_POLICY_NARROW_BYTES_PER_ROW: usize = 1_280;

/// Above this per-row source footprint a coordinate takes the WIDEST block its
/// family can host. 18,432 B/row is exactly 576 KiB per tile.
///
/// Same story: the scan optimum is 19,200 B/row, and it is a THREE-POINT SPIKE
/// rather than a plateau — the neighbouring candidates score worse. Rounding down
/// to a whole tile size trades those three points for a constant that is not
/// balanced on a spike in one dataset.
pub(crate) const SEG_POLICY_WIDE_BYTES_PER_ROW: usize = 18_432;

const _: () = assert!(SEG_POLICY_NARROW_BYTES_PER_ROW < SEG_POLICY_WIDE_BYTES_PER_ROW);

/// The closed form (spec §12), and what the corpus says its arguments are.
///
/// Spec §12 expected `k = f(sources, rows, width mix)`. The corpus says **`k` is a
/// function of the per-row source footprint alone**, and the two other candidates
/// were tested and dropped rather than assumed away:
///
///   * **rows do not enter.** The first pass measured one row count per coordinate
///     and produced a convincing "deeper grid wants a narrower block" rule — which
///     was an ARTIFACT: under one memory budget the row count is a deterministic
///     function of the footprint, so depth and weight moved together. Re-measuring
///     every coordinate at three depths, and the heavy circuits again at a six-times
///     larger budget, separates them: a LIGHT coordinate still wants `K = 4` at the
///     shallowest grid swept, and a HEAVY one still wants a wide block at the
///     deepest. Grid depth as a single feature scores no better than the constant
///     `K = 4`.
///   * **static work does not add.** `ListWorkStats`'s per-list work, the term
///     count and the source count were each fitted as the step feature; all three
///     score measurably worse than the footprint, and adding a work term on top of
///     the footprint moves nothing.
///
/// `bytes_per_row` is the round's own window geometry (`probe_geometry`,
/// bench-gated): `sum over windows of columns * (2 << delta) * width`, plus two
/// E4 per published column. That is exactly "sources and width mix" as one
/// number, and a launcher can compute it at setup from the binding it is about
/// to lower.
///
/// `ceiling` is the largest `K` the compiled family can host — a register fact,
/// not a choice ([`seg_k_ceiling`] probes it; the probe reports 32 for BOTH
/// families at the shipped 64-register band).
///
/// The result is always a member of [`SEG_CORPUS_K`] at or below `ceiling`. The
/// wide arm is `K = 16`, which INVERTS what an earlier band fitted: at 64
/// registers two 512-thread blocks co-reside (2 × 16 = 32 warps) while `K = 24`
/// and `K = 32` are both single-block shapes, and the 2026-08-01 chop-point
/// corpus scores the wide population summed at `K16 +0.0% / K24 +6.2% /
/// K32 +3.1%` (9 of 10 wide cells win at 16). `K = 24` is pruned from the axis
/// outright — see [`SEG_CORPUS_K`]. `K` is deliberately not interpolated either:
/// it is a block geometry, and a launcher choosing `K = 11` would be choosing a
/// shape nothing was measured at.
pub(crate) fn seg_policy_k(bytes_per_row: usize, ceiling: usize) -> usize {
    if let Some(forced) = seg_forced_k() {
        // Still filtered through the ceiling: a `K` the compiled family cannot
        // host is not launchable, so honouring the override literally would turn
        // a diagnostic into a launch failure.
        return forced.min(ceiling);
    }
    seg_policy_k_with(
        bytes_per_row,
        ceiling,
        SEG_POLICY_NARROW_BYTES_PER_ROW,
        SEG_POLICY_WIDE_BYTES_PER_ROW,
    )
}

/// `AB_BWD_VM_SEG_K`: force every VM-owned round to one `K`, bypassing
/// [`seg_policy_k`]'s thresholds.
///
/// The instrument the threshold fit needs against PRODUCTION bindings. The
/// committed thresholds were fitted over the bench's synthetic corpus cells, and
/// a bound production round is not one of those cells — so "is this round's `K`
/// the best `K` for it" was, until this override, unanswerable outside the
/// corpus. Sweeping it against the per-layer A/B answers it directly.
///
/// `K` is a pure performance axis (the partial pair is the bit-identical sum of
/// the rows it replaces), so a forced `K` cannot change a proof — which is what
/// makes a sweep safe to run against the parity gates.
fn seg_forced_k() -> Option<usize> {
    static FORCED: OnceLock<Option<usize>> = OnceLock::new();
    *FORCED.get_or_init(|| {
        let raw = std::env::var("AB_BWD_VM_SEG_K").ok()?;
        let raw = raw.trim();
        if raw.is_empty() {
            return None;
        }
        let k: usize = raw
            .parse()
            .unwrap_or_else(|_| panic!("AB_BWD_VM_SEG_K={raw:?} is not a number"));
        assert!(
            SEG_CORPUS_K.contains(&k),
            "AB_BWD_VM_SEG_K={k} is off the measured axis {SEG_CORPUS_K:?}; a block geometry \
             nothing was measured at is not a data point",
        );
        Some(k)
    })
}

/// [`seg_policy_k`] with the two thresholds supplied rather than committed.
///
/// The fit and the leave-one-circuit-out validation both need to evaluate the
/// policy at thresholds that are NOT the committed ones; sharing this function is
/// what stops the validation from silently scoring a differently-shaped rule.
pub(crate) fn seg_policy_k_with(
    bytes_per_row: usize,
    ceiling: usize,
    narrow: usize,
    wide: usize,
) -> usize {
    let want = if bytes_per_row < narrow {
        4
    } else if bytes_per_row < wide {
        8
    } else {
        16
    };
    // `want` is at least the axis minimum and so is `ceiling`, so the filter is
    // never empty; the `unwrap_or` is a total function, not a guess.
    let cap = want.min(ceiling);
    SEG_CORPUS_K
        .into_iter()
        .filter(|k| *k <= cap)
        .max()
        .unwrap_or(SEG_CORPUS_K[0])
}

/// The largest launchable `K` of one regime's PRODUCTION family (`Inline`
/// program, `Constant` bank, `Plane` epilogue), probed from the driver.
///
/// ENUMERATED over the whole axis rather than bisected, for the same reason the
/// bench's `seg_launchable_k_axis` is: the register limit interacts with the
/// epilogue's shared-memory footprint, so monotonicity in `k` is exactly what a
/// probe should measure rather than assume. `BWD_SEG_MAX_K` driver queries cost
/// microseconds, once per launch site.
pub(crate) fn seg_k_ceiling(regime: BwdRegime) -> CudaResult<usize> {
    let mut ceiling = 0usize;
    for k in 1..=BWD_SEG_MAX_K as u32 {
        let blocks = bwd_seg_blocks_per_sm(
            regime,
            ProgramMode::Inline,
            CoeffMode::Constant,
            BwdSegEpilogue::Plane,
            k,
        )?;
        if blocks > 0 {
            ceiling = k as usize;
        }
    }
    assert!(ceiling > 0, "a production family hosts at least one K");
    Ok(ceiling)
}

// ── Window shapes (CPU) ──────────────────────────────────────────────────────

/// One binding window's production identity, before any pointer exists: where
/// it reads (or that it is procedural), what field backs it, and how round 0
/// classifies it. Everything here is derivable on the CPU from the compiled
/// coordinate alone, which is what makes the shape phase testable without a
/// device.
#[derive(Debug)]
pub(crate) struct R0WindowShape {
    /// The window's base column as a production address, or `None` for a
    /// procedural window (the resolver synthesizes from the row index).
    pub(crate) address: Option<GKRAddress>,
    /// The backing matrix's own field width.
    pub(crate) is_e4: bool,
    pub(crate) class: SourceClass,
    /// Always `false` at R0; carried so the publish plan is derived from the
    /// same declaration [`super::seg_lower::lower_bwd_seg`] checks.
    pub(crate) materialize: bool,
    /// The backing's own referenced columns, ascending; `first_column` is
    /// always the first entry (the lean binder never bases a window on a
    /// hole).
    pub(crate) referenced_columns: Vec<usize>,
    pub(crate) first_column: usize,
}

/// Why a coordinate cannot be bound against production storage. Every variant
/// is a wiring defect, not a runtime condition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum BwdVmBindError {
    /// The coordinate is not an R0 program.
    NotR0 { layer: usize, regime: BwdRegime },
    /// The artifact's own window geometry is malformed.
    WindowShape(BwdSegLowerError),
    /// Round 0 classified a window as publishing — the depth wiring is wrong.
    UnexpectedPublish { window: u8 },
    /// A window's base column has no poly in production storage. Binding it
    /// anyway would hand the kernel a null read pointer.
    UnresolvedWindow { window: u8, address: GKRAddress },
    /// Storage resolved a column of the window in the wrong field.
    WindowFieldMismatch { window: u8, expect_e4: bool },
    /// A resolved column does not sit a whole number of strides into its own
    /// backing, so it has no rank and cannot be addressed as a column of it.
    UnresolvableRank { window: u8 },
    /// Interning production backings needs more address slots than the
    /// descriptor table holds.
    ///
    /// Columns are renumbered to the dense offsets their pointers imply
    /// ([`dense_step`]), so `windows > parents` here means storage genuinely
    /// backs one artifact window through several differently-strided pieces —
    /// not that the artifact numbers its columns sparsely.
    TooManyWindows { windows: usize, parents: usize },
    /// R0 must plan no publish scratch; a non-empty plan means the depth
    /// wiring is wrong.
    PublishPlanNotEmpty { bytes: usize },
    /// The coordinate is not an Ext program.
    NotExt { layer: usize, regime: BwdRegime },
    /// The Ext shape pass was asked about round 0, which the R0 program owns.
    NotAContinuationRound { round: u8 },
    /// A window column has no cascade region: the flat prepare has not run for
    /// this layer, or the address never folds here. Binding it anyway would
    /// publish through a null pointer.
    UnresolvedCascade {
        window: u8,
        address: GKRAddress,
        /// The window's RAW backing field, which picks WHICH folding map was
        /// consulted, and the layer it was consulted at. Both are needed to read
        /// this failure at all: the same address can be absent from the base map
        /// while present in the ext one, and that difference is what separates
        /// "never folds" from "the entry is created lazily by a round this VM
        /// owns, so nothing created it".
        e4_origin: bool,
        looked_in: usize,
    },
}

/// The read place of one window column, or `None` for a procedural window.
pub(super) fn family_read_place(family: WindowFamily, column: usize) -> Option<ReadPlace> {
    match family {
        WindowFamily::BaseLayerMemory => Some(ReadPlace::BaseLayerMemory { column }),
        WindowFamily::BaseLayerWitness => Some(ReadPlace::BaseLayerWitness { column }),
        WindowFamily::Setup => Some(ReadPlace::Setup { column }),
        WindowFamily::Scratch => Some(ReadPlace::Scratch { slot: column }),
        WindowFamily::LayerOutput { layer, .. } => {
            Some(ReadPlace::LayerOutput { layer, offset: column })
        }
        WindowFamily::CacheOutput { layer, .. } => {
            Some(ReadPlace::CacheOutput { layer, offset: column })
        }
        WindowFamily::VirtualSetup { .. } => None,
    }
}

/// The CPU half of the binder: every window's address, field, class and publish
/// flag, from the compiled coordinate alone.
pub(crate) fn r0_window_shapes(
    coord: &LeanCoordinateArtifact,
) -> Result<Vec<R0WindowShape>, BwdVmBindError> {
    if coord.regime.regime() != BwdRegime::R0 {
        return Err(BwdVmBindError::NotR0 {
            layer: coord.layer,
            regime: coord.regime.regime(),
        });
    }
    // A compile invariant (`the_lean_r0_coordinate_compiles_from_the_production_
    // artifact` pins it), not an input condition: R0 reads unfolded polynomials.
    assert_eq!(coord.target_depth, 0, "an R0 coordinate is bound at depth 0");

    let mut shapes = Vec::with_capacity(coord.binding.windows.len());
    for (index, window) in coord.binding.windows.iter().enumerate() {
        let address = family_read_place(window.family, window.first_column)
            .map(|place| read_place_to_gkr_address(&place));
        let origin = if address.is_none() {
            SourceOrigin::Procedural
        } else if window.backing_field() == FieldKind::Ext {
            SourceOrigin::E4
        } else {
            SourceOrigin::Bf
        };
        // Round 0 IS depth 0, so every window's catch-up delta is 0; the D2
        // policy only matters at delta 2 and cannot change the answer here.
        let (class, publishes) = assign_class(origin, 0, D2Policy::Inline);
        if publishes {
            return Err(BwdVmBindError::UnexpectedPublish { window: index as u8 });
        }
        shapes.push(R0WindowShape {
            address,
            is_e4: window.backing_field() == FieldKind::Ext,
            class,
            materialize: publishes,
            referenced_columns: window.columns.iter().map(|c| c.column).collect(),
            first_column: window.first_column,
        });
    }
    Ok(shapes)
}

// ── The Ext shape phase (CPU) ────────────────────────────────────────────────

/// One window's shape at ONE continuation round.
///
/// Unlike [`R0WindowShape`], the class ladder here is round-dependent: the
/// window's ORIGIN is a family property, but what the round reads (raw matrix,
/// synthesis, or the previous round's cascade slot) and whether it publishes
/// follow the materialization ladder — E4-origin from round 1, BF-origin at
/// [`BWD_COEFF_PUBLISH_TARGET_DEPTH`] under `D2Policy::Inline` (round 2 under
/// `Materialize`), procedural at [`BWD_COEFF_PUBLISH_TARGET_DEPTH`]. From its
/// materialization round on, a window publishes cascade slot `round` EVERY
/// round, and reads chained from `round + 1` on.
#[derive(Debug)]
pub(crate) struct ExtWindowShape {
    /// The window's base column as a production address, or `None` for a
    /// procedural window.
    pub(crate) address: Option<GKRAddress>,
    /// The RAW backing matrix's field width (a cascade slot is always E4).
    pub(crate) is_e4_backing: bool,
    pub(crate) class: SourceClass,
    /// This round publishes cascade slot `round`.
    pub(crate) materialize: bool,
    /// This round reads the previous round's cascade slot instead of the raw
    /// matrix or synthesis.
    pub(crate) chained: bool,
    /// `round - 1` when chained, 0 otherwise.
    pub(crate) backing_depth: u8,
    /// The backing's own referenced columns, ascending.
    pub(crate) referenced_columns: Vec<usize>,
    pub(crate) first_column: usize,
}

/// The round `origin` first writes a cascade slot, under `d2`.
fn ext_materialization_round(origin: SourceOrigin, d2: D2Policy) -> u8 {
    match (origin, d2) {
        (SourceOrigin::E4, _) => 1,
        (SourceOrigin::Bf, D2Policy::Materialize) => 2,
        (SourceOrigin::Bf, D2Policy::Inline) => BWD_COEFF_PUBLISH_TARGET_DEPTH,
        (SourceOrigin::Procedural, _) => BWD_COEFF_PUBLISH_TARGET_DEPTH,
    }
}

/// The CPU half of the Ext binder: every window's address, field, class,
/// publish flag and chain state at round `round`, from the compiled coordinate
/// alone.
pub(crate) fn ext_round_window_shapes(
    coord: &LeanCoordinateArtifact,
    round: u8,
    d2: D2Policy,
) -> Result<Vec<ExtWindowShape>, BwdVmBindError> {
    if coord.regime.regime() != BwdRegime::Ext {
        return Err(BwdVmBindError::NotExt {
            layer: coord.layer,
            regime: coord.regime.regime(),
        });
    }
    if round == 0 {
        return Err(BwdVmBindError::NotAContinuationRound { round });
    }

    let mut shapes = Vec::with_capacity(coord.binding.windows.len());
    for window in coord.binding.windows.iter() {
        let address = family_read_place(window.family, window.first_column)
            .map(|place| read_place_to_gkr_address(&place));
        let is_e4_backing = window.backing_field() == FieldKind::Ext;
        let raw_origin = if address.is_none() {
            SourceOrigin::Procedural
        } else if is_e4_backing {
            SourceOrigin::E4
        } else {
            SourceOrigin::Bf
        };
        let chained = round > ext_materialization_round(raw_origin, d2);
        let backing_depth = if chained { round - 1 } else { 0 };
        let delta = round - backing_depth;
        // A chained window reads E4 whatever its family produced — the origin
        // is the ROUND's, not the family's (`lower_window` derives the same
        // answer from the bound read's field).
        let origin = if chained { SourceOrigin::E4 } else { raw_origin };
        let (class, materialize) = assign_class(origin, delta, d2);
        shapes.push(ExtWindowShape {
            address,
            is_e4_backing,
            class,
            materialize,
            chained,
            backing_depth,
            referenced_columns: window.columns.iter().map(|c| c.column).collect(),
            first_column: window.first_column,
        });
    }
    Ok(shapes)
}

// ── The cascade resolver ─────────────────────────────────────────────────────

/// One address's cascade region: the per-poly intermediate folding buffer the
/// flat path folds into (`intermediate_storage_for_folder_*` in production
/// storage), reduced to the facts the Ext binder needs. The region is an
/// append-only cascade of per-round slots — slot r holds the round-r layer
/// (`N/2^r` E4 values, `N` the raw poly length) at a fixed offset, written by
/// round r's kernel. The VM's round-r publish IS slot r; its round-r chain
/// read IS slot r-1.
///
/// Two shapes exist:
///
///   * ext-origin: region = `N` elements, first slot 1 at offset 0
///     (`GpuExtensionFieldPolyIntermediateFoldingStorage`);
///   * base-origin, real and virtual alike: region = `N/2` elements, first
///     slot 2 (`GpuBaseFieldPolyIntermediateFoldingStorage`) — under
///     `D2Policy::Inline` the VM never writes slot 2; its first write is
///     slot 3, and the slot-2 range simply stays unused.
///
/// Both incumbent walks (`pointer_for_sumcheck_continuation` /
/// `pointers_for_sumcheck_accessor_step`, storage_types/views.rs) close to
/// `offset(r) = R - R/2^(r - first_slot)` over the region length `R`. The
/// closed form exists because those walks take `&mut` storage the binder does
/// not have; the CPU test pins it against transcriptions of the walks and the
/// GPU test against the real prepared plans, pointer for pointer.
#[derive(Clone, Copy, Debug)]
pub(crate) struct CascadeRegion {
    /// Device byte address of the region's first element.
    pub(crate) base: *mut u8,
    /// Region length in E4 elements: `N` for ext-origin, `N/2` for base.
    pub(crate) region_elems: usize,
    /// The first round that owns a slot here: 1 for ext-origin, 2 for base.
    pub(crate) first_slot: u8,
    /// Base of the CONSOLIDATED allocation this region is a slice of. Regions of
    /// one backing are equal-sized and packed, so `(base - backing) /
    /// region_bytes` is the poly's rank in it — which is what lets every poly of
    /// a backing share one address slot.
    pub(crate) backing: *mut u8,
}

impl CascadeRegion {
    /// Element offset of cascade slot `round` within the region.
    pub(crate) fn slot_elem_offset(&self, round: u8) -> usize {
        assert!(
            round >= self.first_slot,
            "round {round} has no cascade slot in a region whose first slot is {}",
            self.first_slot
        );
        self.region_elems - (self.region_elems >> (round - self.first_slot))
    }

    /// The slot's length in elements: the round-`round` layer, `2 * rows`.
    pub(crate) fn slot_elems(&self, round: u8) -> usize {
        assert!(
            round >= self.first_slot,
            "round {round} has no cascade slot in a region whose first slot is {}",
            self.first_slot
        );
        self.region_elems >> (round - self.first_slot + 1)
    }

    /// Device byte address of cascade slot `round`.
    pub(crate) fn slot_ptr(&self, round: u8) -> *mut u8 {
        let offset = self.slot_elem_offset(round);
        // SAFETY: pointer arithmetic only — `offset < region_elems` by
        // construction and the region is one poly's slice of a live
        // `DeviceAllocation` (the resolver read it from production storage).
        unsafe { self.base.add(offset * size_of::<E4>()) }
    }

    /// Cascade slot `round` as a resolvable COLUMN of its consolidated backing.
    ///
    /// The matrix base carries the round's own offset, so a slot interned from
    /// this addresses `region_base + rank * region_bytes + slot_offset(round)` —
    /// the flat path's pointer for that poly at that round, by construction. The
    /// stride is the region stride, which is what makes consecutive polys of one
    /// backing consecutive columns of one slot.
    pub(crate) fn slot_column(&self, round: u8) -> ResolvedColumn {
        let region_bytes = self.region_elems * size_of::<E4>();
        let offset = self.slot_elem_offset(round) * size_of::<E4>();
        ResolvedColumn {
            is_e4: true,
            ptr: self.base.cast_const().wrapping_add(offset),
            matrix_base: self.backing.wrapping_add(offset),
            stride_bytes: region_bytes as u32,
        }
    }
}

/// The production address of a procedural window's virtual poly: the inverse
/// of the lowering chain (`VirtualSetupPoly -> VirtualSetupKind -> kind tag`,
/// dag_ir lower's `map_virtual_setup` composed with [`KIND_ORDER`]). The
/// procedural windows synthesize their VALUES from the row index, but their
/// cascade slots — where rounds `>= BWD_COEFF_PUBLISH_TARGET_DEPTH` publish —
/// are the flat path's virtual folding buffers, keyed by this address.
/// Explicit match so an upstream variant addition fails to compile here.
pub(crate) fn virtual_setup_address(kind: u8) -> GKRAddress {
    GKRAddress::VirtualSetup(match KIND_ORDER[kind as usize] {
        VirtualSetupKind::RangeCheck16Bits => VirtualSetupPoly::RangeCheck16Bits,
        VirtualSetupKind::RangeCheckTimestamp => VirtualSetupPoly::RangeCheckTimestamp,
        VirtualSetupKind::InitsAndTeardownsLow => VirtualSetupPoly::InitsAndTeardownsLow,
        VirtualSetupKind::InitsAndTeardownsHigh => VirtualSetupPoly::InitsAndTeardownsHigh,
    })
}

/// Resolve `addr`'s cascade region from the folding-storage entry the flat
/// prepare created (`intermediate_storage_for_folder_*`). Production orders
/// prepare before the VM build (state.rs), so the entries exist — and reading
/// them, rather than re-deriving the consolidated-Arc offsets, makes the
/// binder agree with the flat path's pointers BY CONSTRUCTION, on the
/// consolidated and per-poly allocation paths alike.
///
/// `e4_origin` is the window's RAW backing field and picks the map, mirroring
/// the incumbents' cache-layer rule exactly: ext-origin entries live at the
/// poly's canonical layer (`plan_ext_source_for_rounds_1_and_beyond` keys
/// `ext_poly_layer`), base-origin entries — real, trace-holder and virtual
/// alike — at the REQUESTING layer (`plan_base_source_*`'s
/// `cache_layer = request_layer`).
///
/// `None` is a bind-stopping answer for a window that publishes or chains: it
/// means prepare has not run for this layer (call-order defect) or the
/// address never folds here.
pub(crate) fn resolve_cascade_region<E: Copy>(
    storage: &GpuGKRStorage<BF, E>,
    request_layer: usize,
    addr: GKRAddress,
    e4_origin: bool,
) -> Option<CascadeRegion> {
    assert_eq!(size_of::<E>(), size_of::<E4>(), "the cascade is E4-wide");
    if e4_origin {
        let layer = GpuGKRStorage::<BF, E>::ext_poly_layer(addr)?;
        let (_, buffer) = storage
            .layers
            .get(layer)?
            .intermediate_storage_for_folder_extension_field_inputs
            .get(&addr)?;
        Some(CascadeRegion {
            // SAFETY: pointer arithmetic within `buffer.backing` — the
            // constructor asserted `offset_in_backing` in bounds.
            base: unsafe { buffer.backing.as_ptr().add(buffer.offset_in_backing) }
                .cast_mut()
                .cast::<u8>(),
            region_elems: 2 * buffer.size_after_one_fold,
            first_slot: 1,
            backing: buffer.backing.as_ptr().cast_mut().cast::<u8>(),
        })
    } else {
        let (_, buffer) = storage
            .layers
            .get(request_layer)?
            .intermediate_storage_for_folder_base_field_inputs
            .get(&addr)?;
        Some(CascadeRegion {
            // SAFETY: as above.
            base: unsafe { buffer.backing.as_ptr().add(buffer.offset_in_backing) }
                .cast_mut()
                .cast::<u8>(),
            region_elems: 2 * buffer.size_after_two_folds,
            first_slot: 2,
            backing: buffer.backing.as_ptr().cast_mut().cast::<u8>(),
        })
    }
}

// ── Pointer resolution (production) ──────────────────────────────────────────

/// One round-0 binding, resolved against production storage.
///
/// The coordinate is NOT rebound: the lowering reads the artifact's program, its
/// order and its source COUNT, and nothing else about its windows. Addresses are
/// these two vectors, so the artifact's own window geometry — a fact about the
/// DAG's address space — never has to be reconciled with storage at all.
pub(crate) struct BoundR0Sources {
    /// The round's address table, positionally the descriptor's slot array.
    pub(crate) slots: Vec<ResolvedAddrSlot>,
    /// One entry per wire source, in source-slot order.
    pub(crate) sources: Vec<ResolvedSourceAddr>,
    /// The (empty — asserted) R0 publish plan, kept so the lowering's
    /// [`ResolvedPublishScratch`] is the SAME plan the bind checked rather
    /// than a re-derivation that could disagree.
    pub(crate) publish_plan: PublishScratchPlan,
}

/// Interns production backings into address slots.
///
/// A slot is keyed by `(chunk base, stride)`, where the chunk is the column's
/// rank within its backing divided by [`SOURCE_WINDOW_COLUMNS`]. So every source
/// reading a matrix shares one slot per 128 columns of it, whatever the
/// artifact's numbering, whatever the gaps, and whether the backing is
/// absolute-indexed (an arena, holes physically present) or rank-packed (a
/// consolidated matrix, only what it holds). The rank comes from the POINTER, so
/// the two layouts need no distinction: it is whatever `(ptr - base) / stride`
/// says.
///
/// A backing wider than 128 columns simply takes more slots at offset bases —
/// "just compute the offsetted pointer", which is arithmetic, not a split of
/// anything. That is why the slot count tracks how many matrices a layer touches
/// rather than how its columns are grouped.
#[derive(Default)]
struct SlotTable {
    slots: Vec<ResolvedAddrSlot>,
    /// `(chunk base, stride bytes)` -> slot index.
    index: BTreeMap<(usize, u32), usize>,
}

impl SlotTable {
    /// Intern the backing `column` lives in and answer `(slot, column in slot)`.
    ///
    /// `read_elements` is the readable span per addressed column; a slot keeps
    /// the SMALLEST any of its columns reports, so the lowering's span guard sees
    /// the tightest bound rather than an optimistic one.
    fn intern(
        &mut self,
        window: u8,
        column: ResolvedColumn,
        read_elements: u32,
    ) -> Result<(usize, usize), BwdVmBindError> {
        let stride = column.stride_bytes as usize;
        let ptr = column.ptr as usize;
        let base = column.matrix_base as usize;
        // A backing whose stride cannot index it, or a column that does not sit a
        // whole number of strides into its own matrix, is a resolver defect.
        if stride == 0 || ptr < base || (ptr - base) % stride != 0 {
            return Err(BwdVmBindError::UnresolvableRank { window });
        }
        let rank = (ptr - base) / stride;
        let chunk = rank / SOURCE_WINDOW_COLUMNS;
        let within = rank % SOURCE_WINDOW_COLUMNS;
        let chunk_base = base + chunk * SOURCE_WINDOW_COLUMNS * stride;
        let key = (chunk_base, column.stride_bytes);
        let slot = match self.index.get(&key) {
            Some(&slot) => {
                let entry = &mut self.slots[slot];
                entry.columns = entry.columns.max(within + 1);
                entry.read_elements = entry.read_elements.min(read_elements);
                slot
            }
            None => {
                self.slots.push(ResolvedAddrSlot {
                    base: Some(ResolvedColumn {
                        is_e4: column.is_e4,
                        ptr: chunk_base as *const u8,
                        matrix_base: column.matrix_base,
                        stride_bytes: column.stride_bytes,
                    }),
                    procedural_kind: None,
                    read_elements,
                    columns: within + 1,
                });
                let slot = self.slots.len() - 1;
                self.index.insert(key, slot);
                slot
            }
        };
        Ok((slot, within))
    }

    /// Intern a procedural backing. Keyed by kind, and it addresses no columns,
    /// so every procedural source of one kind shares a single slot.
    fn intern_procedural(&mut self, kind: u8) -> (usize, usize) {
        let key = (usize::MAX, u32::from(kind));
        if let Some(&slot) = self.index.get(&key) {
            return (slot, 0);
        }
        self.slots.push(ResolvedAddrSlot {
            base: None,
            procedural_kind: Some(kind),
            read_elements: 0,
            columns: 1,
        });
        let slot = self.slots.len() - 1;
        self.index.insert(key, slot);
        (slot, 0)
    }
}

/// Resolve one R0 coordinate's sources against production storage.
///
/// Every referenced column resolves independently and is interned into the slot
/// its own pointer implies ([`SlotTable`]). There is no re-partitioning of the
/// artifact's windows and no renumbering of its columns: the artifact's geometry
/// is simply not consulted, because a source's address is a fact about storage.
///
/// `rows` is the launch's logical row count; it enters only the (asserted empty)
/// publish plan.
pub(crate) fn bind_r0_sources<E: Copy>(
    storage: &GpuGKRStorage<BF, E>,
    coord: &LeanCoordinateArtifact,
    rows: usize,
) -> Result<BoundR0Sources, BwdVmBindError> {
    let shapes = r0_window_shapes(coord)?;
    let mut table = SlotTable::default();
    let mut sources: Vec<Option<ResolvedSourceAddr>> =
        vec![None; coord.binding.source_slots.len()];

    for (index, (shape, artifact_window)) in
        shapes.iter().zip(&coord.binding.windows).enumerate()
    {
        let window = index as u8;
        for entry in &artifact_window.columns {
            let (slot, column) = match family_read_place(artifact_window.family, entry.column) {
                None => match artifact_window.family {
                    WindowFamily::VirtualSetup { kind } => table.intern_procedural(kind),
                    _ => unreachable!("an addressless window is procedural"),
                },
                Some(place) => {
                    let address = read_place_to_gkr_address(&place);
                    let resolved = resolve_storage_column(storage, address)
                        .ok_or(BwdVmBindError::UnresolvedWindow { window, address })?;
                    if resolved.is_e4 != shape.is_e4 {
                        return Err(BwdVmBindError::WindowFieldMismatch {
                            window,
                            expect_e4: shape.is_e4,
                        });
                    }
                    let width = if shape.is_e4 {
                        size_of::<E4>()
                    } else {
                        size_of::<BF>()
                    } as u32;
                    table.intern(window, resolved, resolved.stride_bytes / width)?
                }
            };
            sources[entry.source as usize] = Some(ResolvedSourceAddr {
                read_slot: slot,
                read_column: column,
                // R0 reads every backing at depth 0 and publishes nothing.
                publish: None,
                backing_depth: 0,
            });
        }
    }

    let sources = sources
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .expect("every source slot belongs to exactly one artifact window column");
    let slots = table.slots;
    if slots.len() > BWD_SEG_ADDR_SLOTS {
        return Err(BwdVmBindError::TooManyWindows {
            windows: slots.len(),
            parents: coord.binding.windows.len(),
        });
    }

    // R0 publishes nothing; a plan that wants bytes means the depth wiring is
    // wrong and must stop the proof before anything is allocated for it.
    let publishes = vec![false; slots.len()];
    let columns: Vec<usize> = slots.iter().map(|slot| slot.columns).collect();
    let plan = plan_publish_scratch(&[&publishes], &[&columns], &[rows])
        .map_err(BwdVmBindError::WindowShape)?;
    if plan.total_bytes != 0 {
        return Err(BwdVmBindError::PublishPlanNotEmpty {
            bytes: plan.total_bytes,
        });
    }

    Ok(BoundR0Sources {
        slots,
        sources,
        publish_plan: plan,
    })
}

// ── The Ext binding ──────────────────────────────────────────────────────────

/// One Ext binding: per-round address tables and source lanes for the whole
/// continuation sequence.
pub(crate) struct BoundExtSources {
    /// `rounds[r - 1]` is round `r`'s resolution, `r` in `1..=folding_steps-1`.
    pub(crate) rounds: Vec<BoundExtRound>,
    /// The whole sequence's publish plan, absolute-round indexed. Structurally
    /// EMPTY — every publish is explicitly backed by a cascade slot — and
    /// asserted so; a nonzero plan means a destination lost its backing.
    pub(crate) publish_plan: PublishScratchPlan,
}

/// One round's addresses. Unlike the old frozen window partition, each round
/// interns its own table: a destination slot's base includes that round's offset
/// inside its cascade region, so the table is a per-round fact and pretending
/// otherwise is what forced reads and destinations to share an index.
pub(crate) struct BoundExtRound {
    pub(crate) round: u8,
    pub(crate) rows: usize,
    pub(crate) slots: Vec<ResolvedAddrSlot>,
    pub(crate) sources: Vec<ResolvedSourceAddr>,
}

/// Resolve one Ext coordinate's sources against production storage, per round.
///
/// Read and destination are interned INDEPENDENTLY, which is the whole point: a
/// raw matrix is absolute-indexed and its fold backing rank-packed, so the same
/// column has two different ranks and one index cannot serve both. Two lanes per
/// source, two slots, no reconciliation, nothing splits.
pub(crate) fn bind_ext_round_sources<E: Copy>(
    storage: &GpuGKRStorage<BF, E>,
    coord: &LeanCoordinateArtifact,
    request_layer: usize,
    folding_steps: usize,
    d2: D2Policy,
) -> Result<BoundExtSources, BwdVmBindError> {
    // Regime/round validity and the ladder both live in the shape pass; round 1
    // exists for every continuation sequence, so it validates the coordinate.
    ext_round_window_shapes(coord, 1, d2)?;
    assert!(folding_steps >= 2, "a continuation sequence needs rounds");

    let mut rounds = Vec::with_capacity(folding_steps - 1);
    for round in 1..folding_steps {
        let rows = 1usize << (folding_steps - round - 1);
        let round = round as u8;
        let shapes = ext_round_window_shapes(coord, round, d2)?;
        let mut table = SlotTable::default();
        let mut sources: Vec<Option<ResolvedSourceAddr>> =
            vec![None; coord.binding.source_slots.len()];

        for (parent, artifact_window) in coord.binding.windows.iter().enumerate() {
            let window = parent as u8;
            let shape = &shapes[parent];
            let e4_origin = artifact_window.backing_field() == FieldKind::Ext;
            for entry in &artifact_window.columns {
                let (raw, address) = match family_read_place(artifact_window.family, entry.column) {
                    Some(place) => {
                        let address = read_place_to_gkr_address(&place);
                        let resolved = resolve_storage_column(storage, address)
                            .ok_or(BwdVmBindError::UnresolvedWindow { window, address })?;
                        if resolved.is_e4 != e4_origin {
                            return Err(BwdVmBindError::WindowFieldMismatch {
                                window,
                                expect_e4: e4_origin,
                            });
                        }
                        (Some(resolved), address)
                    }
                    None => match artifact_window.family {
                        WindowFamily::VirtualSetup { kind } => (None, virtual_setup_address(kind)),
                        _ => unreachable!("an addressless window is procedural"),
                    },
                };
                let cascade = resolve_cascade_region(storage, request_layer, address, e4_origin)
                    .ok_or_else(|| BwdVmBindError::UnresolvedCascade {
                        window,
                        address,
                        e4_origin,
                        looked_in: if e4_origin {
                            GpuGKRStorage::<BF, E>::ext_poly_layer(address).unwrap_or(usize::MAX)
                        } else {
                            request_layer
                        },
                    })?;

                // The READ lane. A chained round reads the previous round's
                // publish — the same cascade region, one slot back — which is
                // exactly the invariant the parity model enforced with
                // `ChainReadNotPriorPublish`, here by construction.
                let (read_slot, read_column) = if shape.chained {
                    let slot = cascade.slot_column(round - 1);
                    table.intern(window, slot, cascade.slot_elems(round - 1) as u32)?
                } else {
                    match raw {
                        Some(resolved) => {
                            let width = if resolved.is_e4 {
                                size_of::<E4>()
                            } else {
                                size_of::<BF>()
                            } as u32;
                            table.intern(window, resolved, resolved.stride_bytes / width)?
                        }
                        None => match artifact_window.family {
                            WindowFamily::VirtualSetup { kind } => table.intern_procedural(kind),
                            _ => unreachable!("an addressless window is procedural"),
                        },
                    }
                };
                // The DESTINATION lane, interned in its own right.
                let publish = if shape.materialize {
                    let slot = cascade.slot_column(round);
                    Some(table.intern(window, slot, cascade.slot_elems(round) as u32)?)
                } else {
                    None
                };
                sources[entry.source as usize] = Some(ResolvedSourceAddr {
                    read_slot,
                    read_column,
                    publish,
                    backing_depth: shape.backing_depth,
                });
            }
        }

        let sources = sources
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .expect("every source slot belongs to exactly one artifact window column");
        let slots = table.slots;
        if slots.len() > BWD_SEG_ADDR_SLOTS {
            return Err(BwdVmBindError::TooManyWindows {
                windows: slots.len(),
                parents: coord.binding.windows.len(),
            });
        }
        if std::env::var_os("AB_BWD_VM_BIND_CENSUS").is_some() {
            let reads: std::collections::BTreeSet<usize> =
                sources.iter().map(|addr| addr.read_slot).collect();
            eprintln!(
                "[bwd-vm-census] L{} Ext round {round}: {} sources, \
                 {} artifact windows, {} address slots ({} read + {} destination), \
                 {} bytes/row",
                coord.layer,
                sources.len(),
                coord.binding.windows.len(),
                slots.len(),
                reads.len(),
                slots.len() - reads.len(),
                seg_ext_bytes_per_row(&slots, &sources, round),
            );
        }
        rounds.push(BoundExtRound {
            round,
            rows,
            slots,
            sources,
        });
    }

    // ── The (empty) plan for the whole sequence ──────────────────────────────
    // Round 0 belongs to the R0 program and plans nothing here; every
    // destination of rounds 1+ is an explicit cascade slot, so the plan must
    // reserve nothing.
    let no_publishes: Vec<bool> = Vec::new();
    let no_columns: Vec<usize> = Vec::new();
    let mut publishes_per_round: Vec<&[bool]> = vec![&no_publishes];
    let mut columns_per_round: Vec<&[usize]> = vec![&no_columns];
    let mut rows_per_round: Vec<usize> = vec![1 << (folding_steps - 1)];
    let per_round_columns: Vec<Vec<usize>> = rounds
        .iter()
        .map(|bound| bound.slots.iter().map(|slot| slot.columns).collect())
        .collect();
    let per_round_publishes: Vec<Vec<bool>> = rounds
        .iter()
        .map(|bound| vec![false; bound.slots.len()])
        .collect();
    for (bound, (columns, publishes)) in rounds
        .iter()
        .zip(per_round_columns.iter().zip(&per_round_publishes))
    {
        publishes_per_round.push(publishes);
        columns_per_round.push(columns);
        rows_per_round.push(bound.rows);
    }
    let plan = plan_publish_scratch(&publishes_per_round, &columns_per_round, &rows_per_round)
        .map_err(BwdVmBindError::WindowShape)?;
    if plan.total_bytes != 0 {
        return Err(BwdVmBindError::PublishPlanNotEmpty {
            bytes: plan.total_bytes,
        });
    }

    Ok(BoundExtSources {
        rounds,
        publish_plan: plan,
    })
}

// ── The R0 launch ────────────────────────────────────────────────────────────

/// The per-row device footprint of one bound R0 launch — the `K` policy's
/// input.
///
/// The bench probes this off its host model (`probe_geometry`, bench-gated);
/// this is the same formula stated over the BOUND geometry, at R0's fixed
/// shape: the two contribution halves, plus `2 * width` per addressed column
/// (delta 0 reads one endpoint pair per column per logical row), plus nothing
/// procedural (synthesized, no DRAM) and nothing published (empty at R0).
///
/// Counted over COLUMNS ADDRESSED BY SOURCES, not over slot extents. A slot's
/// `columns` is the highest column index it addresses plus one — an extent that
/// can exceed what is read (two sources 100 columns apart address a 101-column
/// extent) and, when two artifact windows share a backing, no longer decomposes
/// per window. The host model's `probe.columns[w]` is the count of columns the
/// window actually addresses, so that is the quantity to restate.
pub(crate) fn seg_r0_bytes_per_row(
    slots: &[ResolvedAddrSlot],
    sources: &[ResolvedSourceAddr],
) -> usize {
    let mut bytes = 2 * size_of::<E4>();
    for (slot, columns) in addressed_columns(slots, sources) {
        let element = match slot.base {
            None => 0,
            Some(base) if base.is_e4 => size_of::<E4>(),
            Some(_) => size_of::<BF>(),
        };
        // R0 publishes nothing, so no `materialize` term and no catch-up delta:
        // every backing is at the round's own depth.
        bytes += columns.len() * 2 * element;
    }
    bytes
}

/// The distinct columns each slot is addressed at, with the deepest catch-up
/// delta any source reads each of them through.
///
/// One `(slot, column)` pair is ONE column of the host model's window whatever
/// number of wire sources read it, which is what makes this a restatement of
/// `probe_geometry` rather than a count of wire slots. Where several sources
/// read one column at different BACKING depths the SHALLOWEST backing wins,
/// because `delta` is `round - backing_depth`: that source has the furthest to
/// catch up, pulls `2^delta` endpoint pairs, and the others read inside its span.
/// The map therefore stores backing depths, and the caller turns each into a
/// delta against the round it is pricing.
fn addressed_columns<'a>(
    slots: &'a [ResolvedAddrSlot],
    sources: &[ResolvedSourceAddr],
) -> Vec<(&'a ResolvedAddrSlot, BTreeMap<usize, u8>)> {
    let mut addressed: Vec<(&ResolvedAddrSlot, BTreeMap<usize, u8>)> =
        slots.iter().map(|slot| (slot, BTreeMap::new())).collect();
    for source in sources {
        let depth = addressed[source.read_slot]
            .1
            .entry(source.read_column)
            .or_insert(source.backing_depth);
        *depth = (*depth).min(source.backing_depth);
    }
    addressed
}

/// Everything one VM-owned R0 launch needs at schedule time, built once at
/// plan-build time (which is where the storage pointers are resolved, exactly
/// like the flat path's own descriptors).
///
/// [`BwdSegSetup::coefficients`] is deliberately NOT uploaded: its values are
/// zeros (the host cannot evaluate a recipe — production challenges are
/// GPU-derived), and the bank is filled ON DEVICE by
/// [`schedule_bwd_seg_coeff_bank_fill`] from the challenge slab instead.
/// `claim_point` and `immediates` are empty at R0 and stay wherever lowering
/// left them.
pub(crate) struct BwdVmRound0Launch {
    setup: BwdSegSetup,
    tables: SegCoeffEvalTables,
    /// The device challenge slab ([`BWD_SEG_CHALLENGE_SLOTS`] E4 values in
    /// slot order), assembled by D2D at schedule time.
    slab: DeviceAllocation<E4>,
}

/// Build one VM-owned R0 launch against production storage.
///
/// Panics on any binding or lowering rejection: every failure here is a wiring
/// defect (a source that does not resolve, a publish at depth 0, a program
/// past its caps), and a proof must stop on it rather than fall back
/// somewhere unmeasured.
pub(crate) fn build_bwd_vm_round0<E: Copy>(
    storage: &GpuGKRStorage<BF, E>,
    slice: &CompiledSlice,
    rows: usize,
    eq_low: *const E4,
    eq_sizes: GkrEqSizes,
    contributions: *mut E4,
    context: &ProverContext,
) -> CudaResult<BwdVmRound0Launch> {
    let bound = bind_r0_sources(storage, &slice.coord, rows)
        .unwrap_or_else(|error| panic!("backward VM R0 source binding: {error:?}"));
    assert!(
        slice.layer.immediates.is_empty(),
        "an R0 layer has no groups, so no immediate table"
    );
    let tables = build_seg_coeff_eval_tables(&slice.layer.coefficients)
        .unwrap_or_else(|error| panic!("backward VM R0 bank translation: {error:?}"));

    // Dead values with a live LENGTH: lowering sizes the bank and validates the
    // wire's coefficient ids off this slice; the device fill above supplies the
    // real values.
    let coefficients = vec![E4::ZERO; slice.layer.coefficients.len()];
    let scratch = ResolvedPublishScratch {
        parity_base: [null_mut(), null_mut()],
        plan: bound.publish_plan.clone(),
    };
    let bytes_per_row = seg_r0_bytes_per_row(&bound.slots, &bound.sources);
    let k = seg_policy_k(bytes_per_row, seg_k_ceiling(BwdRegime::R0)?);
    let binding = BwdSegRoundBinding {
        round: 0,
        rows,
        slots: &bound.slots,
        sources: &bound.sources,
        claim_point: &[],
        coefficients: &coefficients,
        c_init: None,
        immediates: &[],
        eq_low,
        eq_sizes,
        contributions,
        acc_size: rows as u32,
        // Round 0 is never the last round (`last_step >= 3`), so it always runs
        // in the loop and its tail is the fused one.
        output: BWD_SEG_OUTPUT_PARTIALS,
    };
    let setup = lower_bwd_seg(
        &slice.coord,
        &binding,
        &scratch,
        k,
        D2Policy::Inline,
        ProgramMode::Inline,
        CoeffMode::Constant,
    )
    .unwrap_or_else(|error| panic!("backward VM R0 lowering (K = {k}): {error:?}"));

    let slab = context.alloc(BWD_SEG_CHALLENGE_SLOTS, AllocationPlacement::BestFit)?;
    Ok(BwdVmRound0Launch {
        setup,
        tables,
        slab,
    })
}

/// Schedule one VM-owned R0 round on `exec_stream`: assemble the challenge
/// slab (all D2D — every source pointer is already device-resident), fill the
/// coefficient bank on device, launch the segmented kernel.
///
/// The four pointers are the SAME ones the incumbent's `eval_recipes` launch
/// reads its challenges through (`schedule_flat_eval_recipes`): the
/// external-challenges buffer is the slab's 7-slot prefix verbatim (asserted
/// at the slab's definition), and the constraint-aggregation slot is left
/// unwritten — no corpus recipe references it (census-pinned).
pub(crate) fn schedule_bwd_vm_round0(
    launch: &mut BwdVmRound0Launch,
    external_challenges: *const E4,
    lookup_multiplicative: *const E4,
    lookup_additive: *const E4,
    claim_batching: *const E4,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    // The descriptor was lowered at plan build for step 0's row count; a loop
    // handing it a different `acc_size` would compute garbage silently.
    let (lowered_rows, contributions) = match &launch.setup.desc {
        super::seg_lower::BwdSegLaunchDesc::Inline(desc) => {
            (desc.logical_rows, desc.contributions)
        }
        super::seg_lower::BwdSegLaunchDesc::ProgPtr(desc) => {
            (desc.logical_rows, desc.contributions)
        }
    };
    assert_eq!(
        lowered_rows, acc_size,
        "the R0 descriptor was lowered for {lowered_rows} rows but round 0 runs at {acc_size}"
    );
    let stream = context.get_exec_stream();

    // The parity gate's anti-vacuity aid: these tests run `#[serial]` in one
    // process, so the pool has already held — and freed — blocks containing a
    // correct accumulator from earlier proofs. A VM that launches but writes
    // nothing (or half) could reproduce the right proof from recycled values;
    // poisoning both halves first makes that impossible. Opt-in, because it is
    // a full-length device write charged to the VM arm alone — the exact
    // confound that inverted the first forward A/B.
    #[cfg(test)]
    if poison_accumulator_enabled() {
        const POISON: u32 = 0x5EED_DEAD & 0x7FFF_FFFF;
        // See the Ext twin: the length follows the output shape, and round 0
        // always publishes partials.
        let elements = poisoned_output_elements(BWD_SEG_OUTPUT_PARTIALS, acc_size);
        // SAFETY: `contributions` is `round_scratch.partials`' live device
        // pointer, allocated for the worst-case partial count.
        let dst = unsafe { DeviceSlice::from_raw_parts_mut(contributions, elements) };
        crate::ops::simple::set_by_val(
            E4::from_array_of_base([BF::new(POISON); 4]),
            dst,
            stream,
        )?;
    }
    #[cfg(not(test))]
    let _ = contributions;
    schedule_seg_challenge_slab(
        &mut launch.slab,
        external_challenges,
        lookup_multiplicative,
        lookup_additive,
        claim_batching,
        context,
    )?;
    schedule_bwd_seg_coeff_bank_fill(
        &launch.tables,
        launch.slab.as_ptr(),
        bwd_seg_coeff_bank_device_ptr(),
        stream,
    )?;
    #[cfg(test)]
    BWD_VM_R0_LAUNCHES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    launch_bwd_seg(
        &launch.setup,
        BwdRegime::R0,
        CoeffMode::Constant,
        BwdSegEpilogue::Plane,
        context,
    )
}

/// Assemble the device challenge slab, all D2D: the external-challenges buffer
/// is the slab's 7-slot prefix verbatim (asserted at the slab's definition),
/// plus the three single-value slots. Every source pointer is a live device
/// buffer owned by the orchestrator for the whole layer — the same lifetime
/// argument `schedule_flat_eval_recipes` makes for the same pointers.
fn schedule_seg_challenge_slab(
    slab: &mut DeviceAllocation<E4>,
    external_challenges: *const E4,
    lookup_multiplicative: *const E4,
    lookup_additive: *const E4,
    claim_batching: *const E4,
    context: &ProverContext,
) -> CudaResult<()> {
    let stream = context.get_exec_stream();
    let prefix = BWD_SEG_CHALLENGE_LOOKUP_MULTIPLICATIVE as usize;
    debug_assert_eq!(BWD_SEG_CHALLENGE_PERM_LINEARIZATION_BASE, 0);
    // SAFETY: see the doc comment — device sources of at least the copied
    // length; the slab is the launch's own allocation.
    unsafe {
        let external = DeviceSlice::from_raw_parts(external_challenges, prefix);
        memory_copy_async(&mut slab[..prefix], external, stream)?;
        for (slot, source) in [
            (BWD_SEG_CHALLENGE_LOOKUP_MULTIPLICATIVE, lookup_multiplicative),
            (BWD_SEG_CHALLENGE_LOOKUP_ADDITIVE, lookup_additive),
            (BWD_SEG_CHALLENGE_CLAIM_BATCHING, claim_batching),
        ] {
            let slot = slot as usize;
            let source = DeviceSlice::from_raw_parts(source, 1);
            memory_copy_async(&mut slab[slot..slot + 1], source, stream)?;
        }
    }
    Ok(())
}

// ── The Ext launch sequence ──────────────────────────────────────────────────

/// Round `rounds`'s factored-eq sizes at plan build: the drain
/// [`fold_factored_eq_one_round`] applies once per completed round — `high[0]`
/// to zero, then `high[1]`, then `low` — replayed over the layer's initial
/// sizes. Pure host arithmetic: the device STATE it describes (the in-place
/// folded `eq_low` table and the `ab_gkr_eq_high` groups) is produced by the
/// eq folds the round loop schedules between rounds; only the SIZES enter the
/// descriptor, and they are deterministic at plan build.
///
/// [`fold_factored_eq_one_round`]: crate::prover::gkr::backward::kernels::fold_factored_eq_one_round
pub(crate) fn drained_eq_sizes(mut eq_sizes: GkrEqSizes, rounds: u8) -> GkrEqSizes {
    for _ in 0..rounds {
        if eq_sizes.high[0] > 0 {
            eq_sizes.high[0] -= 1;
        } else if eq_sizes.high[1] > 0 {
            eq_sizes.high[1] -= 1;
        } else {
            debug_assert!(eq_sizes.low >= 1, "the factored eq drained past empty");
            eq_sizes.low -= 1;
        }
    }
    eq_sizes
}

/// The per-row device footprint of one bound continuation round — the `K`
/// policy's input. The bench's `probe_geometry` restated over the BOUND
/// geometry: per window, `columns * (2 << delta) * element` (each output pair
/// consumes `2^delta` inputs per half at this round's catch-up delta;
/// procedural windows synthesize and read nothing), plus two E4 per published
/// column, plus the two contribution halves.
///
/// Counted over the columns SOURCES address (see [`addressed_columns`]) rather
/// than over slot extents, and the two shape-carrying terms are per source, not
/// per slot: `delta` is a source's own catch-up (two artifact windows may read
/// one backing at different depths) and publishing is a per-source fact (the
/// destination lane, `materialize` in the pre-table descriptor). A slot-wise
/// count can express neither, and dropping them under-prices exactly the deep
/// and the publishing rounds — which is what the fitted thresholds separate.
pub(crate) fn seg_ext_bytes_per_row(
    slots: &[ResolvedAddrSlot],
    sources: &[ResolvedSourceAddr],
    round: u8,
) -> usize {
    let mut bytes = 2 * size_of::<E4>();
    for (slot, columns) in addressed_columns(slots, sources) {
        let element = match slot.base {
            None => 0,
            Some(base) if base.is_e4 => size_of::<E4>(),
            Some(_) => size_of::<BF>(),
        };
        for backing_depth in columns.into_values() {
            let delta = round.saturating_sub(backing_depth);
            bytes += (2usize << delta) * element;
        }
    }
    // Two raw target-depth endpoints per published column. Counted over distinct
    // destination columns for the same reason the reads are: one column written
    // once is one column however many sources name it.
    let published: BTreeSet<(usize, usize)> = sources.iter().filter_map(|s| s.publish).collect();
    bytes += published.len() * 2 * size_of::<E4>();
    bytes
}

/// Everything the VM-owned continuation rounds of one layer need at schedule
/// time, built once at plan-build time. `setups[r - 1]` is round `r`'s.
///
/// No parity allocations exist: every publish lands in a cascade slot of fold
/// storage the layer already owns (kept alive by the storage struct, which
/// outlives scheduling). The slab and bank fill mirror the R0 launch's; ONE
/// fill before round 1 serves every round, because the bank's recipes are
/// challenge-functions of the LAYER, not of the round.
pub(crate) struct BwdVmExtLaunch {
    setups: Vec<BwdSegSetup>,
    tables: SegCoeffEvalTables,
    slab: DeviceAllocation<E4>,
    /// Bank fill scheduled — the round scheduler's call-order tripwire.
    filled: bool,
}

impl BwdVmExtLaunch {
    #[cfg(test)]
    pub(crate) fn setups(&self) -> &[BwdSegSetup] {
        &self.setups
    }
}

/// Build every VM-owned continuation round against production storage.
///
/// Panics on any binding or lowering rejection, exactly as
/// [`build_bwd_vm_round0`] does: every failure here is a wiring defect and a
/// proof must stop on it rather than fall back somewhere unmeasured.
pub(crate) fn build_bwd_vm_ext_rounds<E: Copy>(
    storage: &GpuGKRStorage<BF, E>,
    slice: &CompiledSlice,
    folding_steps: usize,
    eq_low: *const E4,
    partials: *mut E4,
    context: &ProverContext,
) -> CudaResult<BwdVmExtLaunch> {
    let bound = bind_ext_round_sources(
        storage,
        &slice.coord,
        slice.coord.layer,
        folding_steps,
        D2Policy::Inline,
    )
    .unwrap_or_else(|error| panic!("backward VM Ext source binding: {error:?}"));
    let tables = build_seg_coeff_eval_tables(&slice.layer.coefficients)
        .unwrap_or_else(|error| panic!("backward VM Ext bank translation: {error:?}"));

    // Dead values with a live LENGTH, as at R0: lowering sizes the bank and
    // validates ids; the device fill supplies the real values. The claim-point
    // payload is bounds-check-only — `ab_gkr_main_layer_claim_point` is
    // production-owned, written in place by the round-update kernels, and the
    // VM must NEVER upload over it.
    let coefficients = vec![E4::ZERO; slice.layer.coefficients.len()];
    let claim_point = vec![E4::ZERO; folding_steps];
    let scratch = ResolvedPublishScratch {
        parity_base: [null_mut(), null_mut()],
        plan: bound.publish_plan.clone(),
    };
    let ceiling = seg_k_ceiling(BwdRegime::Ext)?;
    let mut setups = Vec::with_capacity(bound.rounds.len());
    for round in &bound.rounds {
        let bytes_per_row = seg_ext_bytes_per_row(&round.slots, &round.sources, round.round);
        let k = seg_policy_k(bytes_per_row, ceiling);
        let binding = BwdSegRoundBinding {
            round: u32::from(round.round),
            rows: round.rows,
            slots: &round.slots,
            sources: &round.sources,
            claim_point: &claim_point,
            coefficients: &coefficients,
            c_init: slice.layer.c_init,
            immediates: &slice.layer.immediates,
            eq_low,
            eq_sizes: drained_eq_sizes(make_eq_sizes(folding_steps - 1), round.round),
            // EVERY round publishes partials, the final one included: its tail is
            // the same fused kernel with the eq fold suppressed
            // (`dispatch_warp_partial_tail_final_round`), so no round needs the
            // per-row shape and the accumulator is not read on a VM-owned layer
            // at all.
            contributions: partials,
            acc_size: round.rows as u32,
            output: BWD_SEG_OUTPUT_PARTIALS,
        };
        setups.push(
            lower_bwd_seg(
                &slice.coord,
                &binding,
                &scratch,
                k,
                D2Policy::Inline,
                ProgramMode::Inline,
                CoeffMode::Constant,
            )
            .unwrap_or_else(|error| {
                panic!(
                    "backward VM Ext lowering (round {}, K = {k}): {error:?}",
                    round.round
                )
            }),
        );
    }
    let slab = context.alloc(BWD_SEG_CHALLENGE_SLOTS, AllocationPlacement::BestFit)?;
    Ok(BwdVmExtLaunch {
        setups,
        tables,
        slab,
        filled: false,
    })
}

/// Schedule the ONE bank fill the continuation rounds share, before round 1:
/// assemble the challenge slab (all D2D) and evaluate the bank on device —
/// the same fill [`schedule_bwd_vm_round0`] performs, against the same
/// challenge pointers. When R0 is also VM-owned the two fills write identical
/// values to the same `__constant__` symbol, stream-ordered after round 0's
/// reads — redundant but harmless.
pub(crate) fn schedule_bwd_vm_ext_bank_fill(
    launch: &mut BwdVmExtLaunch,
    external_challenges: *const E4,
    lookup_multiplicative: *const E4,
    lookup_additive: *const E4,
    claim_batching: *const E4,
    context: &ProverContext,
) -> CudaResult<()> {
    schedule_seg_challenge_slab(
        &mut launch.slab,
        external_challenges,
        lookup_multiplicative,
        lookup_additive,
        claim_batching,
        context,
    )?;
    schedule_bwd_seg_coeff_bank_fill(
        &launch.tables,
        launch.slab.as_ptr(),
        bwd_seg_coeff_bank_device_ptr(),
        context.get_exec_stream(),
    )?;
    launch.filled = true;
    Ok(())
}

/// Schedule one VM-owned continuation round on `exec_stream`: the fold-weight
/// prelude (reads the claim-point symbol slot `round - 1`, which the previous
/// round's update kernel wrote — stream order IS the data dependency), then
/// the segmented kernel.
/// Elements a launch of `output` shape writes at `acc_size` rows — the poison's
/// length, and the only place the two shapes' extents are spelled.
#[cfg(test)]
fn poisoned_output_elements(output: u32, acc_size: u32) -> usize {
    match output {
        BWD_SEG_OUTPUT_PARTIALS => 2 * (acc_size as usize).div_ceil(WARP_SIZE as usize).max(1),
        _ => 2 * acc_size as usize,
    }
}

pub(crate) fn schedule_bwd_vm_ext_round(
    launch: &BwdVmExtLaunch,
    round: u32,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(
        launch.filled,
        "the Ext bank fill must be scheduled before any round launch"
    );
    let setup = &launch.setups[round as usize - 1];
    let (lowered_rows, contributions, output) = match &setup.desc {
        super::seg_lower::BwdSegLaunchDesc::Inline(desc) => {
            (desc.logical_rows, desc.contributions, desc.output)
        }
        super::seg_lower::BwdSegLaunchDesc::ProgPtr(desc) => {
            (desc.logical_rows, desc.contributions, desc.output)
        }
    };
    assert_eq!(
        lowered_rows, acc_size,
        "the Ext descriptor for round {round} was lowered for {lowered_rows} rows but runs at {acc_size}"
    );
    let stream = context.get_exec_stream();
    // The same anti-vacuity aid as round 0's, per VM round. Opt-in; see
    // `schedule_bwd_vm_round0`.
    #[cfg(test)]
    if poison_accumulator_enabled() {
        const POISON: u32 = 0x5EED_DEAD & 0x7FFF_FFFF;
        // The poison must cover EXACTLY what this launch overwrites, which
        // depends on the output shape: `2 * acc_size` per-row entries in the
        // accumulator, or one interleaved pair per 32-row tile in the partials
        // buffer. Writing the row length into the partials buffer would run off
        // the end of an allocation sized for the partial shape.
        let elements = poisoned_output_elements(output, acc_size);
        // SAFETY: `contributions` is the live device pointer of whichever buffer
        // this round's shape names, and both are allocated for the worst-case
        // `acc_size` in that shape.
        let dst = unsafe { DeviceSlice::from_raw_parts_mut(contributions, elements) };
        crate::ops::simple::set_by_val(E4::from_array_of_base([BF::new(POISON); 4]), dst, stream)?;
    }
    #[cfg(not(test))]
    let _ = contributions;
    launch_bwd_seg_build_fold_weights(round, context)?;
    #[cfg(test)]
    BWD_VM_EXT_LAUNCHES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    launch_bwd_seg(
        setup,
        BwdRegime::Ext,
        CoeffMode::Constant,
        BwdSegEpilogue::Plane,
        context,
    )
}

/// Env var opting the parity gate's accumulator poison in. Off by default so
/// timing runs never pay for a correctness aid — the forward A/B's first
/// inversion came from exactly this kind of aid left inside the measured arm.
pub(crate) const AB_GKR_BWD_VM_POISON_ACCUMULATOR_ENV: &str =
    "AB_GKR_BWD_VM_POISON_ACCUMULATOR";

/// Env var opting the parity gate's CASCADE poison in: sentinel-fill every
/// consolidated fold backing at layer prepare, so a proof that READS a slot
/// nothing wrote — a VM round that silently skipped a publish, a gather over
/// an unpublished address — fails loudly instead of reproducing recycled
/// values. Also proves the inverse: slots the Inline policy never writes
/// (base slot 2) are never read, or the poison would surface. Same off-by-
/// default doctrine as the accumulator poison.
pub(crate) const AB_GKR_BWD_VM_POISON_CASCADE_ENV: &str = "AB_GKR_BWD_VM_POISON_CASCADE";

/// Read fresh, like the coordinate switch.
#[cfg(test)]
pub(crate) fn cascade_poison_enabled() -> bool {
    std::env::var(AB_GKR_BWD_VM_POISON_CASCADE_ENV)
        .map(|v| {
            let v = v.trim().to_ascii_lowercase();
            v == "1" || v == "true"
        })
        .unwrap_or(false)
}

/// Schedule a sentinel fill over EVERY consolidated fold backing currently
/// registered in `storage` — every cascade slot a later read must first be
/// written over. Scheduled on `exec_stream` at the calling layer's prepare,
/// i.e. after every earlier layer's scheduled work and before this layer's
/// rounds.
#[cfg(test)]
pub(crate) fn schedule_cascade_poison<E: Copy>(
    storage: &GpuGKRStorage<BF, E>,
    context: &ProverContext,
) -> CudaResult<()> {
    const POISON: u32 = 0x5EED_DEAD & 0x7FFF_FFFF;
    assert_eq!(size_of::<E>(), size_of::<E4>(), "the cascade is E4-wide");
    let stream = context.get_exec_stream();
    let value = E4::from_array_of_base([BF::new(POISON); 4]);
    let mut fill = |arc: &std::sync::Arc<DeviceAllocation<E>>| -> CudaResult<()> {
        // SAFETY: a live consolidated backing, owned by storage (which
        // outlives scheduling); the fill covers exactly its length.
        let dst =
            unsafe { DeviceSlice::from_raw_parts_mut(arc.as_ptr().cast_mut().cast::<E4>(), arc.len()) };
        crate::ops::simple::set_by_val(value, dst, stream)
    };
    for layer in &storage.layers {
        if let Some(consolidated) = layer.intermediate_folding_consolidated.as_ref() {
            for arc in consolidated.per_class.values() {
                fill(arc)?;
            }
        }
        if let Some(consolidated) = layer.intermediate_base_folding_consolidated.as_ref() {
            for arc in consolidated
                .per_class
                .values()
                .chain(consolidated.virtual_per_class.values())
            {
                fill(arc)?;
            }
        }
    }
    Ok(())
}

/// Read fresh, like the coordinate switch.
#[cfg(test)]
pub(crate) fn poison_accumulator_enabled() -> bool {
    std::env::var(AB_GKR_BWD_VM_POISON_ACCUMULATOR_ENV)
        .map(|v| {
            let v = v.trim().to_ascii_lowercase();
            v == "1" || v == "true"
        })
        .unwrap_or(false)
}

/// VM-owned R0 launch count, for gates that must prove the VM actually ran.
/// Counts PRODUCTION schedules only — the bench harness launches the same
/// kernel through its own path and must not inflate a gate's count.
#[cfg(test)]
static BWD_VM_R0_LAUNCHES: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// VM-owned Ext (continuation) launch count, same doctrine.
#[cfg(test)]
static BWD_VM_EXT_LAUNCHES: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

/// Zero BOTH launch counters and return a handle that reads them back.
#[cfg(test)]
pub(crate) fn count_bwd_vm_r0_launches() -> BwdVmLaunchCounter {
    BWD_VM_R0_LAUNCHES.store(0, std::sync::atomic::Ordering::Relaxed);
    BWD_VM_EXT_LAUNCHES.store(0, std::sync::atomic::Ordering::Relaxed);
    BwdVmLaunchCounter
}

#[cfg(test)]
pub(crate) struct BwdVmLaunchCounter;

#[cfg(test)]
impl BwdVmLaunchCounter {
    pub(crate) fn launches(&self) -> usize {
        BWD_VM_R0_LAUNCHES.load(std::sync::atomic::Ordering::Relaxed)
    }

    pub(crate) fn ext_launches(&self) -> usize {
        BWD_VM_EXT_LAUNCHES.load(std::sync::atomic::Ordering::Relaxed)
    }
}
