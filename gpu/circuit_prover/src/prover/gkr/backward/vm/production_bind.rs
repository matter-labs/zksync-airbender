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
//!     `{ offset: 14 }` sit ONE stride apart, so absolute-offset arithmetic
//!     breaks at every offset gap. The base-layer arenas are the exception —
//!     absolute-indexed, holes physically present.
//!
//! So [`bind_r0_sources`] re-partitions: every referenced column resolves
//! independently, and each artifact window splits into maximal runs where the
//! production pointers advance by exactly `gap * stride` at the original
//! column numbers. add_sub L0 R0's 8 artifact windows become 13 bound windows.
//! The program and its source SLOTS are untouched — the design spec's contract
//! is the source table ("slot ids into a per-launch source table; no
//! windows"), and the window partition was always a compression of it, so
//! re-forming windows against real geometry is a binder-local move with no ABI
//! or artifact-format change. The rebound coordinate
//! ([`BoundR0Sources::coord`]) is what `lower_bwd_seg` must be handed; the
//! original's windows no longer describe the bound pointers.
//!
//! One consequence to watch: `lower_bwd_seg` caps windows at the corpus's
//! observed ARTIFACT-level maximum (`in_scope::MAX_SOURCE_WINDOWS_USED = 17`).
//! Splitting can exceed it for heavier circuits even though the format holds
//! 64; add_sub L0 R0's 13 fits, so widening coordinates later may need that
//! cap revisited against post-split counts.
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
use gkr_eval_isa::bwd::coeff::limits::MAX_SOURCE_WINDOWS;
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
use super::seg_desc::{BWD_COEFF_PUBLISH_TARGET_DEPTH, BWD_SEG_MAX_K};
use super::seg_lower::{
    assign_class, lower_bwd_seg, plan_publish_scratch, window_columns, BwdSegLowerError,
    BwdSegRoundBinding, BwdSegSetup, CoeffMode, D2Policy, ProgramMode, PublishScratchPlan,
    ResolvedBwdCoeffSourceWindow, ResolvedPublishScratch, SourceClass, SourceOrigin,
};
use crate::allocator::tracker::AllocationPlacement;
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
    seg_policy_k_with(
        bytes_per_row,
        ceiling,
        SEG_POLICY_NARROW_BYTES_PER_ROW,
        SEG_POLICY_WIDE_BYTES_PER_ROW,
    )
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
    /// Re-windowing against production geometry needs more windows than the
    /// descriptor format holds.
    TooManyWindows { windows: usize },
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
    UnresolvedCascade { window: u8, address: GKRAddress },
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
        })
    }
}

// ── Pointer resolution (production) ──────────────────────────────────────────

/// One round-0 binding, resolved against production storage.
pub(crate) struct BoundR0Sources {
    /// The coordinate REBOUND to production window geometry: same program,
    /// same order, same source-slot count — only the window partition and
    /// each slot's `(window, column)` changed. This is the artifact
    /// [`super::seg_lower::lower_bwd_seg`] must be handed; the original's
    /// windows no longer describe the pointers below.
    pub(crate) coord: LeanCoordinateArtifact,
    /// One entry per REBOUND window, positionally — exactly the slice
    /// [`super::seg_lower::BwdSegRoundBinding`] takes.
    pub(crate) windows: Vec<ResolvedBwdCoeffSourceWindow>,
    /// Per rebound window: elements readable per addressed column (the poly
    /// length).
    pub(crate) window_read_elements: Vec<u32>,
    /// Per rebound window: addressable column count, for the publish plan and
    /// the policy footprint.
    pub(crate) window_columns: Vec<usize>,
    /// The (empty — asserted) R0 publish plan, kept so the lowering's
    /// [`ResolvedPublishScratch`] is the SAME plan the bind checked rather
    /// than a re-derivation that could disagree.
    pub(crate) publish_plan: PublishScratchPlan,
}

/// One re-windowing run under construction: a maximal stretch of one artifact
/// window that production storage backs contiguously.
struct BindRun {
    /// Resolved base of the run's FIRST column; `None` for procedural.
    read: Option<ResolvedColumn>,
    /// The run's columns, at their ORIGINAL absolute numbers.
    columns: Vec<LeanBoundColumn>,
    /// Resolved pointer of the LAST column added (0 for procedural).
    prev_ptr: usize,
}

/// Resolve one R0 coordinate's windows against production storage,
/// re-partitioning them to production geometry.
///
/// The device resolves `(window, column)` as `base + column * stride`, so a
/// window must be CONTIGUOUS in the matrix it points into. The artifact's
/// windows are contiguous in the DAG's address space, not in storage (see the
/// module doc); this walks every referenced column, resolves it independently,
/// and splits each artifact window into maximal runs where consecutive
/// referenced columns satisfy `ptr(next) == ptr(prev) + gap * stride` at their
/// ORIGINAL column numbers. Keeping absolute numbering (rather than densely
/// renumbering) is what lets an absolute-indexed matrix — the base-layer
/// arenas, where a hole is a physically present column — stay ONE window
/// across holes, while a rank-packed matrix splits exactly at its gaps.
///
/// `rows` is the launch's logical row count; it enters only the (asserted
/// empty) publish plan.
pub(crate) fn bind_r0_sources<E: Copy>(
    storage: &GpuGKRStorage<BF, E>,
    coord: &LeanCoordinateArtifact,
    rows: usize,
) -> Result<BoundR0Sources, BwdVmBindError> {
    let shapes = r0_window_shapes(coord)?;

    let mut new_windows: Vec<LeanBoundWindow> = Vec::new();
    let mut bound: Vec<ResolvedBwdCoeffSourceWindow> = Vec::new();
    let mut read_elements: Vec<u32> = Vec::new();
    // Source slot -> rebound (window, column), filled as runs are flushed.
    let mut new_slots: Vec<Option<LeanSourceSlot>> =
        vec![None; coord.binding.source_slots.len()];

    for (index, (shape, artifact_window)) in
        shapes.iter().zip(&coord.binding.windows).enumerate()
    {
        let window = index as u8;
        let mut runs: Vec<BindRun> = Vec::new();
        for entry in &artifact_window.columns {
            let resolved = match family_read_place(artifact_window.family, entry.column) {
                // Procedural: no matrix at all — one run per artifact window.
                None => None,
                Some(place) => {
                    let address = read_place_to_gkr_address(&place);
                    let column = resolve_storage_column(storage, address)
                        .ok_or(BwdVmBindError::UnresolvedWindow { window, address })?;
                    if column.is_e4 != shape.is_e4 {
                        return Err(BwdVmBindError::WindowFieldMismatch {
                            window,
                            expect_e4: shape.is_e4,
                        });
                    }
                    Some(column)
                }
            };
            let continues = match (runs.last(), &resolved) {
                (None, _) => false,
                // A procedural window is one synthetic backing; it never splits.
                (Some(run), None) => run.read.is_none(),
                (Some(run), Some(next)) => run.read.is_some_and(|base| {
                    let prev = run.columns.last().expect("a run is never empty");
                    let gap = entry.column - prev.column;
                    next.stride_bytes == base.stride_bytes
                        && next.ptr as usize
                            == run.prev_ptr + gap * base.stride_bytes as usize
                }),
            };
            if !continues {
                runs.push(BindRun {
                    read: resolved,
                    columns: Vec::new(),
                    prev_ptr: 0,
                });
            }
            let run = runs.last_mut().expect("just started");
            run.columns.push(LeanBoundColumn {
                column: entry.column,
                source: entry.source,
            });
            run.prev_ptr = resolved.map_or(0, |r| r.ptr as usize);
        }

        for run in runs {
            if new_windows.len() >= MAX_SOURCE_WINDOWS {
                return Err(BwdVmBindError::TooManyWindows {
                    windows: new_windows.len() + 1,
                });
            }
            let nw = new_windows.len() as u8;
            let first_column = run.columns[0].column;
            for entry in &run.columns {
                new_slots[entry.source as usize] = Some(LeanSourceSlot {
                    window: nw,
                    column: (entry.column - first_column) as u16,
                });
            }
            let width = if shape.is_e4 {
                size_of::<E4>()
            } else {
                size_of::<BF>()
            } as u32;
            read_elements.push(run.read.map_or(0, |r| r.stride_bytes / width));
            bound.push(ResolvedBwdCoeffSourceWindow {
                read: run.read,
                publish: None,
                backing_depth: 0,
                target_depth: 0,
                materialize: shape.materialize,
            });
            new_windows.push(LeanBoundWindow {
                family: artifact_window.family,
                first_column,
                columns: run.columns,
            });
        }
    }

    let source_slots = new_slots
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .expect("every source slot belongs to exactly one artifact window column");
    let coord = LeanCoordinateArtifact {
        layer: coord.layer,
        regime: coord.regime,
        target_depth: coord.target_depth,
        order: coord.order.clone(),
        program: coord.program.clone(),
        binding: LeanSourceBinding {
            windows: new_windows,
            source_slots,
        },
    };
    let window_columns = window_columns(&coord.binding).map_err(BwdVmBindError::WindowShape)?;

    // R0 publishes nothing; a plan that wants bytes means the depth wiring is
    // wrong and must stop the proof before anything is allocated for it.
    let plan = plan_publish_scratch(&[&bound], &[&window_columns], &[rows])
        .map_err(BwdVmBindError::WindowShape)?;
    if plan.total_bytes != 0 {
        return Err(BwdVmBindError::PublishPlanNotEmpty {
            bytes: plan.total_bytes,
        });
    }

    Ok(BoundR0Sources {
        coord,
        windows: bound,
        window_read_elements: read_elements,
        window_columns,
        publish_plan: plan,
    })
}

// ── The Ext binding ──────────────────────────────────────────────────────────

/// One Ext binding: the coordinate rebound to production geometry — ONE
/// partition frozen across the whole round sequence, because the program's
/// source slots index windows positionally — plus per-round resolved windows.
pub(crate) struct BoundExtSources {
    /// The rebound coordinate, exactly as [`BoundR0Sources::coord`]: same
    /// program, same order, same slot count; only the window partition and
    /// each slot's `(window, column)` changed.
    pub(crate) coord: LeanCoordinateArtifact,
    /// `rounds[r - 1]` is round `r`'s resolution, `r` in `1..=folding_steps-1`.
    pub(crate) rounds: Vec<BoundExtRound>,
    /// Per rebound window: addressable column count (round-invariant).
    pub(crate) window_columns: Vec<usize>,
    /// The whole sequence's publish plan, absolute-round indexed. Structurally
    /// EMPTY — every publish is explicitly backed by a cascade slot — and
    /// asserted so; a nonzero plan means a window lost its backing.
    pub(crate) publish_plan: PublishScratchPlan,
}

/// One round's resolution over the frozen window partition.
pub(crate) struct BoundExtRound {
    pub(crate) round: u8,
    pub(crate) rows: usize,
    pub(crate) windows: Vec<ResolvedBwdCoeffSourceWindow>,
    /// Per window: elements readable per addressed column — the raw poly
    /// length on raw rounds, the previous slot's length on chained rounds.
    pub(crate) window_read_elements: Vec<u32>,
}

/// One frozen run under construction: a maximal stretch of one artifact window
/// that production backs contiguously on BOTH sides the sequence will address
/// through it — the depth-0 matrix (raw rounds) AND the cascade regions
/// (publishes and chain reads).
struct ExtBindRun {
    /// The parent ARTIFACT window — the per-round shape is its.
    parent: usize,
    /// First column's raw backing; `None` for procedural.
    raw: Option<ResolvedColumn>,
    /// First column's cascade region.
    cascade: CascadeRegion,
    columns: Vec<LeanBoundColumn>,
    prev_raw_ptr: usize,
    prev_cascade_base: usize,
}

/// Resolve one Ext coordinate's windows against production storage for the
/// whole continuation sequence, re-partitioning them to production geometry.
///
/// The split rule is the UNION of the R0 binder's raw-read contiguity and
/// cascade contiguity: a run continues over a column gap `g` iff the raw
/// pointers advance by exactly `g * stride` (holes physically present — the
/// base-layer arenas) AND the cascade regions advance by exactly
/// `g * region_bytes` (the consolidated backings pack REGISTERED addresses
/// densely, so an arena hole with no cache slot splits the run — the publish
/// side cannot address across it). Frozen once: the same partition serves
/// every round, raw and chained alike.
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

    // ── Freeze the partition ─────────────────────────────────────────────────
    let mut runs: Vec<ExtBindRun> = Vec::new();
    for (parent, artifact_window) in coord.binding.windows.iter().enumerate() {
        let window = parent as u8;
        let e4_origin = artifact_window.backing_field() == FieldKind::Ext;
        let mut parent_runs = 0usize;
        for entry in &artifact_window.columns {
            let (raw, address) = match family_read_place(artifact_window.family, entry.column) {
                Some(place) => {
                    let address = read_place_to_gkr_address(&place);
                    let column = resolve_storage_column(storage, address)
                        .ok_or(BwdVmBindError::UnresolvedWindow { window, address })?;
                    if column.is_e4 != e4_origin {
                        return Err(BwdVmBindError::WindowFieldMismatch {
                            window,
                            expect_e4: e4_origin,
                        });
                    }
                    (Some(column), address)
                }
                None => match artifact_window.family {
                    WindowFamily::VirtualSetup { kind } => (None, virtual_setup_address(kind)),
                    // `family_read_place` is total over the other families.
                    _ => unreachable!("an addressless window is procedural"),
                },
            };
            let cascade = resolve_cascade_region(storage, request_layer, address, e4_origin)
                .ok_or(BwdVmBindError::UnresolvedCascade { window, address })?;

            let continues = parent_runs > 0 && {
                let run = runs.last().expect("parent_runs > 0");
                let prev = run.columns.last().expect("a run is never empty");
                let gap = entry.column - prev.column;
                let raw_continues = match (&run.raw, &raw) {
                    (None, None) => true,
                    (Some(base), Some(next)) => {
                        next.stride_bytes == base.stride_bytes
                            && next.ptr as usize
                                == run.prev_raw_ptr + gap * base.stride_bytes as usize
                    }
                    _ => false,
                };
                let region_bytes = run.cascade.region_elems * size_of::<E4>();
                raw_continues
                    && cascade.region_elems == run.cascade.region_elems
                    && cascade.first_slot == run.cascade.first_slot
                    && cascade.base as usize == run.prev_cascade_base + gap * region_bytes
            };
            if !continues {
                runs.push(ExtBindRun {
                    parent,
                    raw,
                    cascade,
                    columns: Vec::new(),
                    prev_raw_ptr: 0,
                    prev_cascade_base: 0,
                });
                parent_runs += 1;
            }
            let run = runs.last_mut().expect("just started");
            run.columns.push(LeanBoundColumn {
                column: entry.column,
                source: entry.source,
            });
            run.prev_raw_ptr = raw.map_or(0, |column| column.ptr as usize);
            run.prev_cascade_base = cascade.base as usize;
        }
    }
    if runs.len() > MAX_SOURCE_WINDOWS {
        return Err(BwdVmBindError::TooManyWindows {
            windows: runs.len(),
        });
    }

    // ── Rebuild the coordinate over the frozen partition ─────────────────────
    let mut new_windows: Vec<LeanBoundWindow> = Vec::with_capacity(runs.len());
    let mut new_slots: Vec<Option<LeanSourceSlot>> =
        vec![None; coord.binding.source_slots.len()];
    for (index, run) in runs.iter().enumerate() {
        let first_column = run.columns[0].column;
        for entry in &run.columns {
            new_slots[entry.source as usize] = Some(LeanSourceSlot {
                window: index as u8,
                column: (entry.column - first_column) as u16,
            });
        }
        new_windows.push(LeanBoundWindow {
            family: coord.binding.windows[run.parent].family,
            first_column,
            columns: run.columns.clone(),
        });
    }
    let source_slots = new_slots
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .expect("every source slot belongs to exactly one artifact window column");
    let coord_rebound = LeanCoordinateArtifact {
        layer: coord.layer,
        regime: coord.regime,
        target_depth: coord.target_depth,
        order: coord.order.clone(),
        program: coord.program.clone(),
        binding: LeanSourceBinding {
            windows: new_windows,
            source_slots,
        },
    };
    let window_columns =
        window_columns(&coord_rebound.binding).map_err(BwdVmBindError::WindowShape)?;

    // ── Resolve every round over the frozen partition ────────────────────────
    let mut rounds = Vec::with_capacity(folding_steps - 1);
    for round in 1..folding_steps {
        let rows = 1usize << (folding_steps - round - 1);
        let round = round as u8;
        let shapes = ext_round_window_shapes(coord, round, d2)?;
        let mut windows = Vec::with_capacity(runs.len());
        let mut read_elements = Vec::with_capacity(runs.len());
        for run in &runs {
            let shape = &shapes[run.parent];
            let region_stride =
                u32::try_from(run.cascade.region_elems * size_of::<E4>()).expect("region stride");
            let read = if shape.chained {
                // The chain read IS the previous round's publish: the same
                // cascade lookup, one slot back — the invariant the parity
                // model enforced with `ChainReadNotPriorPublish` holds here
                // by construction.
                Some(ResolvedColumn {
                    is_e4: true,
                    ptr: run.cascade.slot_ptr(round - 1).cast_const(),
                    matrix_base: run.cascade.base,
                    stride_bytes: region_stride,
                })
            } else {
                run.raw
            };
            let publish = shape.materialize.then(|| ResolvedColumn {
                is_e4: true,
                ptr: run.cascade.slot_ptr(round).cast_const(),
                matrix_base: run.cascade.base,
                stride_bytes: region_stride,
            });
            read_elements.push(match &read {
                _ if shape.chained => run.cascade.slot_elems(round - 1) as u32,
                Some(column) => {
                    let width = if column.is_e4 {
                        size_of::<E4>()
                    } else {
                        size_of::<BF>()
                    } as u32;
                    column.stride_bytes / width
                }
                None => 0,
            });
            windows.push(ResolvedBwdCoeffSourceWindow {
                read,
                publish,
                backing_depth: shape.backing_depth,
                target_depth: round,
                materialize: shape.materialize,
            });
        }
        rounds.push(BoundExtRound {
            round,
            rows,
            windows,
            window_read_elements: read_elements,
        });
    }

    // ── The (empty) plan for the whole sequence ──────────────────────────────
    // Round 0 belongs to the R0 program and plans nothing here; every window
    // of rounds 1+ is explicitly backed, so the plan must reserve nothing.
    let empty_windows: Vec<ResolvedBwdCoeffSourceWindow> = Vec::new();
    let empty_columns: Vec<usize> = Vec::new();
    let mut windows_per_round: Vec<&[ResolvedBwdCoeffSourceWindow]> = vec![&empty_windows];
    let mut columns_per_round: Vec<&[usize]> = vec![&empty_columns];
    let mut rows_per_round: Vec<usize> = vec![1 << (folding_steps - 1)];
    for bound in &rounds {
        windows_per_round.push(&bound.windows);
        columns_per_round.push(&window_columns);
        rows_per_round.push(bound.rows);
    }
    let plan = plan_publish_scratch(&windows_per_round, &columns_per_round, &rows_per_round)
        .map_err(BwdVmBindError::WindowShape)?;
    if plan.total_bytes != 0 {
        return Err(BwdVmBindError::PublishPlanNotEmpty {
            bytes: plan.total_bytes,
        });
    }

    Ok(BoundExtSources {
        coord: coord_rebound,
        rounds,
        window_columns,
        publish_plan: plan,
    })
}

// ── The R0 launch ────────────────────────────────────────────────────────────

/// The per-row device footprint of one bound R0 launch — the `K` policy's
/// input.
///
/// The bench probes this off its host model (`probe_geometry`, bench-gated);
/// this is the same formula stated over the BOUND geometry, at R0's fixed
/// shape: the two contribution halves, plus `columns * 2 * width` per real
/// window (delta 0 reads one endpoint pair per column per logical row), plus
/// nothing procedural (synthesized, no DRAM) and nothing published (asserted
/// empty at R0).
pub(crate) fn seg_r0_bytes_per_row(
    windows: &[ResolvedBwdCoeffSourceWindow],
    columns: &[usize],
) -> usize {
    let mut bytes = 2 * size_of::<E4>();
    for (window, &columns) in windows.iter().zip(columns) {
        debug_assert!(!window.materialize, "R0 publishes nothing");
        let element = match window.read {
            None => 0,
            Some(read) if read.is_e4 => size_of::<E4>(),
            Some(_) => size_of::<BF>(),
        };
        bytes += columns * 2 * element;
    }
    bytes
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
    let bytes_per_row = seg_r0_bytes_per_row(&bound.windows, &bound.window_columns);
    let k = seg_policy_k(bytes_per_row, seg_k_ceiling(BwdRegime::R0)?);
    let binding = BwdSegRoundBinding {
        round: 0,
        rows,
        windows: &bound.windows,
        window_read_elements: &bound.window_read_elements,
        claim_point: &[],
        coefficients: &coefficients,
        c_init: None,
        immediates: &[],
        eq_low,
        eq_sizes,
        contributions,
        acc_size: rows as u32,
    };
    let setup = lower_bwd_seg(
        &bound.coord,
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
        // SAFETY: `contributions` is `round_scratch.accumulator`'s live device
        // pointer and the allocation holds `2 * max_acc_size >= 2 * acc_size`
        // elements; the poison writes exactly the two halves this launch owns.
        let dst = unsafe {
            DeviceSlice::from_raw_parts_mut(contributions, 2 * acc_size as usize)
        };
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
pub(crate) fn seg_ext_bytes_per_row(
    windows: &[ResolvedBwdCoeffSourceWindow],
    columns: &[usize],
) -> usize {
    let mut bytes = 2 * size_of::<E4>();
    for (window, &columns) in windows.iter().zip(columns) {
        let element = match window.read {
            None => 0,
            Some(read) if read.is_e4 => size_of::<E4>(),
            Some(_) => size_of::<BF>(),
        };
        let delta = window.target_depth - window.backing_depth;
        bytes += columns * (2usize << delta) * element;
        if window.materialize {
            bytes += columns * 2 * size_of::<E4>();
        }
    }
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
    contributions: *mut E4,
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
        let bytes_per_row = seg_ext_bytes_per_row(&round.windows, &bound.window_columns);
        let k = seg_policy_k(bytes_per_row, ceiling);
        let binding = BwdSegRoundBinding {
            round: u32::from(round.round),
            rows: round.rows,
            windows: &round.windows,
            window_read_elements: &round.window_read_elements,
            claim_point: &claim_point,
            coefficients: &coefficients,
            c_init: slice.layer.c_init,
            immediates: &slice.layer.immediates,
            eq_low,
            eq_sizes: drained_eq_sizes(make_eq_sizes(folding_steps - 1), round.round),
            contributions,
            acc_size: round.rows as u32,
        };
        setups.push(
            lower_bwd_seg(
                &bound.coord,
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
    let (lowered_rows, contributions) = match &setup.desc {
        super::seg_lower::BwdSegLaunchDesc::Inline(desc) => (desc.logical_rows, desc.contributions),
        super::seg_lower::BwdSegLaunchDesc::ProgPtr(desc) => {
            (desc.logical_rows, desc.contributions)
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
        // SAFETY: `contributions` is the accumulator's live device pointer and
        // the allocation holds `2 * max_acc_size >= 2 * acc_size` elements.
        let dst = unsafe { DeviceSlice::from_raw_parts_mut(contributions, 2 * acc_size as usize) };
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
