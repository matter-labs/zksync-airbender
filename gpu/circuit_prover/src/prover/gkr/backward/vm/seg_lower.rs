//! Host lowering for the SEGMENTED lean VM (segmented-lean-VM design §3, §5,
//! §6, §7): bind one round's physical geometry to a `K`-free lean coordinate and
//! build the complete by-value launch descriptor.
//!
//! The artifact ([`LeanCoordinateArtifact`]) is a pure function of the DAG: a
//! committed term order, a fixed-width program, and a placement-free source
//! binding. Everything PHYSICAL is here, and only here:
//!
//!   1. the per-`(source, round)` [`SourceClass`] — the axis that decides how the
//!      operand behind a wire slot is produced (raw read, inline fold, folded
//!      register, procedural synthesis);
//!   2. the publish-scratch geometry the JAOT prologue writes through and the
//!      NEXT round's chain reads from ([`plan_publish_scratch`] plans the whole
//!      round sequence; [`lower_bwd_seg`] resolves one round of it);
//!   3. the `K`-split of the committed order into per-warp lists — whole ATOMS,
//!      least-loaded for Ext ([`deal_atoms`]) and round-robin for R0 — with its
//!      per-atom work model ([`atom_work`], [`ListWorkStats`]); and
//!   4. the validations a release kernel with no error channel cannot make for
//!      itself.
//!
//! # Where the round's truth comes from
//!
//! The compile-time window FAMILY says where a source lives in the DAG. It does
//! NOT say what is physically there at round `r`: a base-field or virtual-setup
//! source that a previous round materialized is an E4 matrix now. The old
//! cell-era lowering derived the window ORIGIN from that compile-time family,
//! which would refold raw data that has moved — silently, in a release kernel.
//! Here the ROUND BINDING supplies the origin ([`ResolvedBwdCoeffSourceWindow::read`]'s
//! own field), and the family is consulted for exactly one thing: whether the
//! window is procedural at all. The descriptor's `procedural_kind` is therefore a
//! PER-ROUND statement — it is cleared for a window that resolves from DRAM this
//! round even though its family is a virtual setup.
//!
//! # Two-pass by necessity
//!
//! Lowering needs resolved scratch POINTERS, and allocation is the caller's. So
//! planning ([`plan_publish_scratch`], which knows the whole round sequence
//! because the row count halves per round and no single stride serves both the
//! prior-round read and the current-round write) is separated from filling
//! ([`lower_bwd_seg`], which takes the caller's [`ResolvedPublishScratch`]).
//!
//! Nothing in this module dereferences a device pointer, so it is fully testable
//! on the CPU: see [`seg_lower_tests`](super::seg_lower_tests).

// TASK 7 launches with these descriptors; until then the module is referenced
// only by its tests. Scoped here rather than on the parent.
#![allow(dead_code)]

use gkr_eval_isa::bwd::coeff::lean::{
    decode_atoms, LeanAtom, LeanCodecError, LeanTerm, LEAN_CONT_OPCODES, LEAN_R0_OPCODES,
    LEAN_WORDS_PER_TERM, SOURCE_NONE,
};
use gkr_eval_isa::bwd::coeff::lean_artifact::LeanCoordinateArtifact;
use gkr_eval_isa::bwd::coeff::lean_bind::LeanSourceBinding;
use gkr_eval_isa::bwd::coeff::limits::{
    category_arity, in_scope, TermCategory, LEAN_DESCRIPTOR_PROGRAM_WORDS, LEAN_MAX_IMMEDIATES,
    MAX_COEFFICIENT_ENCODINGS, SOURCE_WINDOW_COLUMNS,
};
use gkr_eval_isa::bwd::coeff::model::{CoefficientRecipeId, ImmediateId};
use gkr_eval_isa::bwd::coeff::order::split_round_robin;

use super::seg_desc::{
    bwd_seg_lane, bwd_seg_lane_column, bwd_seg_lane_slot, BwdSegAddrSlot, BwdSegDesc, BwdSegProgPtrDesc, BwdSegSourceRecord,
    BWD_COEFF_MAX_FOLD_DEPTH, BWD_COEFF_ORIGIN_PROCEDURAL, BWD_COEFF_ORIGIN_READ_BASE,
    BWD_COEFF_ORIGIN_READ_EXT, BWD_COEFF_PROCEDURAL_KINDS, BWD_COEFF_PROCEDURAL_NONE,
    BWD_COEFF_PUBLISH_TARGET_DEPTH, BWD_SEG_CONST_BANK, BWD_SEG_C_INIT_NONE, BWD_SEG_MAX_K,
    BWD_SEG_ADDR_NONE, BWD_SEG_ADDR_SLOTS, BWD_SEG_MAX_SOURCES,
};
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::backward::GkrEqSizes;
use crate::prover::gkr::forward::vm::lower::ResolvedColumn;
use crate::upstream::{BwdRegime, PrimeField};

/// Bytes one column of a backing occupies, by storage field.
const BF_COLUMN_BYTES: u32 = 4;
const E4_COLUMN_BYTES: u32 = 16;

/// The bounded lazy-fold resolver this round needs (§10.2).
///
/// Rounds 0..=3 map to D0..D3. From [`BWD_COEFF_PUBLISH_TARGET_DEPTH`] `+ 1` on,
/// every materializing source has already published at its target depth, so a
/// backing is at most ONE fold behind and D1 is exact — which is why the resolver
/// set stays bounded instead of growing with the round index.
pub(crate) fn bwd_coeff_fold_depth(round: u8) -> u8 {
    match round {
        0 => 0,
        1 => 1,
        2 => 2,
        3 => 3,
        _ => 1,
    }
}

/// The round's physical geometry for ONE bound source window.
///
/// Indexed positionally by wire window: entry `w` describes
/// `LeanSourceBinding::windows[w]`. `read`/`publish` name the window's FIRST
/// column, so the device resolves a bound coordinate as
/// `read_base + column * read_stride_bytes`.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ResolvedAddrSlot {
    /// The backing's base column. `None` only for a procedural slot, whose
    /// values are produced from the row rather than read.
    pub base: Option<ResolvedColumn>,
    /// The procedural kind when this slot synthesizes, else `None`.
    pub procedural_kind: Option<u8>,
    /// Elements readable at the base, per addressed column — the span length
    /// `ResolvedColumn` has no field for, and the reason a short backing is a
    /// rejection here instead of an out-of-bounds read on the device.
    pub read_elements: u32,
    /// Addressable columns. A slot covers at most [`SOURCE_WINDOW_COLUMNS`] of
    /// its backing; a wider backing takes several slots at offset bases.
    pub columns: usize,
    /// This slot's backing does not exist yet: its ADDRESS arrives between
    /// lowering and launch (the production Ext launch's just-in-time folding
    /// buffers), and `base`'s pointer is a byte OFFSET from the eventual
    /// allocation rather than a device address — which is exactly what makes the
    /// offset-from-null arithmetic resolve to the right column.
    ///
    /// Lowering validates everything the shape carries (field, stride, columns,
    /// span) and emits a NULL base for the caller to fill in with
    /// [`BwdSegLaunchDesc::slots_mut`]. Two obligations move to the caller with
    /// the address: patching every deferred slot before the launch, and the
    /// aliasing proof [`check_alias`] cannot make without addresses — for the
    /// folding buffers that proof is structural, since a round's destination and
    /// its reads are different allocations of the pool.
    pub deferred_base: bool,
}

/// One wire source's ADDRESSES for one round: which slot and column it reads,
/// and where its fold publishes.
///
/// Read and destination are independent by construction, which is the whole
/// point of the two-lane record: a matrix and the fold buffer its columns
/// materialize into are packed differently, so one index cannot serve both.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ResolvedSourceAddr {
    /// Slot index into the round's table, and the column within it.
    pub read_slot: usize,
    pub read_column: usize,
    /// Where this source's fold publishes, when the caller backs it explicitly
    /// (production: a column of the round's own folding buffer). `None`
    /// leaves the destination to the publish-scratch plan, which is what the
    /// bench's host model uses.
    pub publish: Option<(usize, usize)>,
    /// Depth this source's read backing is currently at. Per source, not per
    /// slot: two artifact windows may read one matrix at different depths.
    pub backing_depth: u8,
}

// ── Source classes ───────────────────────────────────────────────────────────

/// How the operand behind ONE wire source slot is produced at ONE round.
///
/// This is the AUTHORITY for [`BwdSegSourceRecord::class`]'s five documented
/// numbers (`seg_desc.rs`'s struct doc states them; the assertion below is what
/// makes them binding). It is NOT the lean wire's three-bit TERM class: the term
/// class fixes an operation's projection and arity, this fixes where its operand
/// comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub(crate) enum SourceClass {
    /// A matrix read already at target depth: no fold at all.
    BfDirect = 0,
    /// Raw base field, one fold behind: two raw values per endpoint, folded in
    /// registers.
    BfInlineD1 = 1,
    /// Raw base field, two folds behind: four raw values per endpoint, folded in
    /// registers. The alternative is [`D2Policy::Materialize`], which turns the
    /// same window into a published E4 pyramid instead.
    BfInlineD2 = 2,
    /// An E4 value the prologue produced (a chain step, a BF pyramid, or a
    /// procedural materialization) or read directly at target depth.
    E4Direct = 3,
    /// Synthesized from the row index; no DRAM read.
    ProceduralInline = 4,
}

impl SourceClass {
    pub(crate) const fn code(self) -> u8 {
        self as u8
    }
}

// The `class: u8` byte's documented values. `seg_desc` states them in prose and
// cannot enforce them (the enum is here), so this is the whole guard against the
// two halves drifting.
const _: () = {
    assert!(SourceClass::BfDirect.code() == 0);
    assert!(SourceClass::BfInlineD1.code() == 1);
    assert!(SourceClass::BfInlineD2.code() == 2);
    assert!(SourceClass::E4Direct.code() == 3);
    assert!(SourceClass::ProceduralInline.code() == 4);
    // The publish depth the procedural row of the assignment matrix pivots on is
    // the descriptor's own, never a second copy.
    assert!(BWD_COEFF_PUBLISH_TARGET_DEPTH == 3);
};

/// What is PHYSICALLY behind a window at this round — the class matrix's first
/// axis.
///
/// Derived from the round binding, never from the compile-time family: see the
/// module doc.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SourceOrigin {
    Bf,
    E4,
    Procedural,
}

/// The one genuine policy choice in the matrix: what to do with a base-field
/// window that is TWO folds behind.
///
/// `Materialize` has an explicit ABI representation (the window's
/// `materialize` flag plus a fold-list entry), so it is a lowering decision the
/// descriptor carries, not a kernel flag.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum D2Policy {
    Inline,
    Materialize,
}

/// Which coefficient loader the launch is specialized for.
///
/// In BOTH modes [`BwdSegSetup::coefficients`] is the RESERVED-INCLUSIVE payload
/// `[ONE, NEG_ONE, recipes…]` (RR ruling 2026-07-27) and the descriptor's
/// `coefficients` pointer is left null: `Constant` uploads the payload to the
/// `ab_gkr_bwd_seg_coeff_bank` symbol, `DevPtr` uploads it to a device buffer and
/// patches the pointer into its host copy of the descriptor before launch.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CoeffMode {
    Constant,
    DevPtr,
}

/// Which program family the launch uses: the by-value array, or the spike-only
/// device-pointer twin.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ProgramMode {
    Inline,
    DevPtr,
}

/// The lowered descriptor, boxed.
///
/// Boxed on purpose: the inline descriptor is 26 KB of `Copy` data, and moving it
/// through the stack by value both costs a memcpy per move and risks carrying
/// uninitialized interior padding into the launch. Lowering allocates it
/// ZEROED and fills named fields, so the launch bytes are deterministic.
pub(crate) enum BwdSegLaunchDesc {
    Inline(Box<BwdSegDesc>),
    ProgPtr(Box<BwdSegProgPtrDesc>),
}

impl BwdSegLaunchDesc {
    /// The address table, mutable.
    ///
    /// Exists for ONE caller: a destination whose backing is created at
    /// schedule time rather than at lowering (the production Ext launch's
    /// just-in-time folding buffers). Lowering validates the slot's SHAPE —
    /// field, stride, column count, span — none of which the base pointer
    /// carries, so filling the base in later is a pointer substitution, not a
    /// second lowering. Nothing else may reach into a lowered descriptor.
    pub(crate) fn slots_mut(&mut self) -> &mut [BwdSegAddrSlot] {
        match self {
            Self::Inline(desc) => &mut desc.slot,
            Self::ProgPtr(desc) => &mut desc.slot,
        }
    }
}

// ── Publish scratch planning ─────────────────────────────────────────────────

/// [`PublishRoundLayout::window_base`] entry for a window that publishes NOTHING
/// at that round. Not zero: zero is the first publishing window's own offset.
pub(crate) const PUBLISH_WINDOW_ABSENT: usize = usize::MAX;

/// One round's publish layout inside ONE parity buffer.
///
/// The backing of a publishing window is `columns` consecutive column regions of
/// `column_stride_bytes` bytes each, so a source at window-relative column `c`
/// publishes at `window_base[w] + c * column_stride_bytes` — the same
/// base-plus-stride shape [`BwdCoeffSourceWindow`] already models.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PublishRoundLayout {
    /// Bytes this round needs in its parity buffer.
    pub bytes: usize,
    /// Per window (indexed by window slot, NOT densified): the byte offset of its
    /// column-0 backing, or [`PUBLISH_WINDOW_ABSENT`].
    ///
    /// Indexed by window rather than packed over the publishing ones so that
    /// resolving a window needs no second computation of which windows fold —
    /// the one place that decision is made is [`assign_class`].
    pub window_base: Vec<usize>,
    /// `2 * rows_r * 16`: both endpoint halves of every row, as E4.
    pub column_stride_bytes: usize,
}

/// The publish geometry of a WHOLE round sequence.
///
/// One layout per round, because the row count halves per round: no single
/// stride can serve both round `r - 1`'s read and round `r`'s write. Two buffers
/// suffice regardless of the sequence length — round `r` writes parity `r & 1`
/// and reads parity `(r + 1) & 1` — so each parity is sized by the WORST round it
/// serves, not by the sum.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PublishScratchPlan {
    /// Indexed by ABSOLUTE round. A round that publishes nothing costs nothing.
    pub per_round: Vec<PublishRoundLayout>,
    /// Bytes each parity buffer must hold: the max over the rounds it serves.
    pub bytes_per_parity: [usize; 2],
    /// `bytes_per_parity[0] + bytes_per_parity[1]`.
    pub total_bytes: usize,
}

/// A plan plus the caller's two allocations.
///
/// **The parity rule (normative).** Round `r`'s prologue WRITES via
/// `plan.per_round[r]` offsets into `parity_base[r & 1]`, and its E4 chain READS
/// round `r - 1`'s publishes via `plan.per_round[r - 1]` offsets from
/// `parity_base[(r + 1) & 1]`. The write stride is this round's
/// `column_stride_bytes`, the read stride the previous round's.
pub(crate) struct ResolvedPublishScratch {
    pub parity_base: [*mut u8; 2],
    pub plan: PublishScratchPlan,
}

/// Plan the publish scratch for a whole round sequence.
///
/// The three slices are parallel and indexed by ABSOLUTE round: `windows_per_round[r]`
/// is round `r`'s bound windows, `columns_per_round[r]` their addressable column
/// counts ([`window_columns`] derives these from the artifact), `rows_per_round[r]`
/// its logical row count. A round with no windows is legal and plans nothing.
///
/// A window publishes at round `r` iff its
/// [`ResolvedBwdCoeffSourceWindow::materialize`] is set — the caller's
/// declaration, which [`lower_bwd_seg`] then checks against the class the policy
/// actually derives, so a plan and a lowering cannot disagree about who publishes.
///
/// Validates STRUCTURAL non-overlap within each parity buffer. It cannot validate
/// anything about POINTERS: there are none yet.
pub(crate) fn plan_publish_scratch(
    windows_per_round: &[&[bool]],
    columns_per_round: &[&[usize]],
    rows_per_round: &[usize],
) -> Result<PublishScratchPlan, BwdSegLowerError> {
    if windows_per_round.len() != rows_per_round.len()
        || columns_per_round.len() != rows_per_round.len()
    {
        return Err(BwdSegLowerError::PlanRoundCountMismatch {
            windows: windows_per_round.len(),
            columns: columns_per_round.len(),
            rows: rows_per_round.len(),
        });
    }

    let mut per_round = Vec::with_capacity(rows_per_round.len());
    for (round, ((windows, columns), &rows)) in windows_per_round
        .iter()
        .zip(columns_per_round)
        .zip(rows_per_round)
        .enumerate()
    {
        if windows.len() != columns.len() {
            return Err(BwdSegLowerError::PlanShapeMismatch {
                round,
                windows: windows.len(),
                entries: columns.len(),
            });
        }
        let column_stride_bytes = rows
            .checked_mul(2 * E4_COLUMN_BYTES as usize)
            .ok_or(BwdSegLowerError::PublishScratchOverflow { round })?;

        let mut window_base = vec![PUBLISH_WINDOW_ABSENT; windows.len()];
        let mut regions: Vec<(u8, usize, usize)> = Vec::new();
        let mut cursor = 0usize;
        for (index, bound) in windows.iter().enumerate() {
            // A slot whose sources publish into a caller-supplied region
            // (production: the layer's own fold storage) needs no parity
            // reservation — `lower_source` takes its explicit arm on the ABSENT
            // entry this leaves behind.
            if !*bound {
                continue;
            }
            let span = columns[index]
                .checked_mul(column_stride_bytes)
                .ok_or(BwdSegLowerError::PublishScratchOverflow { round })?;
            let end = cursor
                .checked_add(span)
                .ok_or(BwdSegLowerError::PublishScratchOverflow { round })?;
            window_base[index] = cursor;
            regions.push((u8::try_from(index).unwrap_or(u8::MAX), cursor, end));
            cursor = end;
        }
        // Packed by a cursor, so disjoint by construction — checked anyway,
        // because "the regions of one parity buffer are disjoint" is the
        // property every publish pointer downstream rests on.
        check_regions_disjoint(&regions)?;

        per_round.push(PublishRoundLayout {
            bytes: cursor,
            window_base,
            column_stride_bytes,
        });
    }

    let mut bytes_per_parity = [0usize; 2];
    for (round, layout) in per_round.iter().enumerate() {
        let parity = round & 1;
        bytes_per_parity[parity] = bytes_per_parity[parity].max(layout.bytes);
    }
    Ok(PublishScratchPlan {
        total_bytes: bytes_per_parity[0] + bytes_per_parity[1],
        per_round,
        bytes_per_parity,
    })
}

/// The read column round `round`'s E4 chain must use for `window`, or `None` when
/// the previous round published nothing for it.
///
/// The ONE place the parity-plus-offset arithmetic of the chain lives: a caller
/// builds the round's [`ResolvedBwdCoeffSourceWindow::read`] from this, and
/// [`lower_bwd_seg`] re-derives it and rejects a disagreement
/// ([`BwdSegLowerError::ChainReadNotPriorPublish`]).
pub(crate) fn chain_read_column(
    scratch: &ResolvedPublishScratch,
    round: u32,
    window: usize,
) -> Option<(*const u8, u32)> {
    let previous = usize::try_from(round).ok()?.checked_sub(1)?;
    let layout = scratch.plan.per_round.get(previous)?;
    let offset = *layout.window_base.get(window)?;
    if offset == PUBLISH_WINDOW_ABSENT {
        return None;
    }
    let base = scratch.parity_base[((round + 1) & 1) as usize];
    if base.is_null() {
        return None;
    }
    let stride = u32::try_from(layout.column_stride_bytes).ok()?;
    // SAFETY: the offset is inside the parity buffer the plan sized, which the
    // caller allocated; this computes an address and never reads it.
    Some((unsafe { base.add(offset) } as *const u8, stride))
}

/// `[(window, lo, hi)]` regions must be pairwise disjoint.
pub(crate) fn check_regions_disjoint(
    regions: &[(u8, usize, usize)],
) -> Result<(), BwdSegLowerError> {
    for (index, &(window, lo, hi)) in regions.iter().enumerate() {
        for &(other, other_lo, other_hi) in &regions[..index] {
            if lo < other_hi && other_lo < hi {
                return Err(BwdSegLowerError::UnsafePublishAlias { window, other });
            }
        }
    }
    Ok(())
}

// ── Per-list work model ──────────────────────────────────────────────────────

/// One wire term annotated with the SOURCE classes its operands resolved to —
/// the input the static cost model needs and the wire alone cannot supply.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct AnnotatedTerm {
    /// The term class's category: its projection and arity.
    pub category: TermCategory,
    /// Per operand slot, in wire order. `None` past the category's arity.
    pub operands: [Option<SourceClass>; 2],
}

/// Static work of one term, in arbitrary comparable units.
///
/// The model, documented once here because it is the only thing that decides
/// whether a `K`-split is balanced:
///
/// | contribution | cost | why |
/// |---|---|---|
/// | `C0Linear*` | 2 | one E4 multiply-add against the coefficient |
/// | `C2Product*` | 6 | two E4 multiplies plus the accumulate |
/// | `DualProductE4` | 10 | both projections of both operands |
/// | `BfInlineD1` operand | +4 | two raw reads and one fold per endpoint |
/// | `BfInlineD2` operand | +10 | four raw reads and a two-level fold |
/// | `ProceduralInline` operand | +3 | closed-form synthesis from the row |
/// | `BfDirect` / `E4Direct` operand | +0 | a load, or an already-folded register |
///
/// Relative, not absolute: it exists to compare LISTS of the same program, and
/// [`ListWorkStats::max_over_mean`] is the only number read off it.
///
/// This is the SINGLETON / plain-record price. A grouped member is priced by
/// [`member_work`] and a whole group by [`atom_work`], because the coefficient FMA
/// this model charges every term is exactly what grouping removes (spec §4.5).
pub(crate) fn static_term_work(term: &AnnotatedTerm) -> u64 {
    static_term_work_base(term.category) + operand_work(term)
}

/// The CATEGORY half of [`static_term_work`]: the term body, coefficient FMA
/// included. Split out because a GROUPED member performs no coefficient multiply
/// of its own (spec §4.5) and therefore wants the operand half alone plus its own
/// smaller body.
pub(crate) fn static_term_work_base(category: TermCategory) -> u64 {
    match category {
        TermCategory::C0LinearBf | TermCategory::C0LinearE4 => 2,
        TermCategory::C2ProductBfBf | TermCategory::C2ProductBfE4 | TermCategory::C2ProductE4E4 => {
            6
        }
        TermCategory::DualProductE4 => 10,
        // The lean class tables carry no `Move` rows, so no wire record can
        // decode to one.
        TermCategory::MoveBf | TermCategory::MoveE4 => 0,
    }
}

/// The OPERAND half of [`static_term_work`]: what resolving this term's operands
/// costs, which a grouped member pays in full.
pub(crate) fn operand_work(term: &AnnotatedTerm) -> u64 {
    term.operands
        .iter()
        .flatten()
        .map(|class| match class {
            SourceClass::BfInlineD1 => 4,
            SourceClass::BfInlineD2 => 10,
            SourceClass::ProceduralInline => 3,
            SourceClass::BfDirect | SourceClass::E4Direct => 0,
        })
        .sum()
}

// ── Atoms: the unit the deal places ──────────────────────────────────────────

/// One member of a decoded group atom.
///
/// A member's wire coefficient field is an IMMEDIATE id, not a recipe id (spec
/// §4.4): `0` is `+1`, `1` is `-1`, and `id >= 2` addresses
/// `immediates[id - 2]` of the grouped layer's table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SegMember {
    /// The member record's category and operand classes — the same annotation a
    /// plain record carries.
    pub annotated: AnnotatedTerm,
    /// The wire immediate id.
    pub immediate: u16,
}

impl SegMember {
    /// How many accumulator sides a NON-`±1` immediate costs a `BF × E4` multiply
    /// on (spec §4.5): one for a linear member, two for a dual member, which
    /// applies its immediate to both partial sums. `None` for the two literals,
    /// which the kernel folds into an add or a subtract.
    pub(crate) fn immediate_sides(&self) -> Option<u64> {
        if self.immediate < ImmediateId::RESERVED {
            return None;
        }
        Some(match self.annotated.category {
            TermCategory::DualProductE4
            | TermCategory::C2ProductBfBf
            | TermCategory::C2ProductBfE4
            | TermCategory::C2ProductE4E4 => 2,
            TermCategory::C0LinearBf
            | TermCategory::C0LinearE4
            | TermCategory::MoveBf
            | TermCategory::MoveE4 => 1,
        })
    }
}

/// One decoded atom plus the source annotations lowering added: the unit the
/// committed order places, the deal assigns to a warp, and the stream emits whole.
///
/// The wire counterpart is [`LeanAtom`]; this is that value after
/// [`annotate_atoms`] has resolved every operand's [`SourceClass`] and validated
/// every coefficient / immediate id.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SegAtom {
    /// A plain record: singleton coefficient semantics, wire-unchanged.
    Term(AnnotatedTerm),
    /// A group header plus its members. `core` is the header's recipe-bank id.
    Group {
        core: u16,
        has_c0: bool,
        has_c2: bool,
        members: Vec<SegMember>,
    },
}

/// What ONE grouped member costs (spec §4.5).
///
/// Deliberately NOT [`static_term_work`]: that function's base weights price
/// today's per-term coefficient FMA (`C0Linear` 2 = "one E4 multiply-add against
/// the coefficient"), and a grouped member no longer performs one — the group's
/// single core multiply, priced by [`atom_work`], replaced them all.
pub(crate) fn member_work(member: &SegMember) -> u64 {
    let body = match member.annotated.category {
        TermCategory::C0LinearE4 => 1,
        TermCategory::DualProductE4 => 8,
        // Ext groups only ever hold the two above (the continuation class table
        // has no other rows); anything else keeps its full term body.
        other => static_term_work_base(other),
    };
    let imm_surcharge = member.immediate_sides().unwrap_or(0);
    body + operand_work(&member.annotated) + imm_surcharge
}

/// The static work of one ATOM: [`static_term_work`] verbatim for a plain record,
/// and for a group its members plus two per active accumulator side for the core
/// multiply (spec §4.5).
pub(crate) fn atom_work(atom: &SegAtom) -> u64 {
    match atom {
        SegAtom::Term(term) => static_term_work(term),
        SegAtom::Group {
            members,
            has_c0,
            has_c2,
            ..
        } => {
            let base: u64 = members.iter().map(member_work).sum();
            base + 2 * (u64::from(*has_c0) + u64::from(*has_c2))
        }
    }
}

/// The Ext deal (spec §4.5): walk atoms in COMMITTED order and give each to the
/// currently least-loaded list, ties to the lowest list index.
///
/// Deterministic, whole-atom by construction (a list holds atom indices, and the
/// stream emits an atom's records contiguously), and degenerate to round-robin
/// when every cost is equal — which is what keeps the uniform-cost case, and R0's
/// own [`split_round_robin`], one behavior. The `max(1)` floor keeps a zero-cost
/// atom from being stacked without bound onto one list.
///
/// Balance: every atom lands on a list at or below the mean load at the time, so
/// the final maximum is at most the average plus one max-atom cost.
pub(crate) fn deal_atoms(costs: &[u64], k: usize) -> Vec<Vec<usize>> {
    let mut lists = vec![Vec::new(); k];
    let mut load = vec![0u64; k];
    for (atom, &cost) in costs.iter().enumerate() {
        let target = (0..k)
            .min_by_key(|&list| (load[list], list))
            .expect("k lists");
        lists[target].push(atom);
        load[target] += cost.max(1);
    }
    lists
}

/// How the stream emits one deal unit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SegUnitEmit {
    /// One whole atom's records, copied verbatim: `(first record, records)`.
    Atom { first: usize, span: usize },
    /// One chunk of a chopped group: a SYNTHESIZED header — the original's
    /// `word0` (class | core) and `word2` (flags) with the member count replaced
    /// and the reserved `word3` zero — followed by `members` member records
    /// copied verbatim from record `first_member`.
    GroupChunk {
        /// The original header's record index.
        header: usize,
        /// The chunk's first MEMBER record index.
        first_member: usize,
        /// The chunk's member count, at least one.
        members: usize,
    },
}

/// One unit the Ext deal places after [`chop_atoms`]: a whole atom, or one chunk
/// of a group too heavy for a `K`-way balance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SegDealUnit {
    /// The unit's static work: [`atom_work`] for a whole atom; for a chunk, its
    /// own members' [`member_work`] plus the core multiply, which every chunk
    /// repays in full.
    pub cost: u64,
    pub emit: SegUnitEmit,
}

/// The chop threshold's denominator: an atom heavier than `total / (4 K)` chops.
///
/// A quarter of a list's fair share bounds the deal's imbalance at
/// `max <= mean + max_unit <= 1.25 x mean` while capping the repaid cores at
/// `4 K` extra headers per program — both small against `total` for any program
/// heavy enough to matter.
const SEG_CHOP_DIVISOR: u64 = 4;

/// Chop the committed atoms into the Ext deal's units.
///
/// Any GROUP atom whose [`atom_work`] exceeds `total / (SEG_CHOP_DIVISOR * k)`
/// splits into `ceil(work / threshold)` even whole-member chunks — first chunks
/// take the remainder — clamped by AMORTIZATION: at most one chunk per
/// `2 * core_work` of member work, so the repaid cores never inflate a group's
/// work by more than half its members'. A chunk may hold a SINGLE member when
/// that member is heavy enough to carry its own header (a dual pair is the
/// corpus's worst deal spike, and a two-member floor would strand it whole);
/// the `N >= 2` rule is the ARTIFACT encoder's, and the dealt stream never
/// re-enters that codec — the kernel's member walk takes any `N >= 1`.
///
/// Every chunk header is a record the emitted stream must hold, so the chop
/// additionally spends a RECORD BUDGET — `record_capacity` minus the artifact's
/// own records — in committed order, degrading a group's chunk count to what the
/// remaining budget allows before dropping its chop entirely. A program already
/// at capacity chops nothing and lowers byte-identically to the unchopped deal;
/// the capacity is the INLINE descriptor's in both program families, so the two
/// families keep one stream.
///
/// Chunks keep the group's committed position and stay adjacent, so the deal's
/// cross-warp temporal alignment is untouched: the chop only refines the deal's
/// GRANULARITY, never its order. Value-exactness is field distributivity —
/// `core * (A + B) = core * A + core * B` holds exactly in the extension field,
/// so a chopped group accumulates the same value its whole form does.
pub(crate) fn chop_atoms(
    seg_atoms: &[SegAtom],
    atom_spans: &[(usize, usize)],
    k: usize,
    record_capacity: usize,
) -> Vec<SegDealUnit> {
    let total: u64 = seg_atoms.iter().map(atom_work).sum();
    let threshold = (total / (SEG_CHOP_DIVISOR * k as u64)).max(1);
    let records = atom_spans
        .last()
        .map(|&(first, span)| first + span)
        .unwrap_or(0);
    let mut budget = record_capacity.saturating_sub(records) as u64;
    let mut units = Vec::with_capacity(seg_atoms.len());
    for (atom, &(first, span)) in seg_atoms.iter().zip(atom_spans) {
        let cost = atom_work(atom);
        let whole = SegDealUnit {
            cost,
            emit: SegUnitEmit::Atom { first, span },
        };
        let SegAtom::Group {
            has_c0,
            has_c2,
            members,
            ..
        } = atom
        else {
            units.push(whole);
            continue;
        };
        let core_work = 2 * (u64::from(*has_c0) + u64::from(*has_c2));
        let member_total: u64 = members.iter().map(member_work).sum();
        let chunks = if cost > threshold {
            cost.div_ceil(threshold)
                .min(members.len() as u64)
                .min((member_total / (2 * core_work).max(1)).max(1))
                .min(1 + budget)
        } else {
            1
        };
        if chunks <= 1 {
            units.push(whole);
            continue;
        }
        budget -= chunks - 1;
        let chunks = chunks as usize;
        let base = members.len() / chunks;
        let extra = members.len() % chunks;
        let mut member = 0usize;
        for chunk in 0..chunks {
            let count = base + usize::from(chunk < extra);
            let cost: u64 = members[member..member + count]
                .iter()
                .map(member_work)
                .sum::<u64>()
                + core_work;
            units.push(SegDealUnit {
                cost,
                emit: SegUnitEmit::GroupChunk {
                    header: first,
                    first_member: first + 1 + member,
                    members: count,
                },
            });
            member += count;
        }
        debug_assert_eq!(member, members.len(), "every member lands in one chunk");
    }
    units
}

/// The `K`-split's balance, measured with [`atom_work`].
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) struct ListWorkStats {
    /// The busiest list — the block's critical path, since warps join at the
    /// epilogue.
    pub max_work: u64,
    /// Mean over the `k` lists. Zero-length lists count.
    pub mean_work: f64,
    /// `max_work / mean_work`, or `0.0` for a program with no work at all. One
    /// means perfectly balanced.
    pub max_over_mean: f64,
}

// ── Round binding and setup ──────────────────────────────────────────────────

/// Everything about one sumcheck round that a `K`-free artifact cannot carry.
pub(crate) struct BwdSegRoundBinding<'a> {
    /// Sumcheck round index. It is ALSO every window's target depth.
    pub round: u32,
    /// Logical rows this launch evaluates: one per thread, and the contribution
    /// half-stride.
    pub rows: usize,
    /// The round's address table, positionally the descriptor's slot array.
    /// Keyed by BACKING: two sources reading one matrix share a slot whatever
    /// their columns, and a source publishes through a slot of its own.
    pub slots: &'a [ResolvedAddrSlot],
    /// One entry per wire source, in source-slot order.
    pub sources: &'a [ResolvedSourceAddr],
    /// The main-layer claim point, as a HOST slice. It becomes
    /// [`BwdSegSetup::claim_point`] (the caller uploads it to the
    /// `ab_gkr_main_layer_claim_point` symbol, which is the ONE challenge
    /// authority) and bounds-checks the challenge slots the fold prologue reads.
    /// It is NEVER copied into the descriptor — the descriptor has no challenge
    /// pointer.
    pub claim_point: &'a [E4],
    /// Bank recipes, ALREADY EVALUATED in this round's challenge context, in
    /// recipe-index order. Reserved-EXCLUSIVE: lowering materializes `ONE` and
    /// `NEG_ONE` at the head of [`BwdSegSetup::coefficients`].
    pub coefficients: &'a [E4],
    /// The layer's `acc_c0` seed recipe, or `None`.
    ///
    /// A layer property whose VALUE is round-dependent (a recipe evaluated in
    /// this round's challenge context), which is why it arrives with
    /// [`Self::coefficients`] and resolves against the same payload. The lean
    /// artifact does not carry it: `LeanCoordinateArtifact` is the program plus
    /// the binding, and a seed is neither.
    pub c_init: Option<CoefficientRecipeId>,
    /// The grouped layer's immediate table, CANONICAL base-field values in
    /// `ImmediateId::banked` order (`immediates[id - 2]`).
    ///
    /// It arrives with the round binding for the same reason
    /// [`Self::coefficients`] does: [`LeanCoordinateArtifact`] carries the program
    /// plus its source binding, and the table is neither — it is a property of the
    /// LAYER the program was lowered from, which only the bridge that built both
    /// still holds. Unlike the coefficients it is round-INDEPENDENT (a BF scalar,
    /// not a challenge-evaluated recipe); lowering converts it to the kernel's
    /// in-memory form once, host-side. Empty for a layer with no groups, which is
    /// every R0 layer and every ungrouped Ext layer.
    pub immediates: &'a [u32],
    pub eq_low: *const E4,
    pub eq_sizes: GkrEqSizes,
    pub contributions: *mut E4,
    /// The contribution half-stride. One number wearing two hats with
    /// [`Self::rows`]; the descriptor carries ONE field, so lowering requires
    /// them equal rather than picking one.
    pub acc_size: u32,
    /// What the epilogue writes into [`Self::contributions`]:
    /// [`BWD_SEG_OUTPUT_ROWS`] (`2 * rows` per-row entries) or
    /// [`BWD_SEG_OUTPUT_PARTIALS`] (`2 * rows.div_ceil(32)` entries — one
    /// interleaved pair per 32-row tile, for the fused tail).
    ///
    /// The buffer must be sized for the shape requested: a partials-shaped buffer
    /// handed to a rows-shaped launch is an out-of-bounds write, which is why this
    /// travels WITH the pointer rather than being a launch-site argument.
    pub output: u32,
}

/// A lowered launch: the descriptor plus every payload the caller must upload.
pub(crate) struct BwdSegSetup {
    pub desc: BwdSegLaunchDesc,
    /// The RESERVED-INCLUSIVE coefficient payload `[ONE, NEG_ONE, recipes…]`,
    /// indexed raw by wire coefficient ids. Upload target is the mode's
    /// ([`CoeffMode`]).
    pub coefficients: Vec<E4>,
    /// The `ab_gkr_main_layer_claim_point` upload payload.
    pub claim_point: Vec<E4>,
    /// The immediate table in the kernel's IN-MEMORY base-field form — Montgomery
    /// representation, exactly the bytes a device load of a `bf` sees — converted
    /// once here from [`BwdSegRoundBinding::immediates`]' canonical values, because
    /// the eval loop must never pay a conversion per member. Indexed by
    /// `id - ImmediateId::RESERVED`.
    pub immediates: Vec<u32>,
    /// The reordered lean stream for [`ProgramMode::DevPtr`]; empty inline.
    pub program_words: Vec<u16>,
    pub work: ListWorkStats,
    /// Source slots NO TERM reads (`first_touch == usize::MAX` over the committed
    /// order), ascending. Host-side only — the descriptor keeps carrying every
    /// slot. This is the audit §7.3 "dead-slot pricing" discriminator column the
    /// footprint census emits; it is NOT the floor's skip criterion, because a
    /// foldable source no term projects is still read in full by the
    /// fold-and-publish pass — [`Self::source_endpoints`] is the field the floor
    /// prices from.
    pub dead_sources: Vec<u16>,
    /// Per source slot, how many of the two target-depth endpoint halves the
    /// launch's DRAM footprint spans: `0` (nothing touches the slot), `1` (every
    /// reference is a `C0Linear*` term — `seg_project` resolves ONLY the halves a
    /// projection needs, so an Endpoint0-only slot reads the low half alone), or
    /// `2` (a `C2Product*`/`DualProduct` reference, or the slot is foldable — the
    /// fold-and-publish pass reads both halves regardless of what the eval loop
    /// projects). The read-floor walk prices each backing at the MAX factor over
    /// the slots that share it; pricing every slot at `2` is the audit §7.3
    /// overstatement (331.8 B/row on the R0 headline cell).
    pub source_endpoints: Vec<u8>,
}

// ── Errors ───────────────────────────────────────────────────────────────────

/// Everything host lowering can reject. One variant per check.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BwdSegLowerError {
    /// `k` is zero, or past the warps a CUDA block can hold.
    InvalidListCount { k: usize },
    /// The round index does not fit the depth fields it also serves as.
    RoundTooDeep { round: u32 },
    /// An R0 program was lowered off round zero. R0 IS round zero: its kernel
    /// never folds, so a later round would silently read leaf zero only.
    R0RoundMismatch { round: u32 },
    /// R0 lowering DROPS the spine's scalar addends (they are already inside the
    /// materialized output the `acc_c0` shortcut reads), so seeding one would
    /// double-count it.
    R0CarriesCInit { id: CoefficientRecipeId },
    /// `c_init` names a coefficient id the payload cannot supply.
    InvalidCInit { index: u32 },
    /// The stream does not fit the by-value program array.
    ProgramOverflow { words: usize, cap: usize },
    /// The stream is longer than a `u16` list offset can address.
    ProgramOffsetOverflow { words: usize },
    /// The lean wire itself is malformed: length, reserved words, a class dead in
    /// the regime, or a source-arity rule.
    Codec(LeanCodecError),
    /// More live windows than the measured corpus maximum the descriptor is sized
    /// from.
    SourceWindowOverflow { windows: usize, cap: usize },
    /// The round bound a different number of windows than the artifact compiled.
    SourceWindowCountMismatch { compiled: usize, bound: usize },
    /// A window addresses more columns than its coordinate can reach.
    WindowColumnOverflow { window: u8, offset: usize },
    /// A procedural window named a kind the resolver does not serve.
    UnknownProceduralKind { window: u8, kind: u8 },
    /// A procedural window addresses more than one column: a procedural value
    /// comes from the ROW, so every column past the first would silently resolve
    /// to column zero.
    MultiColumnProceduralWindow { window: u8, columns: usize },
    /// A matrix-backed window has no read backing.
    MissingReadBacking { window: u8 },
    /// A procedural family was bound to a raw BASE matrix. Its materialization is
    /// E4 by construction, so a base backing is neither the synthesis nor the
    /// materialized form.
    ProceduralWindowWithMatrixRead { window: u8 },
    /// A backing pointer is null, or its stride is zero.
    NullWindowGeometry { window: u8 },
    /// A backing's column stride is not a whole power of two in its own element
    /// width, so a lane cannot index it: the kernel steps
    /// `column << log2_stride`. Every production stride is a power of two, so
    /// this is a resolver defect rather than a limitation.
    StrideNotPowerOfTwo { window: u8, stride_bytes: u32 },
    /// A backing's column stride is not a whole number of its own elements.
    WindowStrideMismatch {
        window: u8,
        is_e4: bool,
        stride_bytes: u32,
    },
    /// A window's target depth is not this round.
    ///
    /// `backing_depth > target_depth`, or a depth outside the D0..D3 range.
    InvalidDepths {
        window: u8,
        backing_depth: u8,
        target_depth: u8,
    },
    /// A catch-up distance the runtime factor bank cannot weight: it holds the
    /// depth-one pair and ONE depth-`fold_depth` table, nothing between.
    UnsupportedFoldDelta {
        window: u8,
        delta: u8,
        fold_depth: u8,
    },
    /// A caller-supplied publish backing on a window that does not publish —
    /// it would be silently ignored.
    UnexpectedPublishBacking { window: u8 },
    /// A caller-supplied publish backing AND a planned parity region for the
    /// same window: the plan was built from different windows than the
    /// lowering was handed.
    AmbiguousPublishBacking { window: u8 },
    /// An explicit publish backing that is not E4, or whose stride is narrower
    /// than the round's per-column extent (`2 * rows * 16`) — consecutive
    /// columns would overwrite each other.
    ExplicitPublishGeometry {
        window: u8,
        is_e4: bool,
        stride_bytes: u32,
    },
    /// A read is shorter than the PAIR total the round needs: both endpoint
    /// halves, each consuming its own `2^delta` inputs.
    ReadSpanOverflow { window: u8, needed: u32, have: u32 },
    /// The plan's stride is not `2 * rows * 16` for the rows this round claims.
    PublishStrideMismatch {
        round: u8,
        expected: usize,
        actual: usize,
    },
    /// The plan does not cover this round.
    PlanMissingRound { round: u8, rounds: usize },
    /// A round's window and column slices disagree.
    PlanShapeMismatch {
        round: usize,
        windows: usize,
        entries: usize,
    },
    /// The three per-round slices have different lengths.
    PlanRoundCountMismatch {
        windows: usize,
        columns: usize,
        rows: usize,
    },
    /// A window the policy publishes has no region in the plan.
    PlanMissingPublishRegion { window: u8 },
    /// A window the policy does NOT publish has a region in the plan.
    PlanPublishRegionUnused { window: u8 },
    /// The plan's byte arithmetic overflowed.
    PublishScratchOverflow { round: usize },
    /// A parity buffer the plan needs was not allocated.
    NullParityBase { parity: usize },
    /// A chain read does not point at the previous round's published region for
    /// this window — the parity rule, enforced rather than assumed.
    ChainReadNotPriorPublish { window: u8 },
    /// A RAW source at nonzero depth: a base-field read backing, or a procedural
    /// window with no read backing at all.
    ///
    /// A value at depth `k > 0` is the output of `k` folds, and a fold weights
    /// with E4 challenges and produces E4 — so only an E4 backing can carry a
    /// nonzero depth. A base matrix is never folded in place and a procedural
    /// source is row-synthesized at depth zero, so a nonzero depth on either
    /// shortens the catch-up over data that was never folded.
    BaseReadAtFoldedDepth { window: u8, backing_depth: u8 },
    /// A window the PREVIOUS round published was bound to a raw (base-field or
    /// procedural) source at this round. Its folded values are in the scratch
    /// region; refolding the raw source reads data the chain has moved past.
    RawReadOverPriorPublish { window: u8 },
    /// A publish region overlaps a read range or another publish region.
    UnsafePublishAlias { window: u8, other: u8 },
    /// A read range lies inside the parity buffer this round publishes into.
    ReadAliasesPublishBuffer { window: u8 },
    /// The two parity buffers overlap, so ping-pong would read what the prologue
    /// is writing.
    ParityBuffersAlias,
    /// More sources than the descriptor's table can hold.
    SourceOverflow { sources: usize, cap: usize },
    /// A source names a window the binding does not have.
    SourceWindowOutOfRange { source: usize, window: u8 },
    /// A source names a column past its window's addressable span.
    SourceColumnOutOfWindow {
        source: usize,
        window: u8,
        column: u16,
    },
    /// A wire record names a slot past the source table.
    SourceSlotOutOfRange { term: usize, slot: u16 },
    /// A term header names a coefficient id past the payload. The device indexes
    /// the bank with no bound of its own.
    CoefficientIndexPastBank { index: usize, entries: usize },
    /// More coefficients than the selected loader holds.
    CoefficientBankOverflow { coefficients: usize, cap: usize },
    /// The layer's immediate table is longer than one coordinate may carry
    /// (`LEAN_MAX_IMMEDIATES`, spec §4.5). The descriptor's own inline capacity
    /// mirror-asserts equal to it, so one bound serves both.
    ImmediateTableOverflow { len: usize },
    /// A group MEMBER's coefficient field — an immediate id, not a recipe id
    /// (spec §4.4) — addresses neither literal nor a table entry. `record` is the
    /// member's RECORD index in the word stream, headers included.
    ImmediateOutOfRange { record: usize, id: u16 },
    /// The claim point does not reach the challenge the deepest catch-up needs.
    ClaimPointTooShort { round: u8, entries: usize },
    /// The row count is zero, or past what the span arithmetic can express.
    RowsOutOfRange { rows: usize },
    /// `acc_size` is not the row count.
    AccSizeRowsMismatch { rows: usize, acc_size: u32 },
    /// A pointer the kernel dereferences unconditionally is null.
    NullRuntimePointer { what: &'static str },
}

impl From<LeanCodecError> for BwdSegLowerError {
    fn from(error: LeanCodecError) -> Self {
        BwdSegLowerError::Codec(error)
    }
}

// ── The assignment matrix ────────────────────────────────────────────────────

/// The per-`(source, round)` class and whether the prologue publishes for it.
///
/// The complete matrix, over `(origin, catch-up delta, D2 policy)`:
///
/// ```text
/// (BF,         d0, either)      -> BfDirect          no publish
/// (BF,         d1, either)      -> BfInlineD1        no publish
/// (BF,         d2, Inline)      -> BfInlineD2        no publish
/// (BF,         d2, Materialize) -> E4Direct          PUBLISH (depth-2 4xBF->E4 pyramid)
/// (BF,         d3, either)      -> E4Direct          PUBLISH (depth-3 pyramid)
/// (E4,         d0, either)      -> E4Direct          no publish
/// (E4,        d>=1, either)     -> E4Direct          PUBLISH (one chain step)
/// (procedural, d<3, either)     -> ProceduralInline  no publish
/// (procedural, d>=3, either)    -> E4Direct          PUBLISH (synthesize, then chain)
/// ```
///
/// `delta` is assumed already validated into `0..=BWD_COEFF_MAX_FOLD_DEPTH`.
/// Publishing is per WINDOW (every source of a window shares its origin and
/// depth), and it is what the scratch plan's regions and the descriptor's fold
/// list are both derived from.
pub(crate) fn assign_class(origin: SourceOrigin, delta: u8, d2: D2Policy) -> (SourceClass, bool) {
    match (origin, delta) {
        (SourceOrigin::Procedural, delta) if delta < BWD_COEFF_PUBLISH_TARGET_DEPTH => {
            (SourceClass::ProceduralInline, false)
        }
        (SourceOrigin::Procedural, _) => (SourceClass::E4Direct, true),
        (SourceOrigin::Bf, 0) => (SourceClass::BfDirect, false),
        (SourceOrigin::Bf, 1) => (SourceClass::BfInlineD1, false),
        (SourceOrigin::Bf, 2) => match d2 {
            D2Policy::Inline => (SourceClass::BfInlineD2, false),
            D2Policy::Materialize => (SourceClass::E4Direct, true),
        },
        (SourceOrigin::Bf, _) => (SourceClass::E4Direct, true),
        (SourceOrigin::E4, 0) => (SourceClass::E4Direct, false),
        (SourceOrigin::E4, _) => (SourceClass::E4Direct, true),
    }
}

// ── Lowering ─────────────────────────────────────────────────────────────────

/// Fill every field both descriptor families share.
///
/// A macro rather than a function: the two structs are field-for-field identical
/// over this set, so a field added to one and not the other stops compiling here.
macro_rules! fill_seg_desc {
    ($desc:expr, $body:expr) => {{
        let desc = &mut *$desc;
        let body = &$body;
        desc.list_offset[..body.list_offset.len()].copy_from_slice(&body.list_offset);
        desc.k = body.k;
        desc.record_count = body.record_count;
        desc.num_sources = body.num_sources;
        desc.num_foldable = body.num_foldable;
        desc.num_immediates = body.num_immediates;
        desc.fold_source[..body.fold_source.len()].copy_from_slice(&body.fold_source);
        // Dead source records carry the ABSENT lanes rather than zeros, which
        // would name slot 0 column 0 — a live address.
        for (index, record) in desc.source.iter_mut().enumerate() {
            *record = body
                .sources
                .get(index)
                .copied()
                .unwrap_or_else(BwdSegSourceRecord::default);
        }
        // Dead slots carry the ABSENT procedural kind rather than the zeroed
        // `0`, which is a LIVE kind.
        for (index, entry) in desc.slot.iter_mut().enumerate() {
            *entry = body
                .slots
                .get(index)
                .copied()
                .unwrap_or_else(BwdSegAddrSlot::default);
        }
        desc.c_init_coeff = body.c_init_coeff;
        desc.immediates[..body.immediates.len()].copy_from_slice(&body.immediates);
        desc.eq_low = body.eq_low;
        desc.contributions = body.contributions;
        desc.eq_sizes = body.eq_sizes;
        desc.n_coefficients = body.n_coefficients;
        desc.logical_rows = body.logical_rows;
        desc.output = body.output;
    }};
}

/// A zero-initialized `Box<T>`.
///
/// # Safety
///
/// The all-zero bit pattern must be a valid `T`.
pub(crate) unsafe fn zeroed_box<T>() -> Box<T> {
    let layout = std::alloc::Layout::new::<T>();
    let ptr = std::alloc::alloc_zeroed(layout) as *mut T;
    if ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    Box::from_raw(ptr)
}

/// What one window resolved to at this round.
struct LoweredSource {
    record: BwdSegSourceRecord,
    class: SourceClass,
    publishes: bool,
}

/// The pieces both descriptor families carry, computed once.
struct SegDescBody {
    list_offset: Vec<u16>,
    k: u16,
    record_count: u16,
    num_sources: u16,
    num_foldable: u16,
    num_immediates: u16,
    fold_source: Vec<u16>,
    sources: Vec<BwdSegSourceRecord>,
    slots: Vec<BwdSegAddrSlot>,
    c_init_coeff: u32,
    /// The immediate table in the kernel's in-memory (Montgomery) form, already
    /// capped by the wire validator — see [`BwdSegSetup::immediates`].
    immediates: Vec<u32>,
    eq_low: *const E4,
    contributions: *mut E4,
    eq_sizes: GkrEqSizes,
    n_coefficients: u32,
    logical_rows: u32,
    output: u32,
}

/// Build the complete launch setup for one `(artifact, round)` pair.
///
/// `k` is the number of per-warp term lists; `d2` the base-field depth-two
/// policy; `prog` and `coeff` select the program and coefficient-loader
/// families. Everything the caller must still do is in [`BwdSegSetup`]: upload
/// the coefficient payload, upload the claim point, and (in
/// [`ProgramMode::DevPtr`]) upload the stream and patch the pointer into its host
/// copy of the descriptor.
pub(crate) fn lower_bwd_seg(
    artifact: &LeanCoordinateArtifact,
    binding: &BwdSegRoundBinding<'_>,
    scratch: &ResolvedPublishScratch,
    k: usize,
    d2: D2Policy,
    prog: ProgramMode,
    coeff: CoeffMode,
) -> Result<BwdSegSetup, BwdSegLowerError> {
    if k == 0 || k > BWD_SEG_MAX_K {
        return Err(BwdSegLowerError::InvalidListCount { k });
    }
    let round = u8::try_from(binding.round).map_err(|_| BwdSegLowerError::RoundTooDeep {
        round: binding.round,
    })?;
    let regime = artifact.regime.regime();
    // R0 IS round zero: its kernel is the `FOLD_DEPTH = 0` specialization.
    if regime == BwdRegime::R0 && round != 0 {
        return Err(BwdSegLowerError::R0RoundMismatch {
            round: binding.round,
        });
    }
    let fold_depth = bwd_coeff_fold_depth(round);

    // The reserved literals are MATERIALIZED at the payload head (RR ruling
    // 2026-07-27), so the kernel resolves every coefficient with one uniform
    // `bank[coeff_idx]` load: no fast path, no offset subtraction.
    let mut coefficients =
        Vec::with_capacity(CoefficientRecipeId::RESERVED as usize + binding.coefficients.len());
    coefficients.push(
        CoefficientRecipeId::ONE
            .literal()
            .expect("ONE is a reserved literal"),
    );
    coefficients.push(
        CoefficientRecipeId::NEG_ONE
            .literal()
            .expect("NEG_ONE is a reserved literal"),
    );
    coefficients.extend_from_slice(binding.coefficients);
    let bank_cap = match coeff {
        CoeffMode::Constant => BWD_SEG_CONST_BANK,
        // A device buffer is unbounded; the wire's thirteen coefficient bits are
        // not.
        CoeffMode::DevPtr => MAX_COEFFICIENT_ENCODINGS,
    };
    if coefficients.len() > bank_cap {
        return Err(BwdSegLowerError::CoefficientBankOverflow {
            coefficients: coefficients.len(),
            cap: bank_cap,
        });
    }

    let c_init_coeff = match binding.c_init {
        None => BWD_SEG_C_INIT_NONE,
        Some(id) if regime == BwdRegime::R0 => return Err(BwdSegLowerError::R0CarriesCInit { id }),
        // The id travels; the DEVICE resolves it, through the same bank accessor
        // the eval loop uses for every other coefficient. The bounds check stays
        // here — a release kernel has no error channel, and an id past the payload
        // would be an out-of-bounds constant read — and it is the same indexing the
        // CPU oracle applies (`interp.rs`'s `coefficient(layer, id, resolver)`): a
        // reserved literal and a banked recipe are one lookup.
        //
        // Resolving to limbs here is what this used to do, and it cannot survive
        // production: the bank is filled on the device from challenges squeezed
        // there, so at descriptor-build time the host has no value to write.
        Some(id) => {
            let index = usize::try_from(id.0).ok();
            index
                .filter(|index| *index < coefficients.len())
                .ok_or(BwdSegLowerError::InvalidCInit { index: id.0 })?;
            id.0
        }
    };

    // Bounded so that BOTH derived quantities stay in `u32`: the deepest pair
    // total (`2 * rows * 2^3` elements) and the publish stride
    // (`2 * rows * 16` bytes).
    let bound_by = 2 * (1usize << BWD_COEFF_MAX_FOLD_DEPTH).max(E4_COLUMN_BYTES as usize);
    if binding.rows == 0
        || binding
            .rows
            .checked_mul(bound_by)
            .and_then(|value| u32::try_from(value).ok())
            .is_none()
    {
        return Err(BwdSegLowerError::RowsOutOfRange { rows: binding.rows });
    }
    let logical_rows = binding.rows as u32;
    if binding.acc_size != logical_rows {
        return Err(BwdSegLowerError::AccSizeRowsMismatch {
            rows: binding.rows,
            acc_size: binding.acc_size,
        });
    }
    // The deepest catch-up at round `r` weights with the challenges of rounds
    // `[r - delta, r)`, so the claim point has to reach index `r - 1`.
    if binding.claim_point.len() < usize::from(round) {
        return Err(BwdSegLowerError::ClaimPointTooShort {
            round,
            entries: binding.claim_point.len(),
        });
    }
    if binding.eq_low.is_null() {
        return Err(BwdSegLowerError::NullRuntimePointer { what: "eq_low" });
    }
    if binding.contributions.is_null() {
        return Err(BwdSegLowerError::NullRuntimePointer {
            what: "contributions",
        });
    }

    // ── The wire ─────────────────────────────────────────────────────────────
    // Decoded as ATOMS, not as a flat record list: a group is one unit for the
    // deal (spec §4.5), and its header's member count is what makes the Ext walk
    // self-delimiting. `atom_spans[i]` is atom `i`'s `(first record, records)`,
    // the whole-atom word span the stream copies — or, for a group
    // [`chop_atoms`] splits, the span its chunk headers and member copies are
    // addressed within.
    let atoms = decode_atoms(&artifact.program, regime)?;
    let mut atom_spans = Vec::with_capacity(atoms.len());
    let mut record_count = 0usize;
    for atom in &atoms {
        let span = match atom {
            LeanAtom::Term(_) => 1,
            LeanAtom::Group { members, .. } => 1 + members.len(),
        };
        atom_spans.push((record_count, span));
        record_count += span;
    }
    // R0 is atoms-are-records by construction (no headers exist there), which is
    // what keeps its `split_round_robin` over POSITIONS and the shared whole-atom
    // emission below the same bytes.
    debug_assert!(regime != BwdRegime::R0 || record_count == atoms.len());
    let words = artifact.program.words.len();
    if prog == ProgramMode::Inline && words > LEAN_DESCRIPTOR_PROGRAM_WORDS {
        return Err(BwdSegLowerError::ProgramOverflow {
            words,
            cap: LEAN_DESCRIPTOR_PROGRAM_WORDS,
        });
    }
    if u16::try_from(words).is_err() || u16::try_from(record_count).is_err() {
        return Err(BwdSegLowerError::ProgramOffsetOverflow { words });
    }

    // ── The address table ────────────────────────────────────────────────────
    // A slot is a BACKING, so the count is bounded by how many matrices and fold
    // buffers a layer touches — never by how the artifact groups its columns.
    // Scratch-backed destinations are interned below and share the same budget.
    if binding.slots.len() > BWD_SEG_ADDR_SLOTS {
        return Err(BwdSegLowerError::SourceWindowOverflow {
            windows: binding.slots.len(),
            cap: BWD_SEG_ADDR_SLOTS,
        });
    }
    if binding.sources.len() != artifact.binding.source_slots.len() {
        return Err(BwdSegLowerError::SourceWindowCountMismatch {
            compiled: artifact.binding.source_slots.len(),
            bound: binding.sources.len(),
        });
    }
    let columns: Vec<usize> = binding.slots.iter().map(|slot| slot.columns).collect();
    for (index, count) in columns.iter().enumerate() {
        if *count == 0 || *count > SOURCE_WINDOW_COLUMNS {
            return Err(BwdSegLowerError::WindowColumnOverflow {
                window: index as u8,
                offset: *count,
            });
        }
    }

    let rounds = scratch.plan.per_round.len();
    let layout = scratch
        .plan
        .per_round
        .get(usize::from(round))
        .ok_or(BwdSegLowerError::PlanMissingRound { round, rounds })?;
    // As above: a plan with no bytes reserves nothing for anyone, so its per-round
    // entry count carries no claim about this round's slot table. When it DOES
    // reserve, it must cover every slot a source READS through — those are the
    // keys `plan_publish_scratch` assigns regions to. Destination slots are not
    // keys, so a plan shorter than the whole table is normal.
    let read_slots = binding
        .sources
        .iter()
        .map(|addr| addr.read_slot + 1)
        .max()
        .unwrap_or(0);
    if layout.bytes != 0 && layout.window_base.len() < read_slots {
        return Err(BwdSegLowerError::PlanShapeMismatch {
            round: usize::from(round),
            windows: read_slots,
            entries: layout.window_base.len(),
        });
    }
    // The PREVIOUS round's shape matters too, and its failure is silent rather
    // than loud: `chain_read_column` answers `None` for a slot index the prior
    // layout does not reach, which is indistinguishable from "that slot published
    // nothing" — so a plan whose round `r - 1` was built for a different
    // (narrower) binding would disable the chain check instead of failing it.
    //
    // Only checked when the scratch path is LIVE. A caller that backs every
    // destination explicitly (production) plans nothing, and its slot tables are
    // per-round facts whose lengths legitimately differ round to round — the
    // read side interns whatever backings that round reads. Comparing those
    // lengths would reject a correct binding.
    let scratch_is_live = scratch.plan.bytes_per_parity.iter().any(|&bytes| bytes != 0);
    if scratch_is_live {
        if let Some(previous) = usize::from(round)
            .checked_sub(1)
            .and_then(|index| scratch.plan.per_round.get(index))
        {
            let entries = previous.window_base.len();
            if entries != 0 && entries < read_slots {
                return Err(BwdSegLowerError::PlanShapeMismatch {
                    round: usize::from(round) - 1,
                    windows: read_slots,
                    entries,
                });
            }
        }
    }
    let expected_stride = binding.rows * 2 * E4_COLUMN_BYTES as usize;
    if layout.column_stride_bytes != expected_stride {
        return Err(BwdSegLowerError::PublishStrideMismatch {
            round,
            expected: expected_stride,
            actual: layout.column_stride_bytes,
        });
    }
    // In `u32` because the row guard above bounds `2 * rows * 16`.
    let publish_stride = expected_stride as u32;
    let write_parity = usize::from(round & 1);
    let read_parity = write_parity ^ 1;
    // A parity buffer with bytes must exist. `layout.bytes` is checked as well as
    // the plan's per-parity total so that a hand-built plan whose totals
    // under-report a round still cannot get an offset computed off a null base.
    for parity in [write_parity, read_parity] {
        let needed = scratch.plan.bytes_per_parity[parity] > 0
            || (parity == write_parity && layout.bytes > 0);
        if needed && scratch.parity_base[parity].is_null() {
            return Err(BwdSegLowerError::NullParityBase { parity });
        }
    }

    // The table the descriptor carries: one entry per supplied slot, plus one per
    // scratch-backed destination interned while lowering the sources.
    let mut table: Vec<BwdSegAddrSlot> = Vec::with_capacity(binding.slots.len());
    for (index, slot) in binding.slots.iter().enumerate() {
        table.push(lower_slot(index as u8, slot)?);
    }

    // ── Sources ──────────────────────────────────────────────────────────────
    if binding.sources.len() > BWD_SEG_MAX_SOURCES {
        return Err(BwdSegLowerError::SourceOverflow {
            sources: binding.sources.len(),
            cap: BWD_SEG_MAX_SOURCES,
        });
    }
    // Scratch-backed destinations, interned by the READ slot they belong to. This
    // is the publish-scratch plan's own keying (`layout.window_base[i]` is slot
    // `i`'s region), so a caller that supplies no explicit destination gets
    // exactly the region the plan sized for it.
    let mut scratch_slot: Vec<Option<usize>> = vec![None; binding.slots.len()];
    let mut slot_columns: Vec<usize> = columns.clone();
    let mut sources = Vec::with_capacity(binding.sources.len());
    let mut source_classes = Vec::with_capacity(binding.sources.len());
    let mut publishing = Vec::with_capacity(binding.sources.len());
    for (source, addr) in binding.sources.iter().enumerate() {
        let lowered = lower_source(
            source,
            addr,
            binding,
            &mut table,
            &mut slot_columns,
            &mut scratch_slot,
            scratch,
            layout,
            publish_stride,
            round,
            fold_depth,
            d2,
        )?;
        sources.push(lowered.record);
        source_classes.push(lowered.class);
        publishing.push(lowered.publishes);
    }
    // Per-slot alias inputs, read off the RECORDS: a slot is a read source with
    // the widest extent any source demands of it, and a publish target if any
    // source names it on the destination lane.
    let mut slot_read_extent = vec![0usize; table.len()];
    let mut slot_publishes = vec![false; table.len()];
    for record in &sources {
        let read_slot = bwd_seg_lane_slot(record.src);
        let width = if table[read_slot].origin == BWD_COEFF_ORIGIN_READ_EXT {
            E4_COLUMN_BYTES
        } else {
            BF_COLUMN_BYTES
        } as usize;
        let extent = 2 * binding.rows * (1usize << record.delta) * width;
        slot_read_extent[read_slot] = slot_read_extent[read_slot].max(extent);
        if record.cache != BWD_SEG_ADDR_NONE {
            slot_publishes[bwd_seg_lane_slot(record.cache)] = true;
        }
    }
    check_alias(
        &table,
        &slot_columns,
        &slot_read_extent,
        &slot_publishes,
        scratch,
        write_parity,
        read_parity,
        binding.rows,
    )?;

    // ── The wire, validated and annotated against those sources ──────────────
    let seg_atoms = annotate_atoms(
        &atoms,
        regime,
        &source_classes,
        coefficients.len(),
        binding.immediates.len(),
    )?;
    // The flat TERM view of the annotated atoms, in committed order: headers drop
    // out (they carry no sources and no category), members splice in place. Every
    // per-source walk below is a statement about terms, so this is the view they
    // want — and dropping the headers is exactly why the floor is unchanged by
    // grouping.
    let mut terms: Vec<(&LeanTerm, AnnotatedTerm)> = Vec::with_capacity(artifact.order.len());
    for (atom, annotated) in atoms.iter().zip(&seg_atoms) {
        match (atom, annotated) {
            (LeanAtom::Term(record), SegAtom::Term(term)) => terms.push((record, *term)),
            (
                LeanAtom::Group { members, .. },
                SegAtom::Group {
                    members: annotated, ..
                },
            ) => terms.extend(
                members
                    .iter()
                    .zip(annotated)
                    .map(|(record, member)| (record, member.annotated)),
            ),
            // `annotate_atoms` maps each atom to its own shape, in order.
            _ => unreachable!("the annotated atom shape follows the decoded one"),
        }
    }

    // ── The fold list (§7) ───────────────────────────────────────────────────
    // The sources the eval loop touches EARLIEST are folded LAST, so they are the
    // warmest in L1 when eval starts. First touch is taken over the COMMITTED
    // order, which is the global order the `K` warps advance through together.
    let mut first_touch = vec![usize::MAX; sources.len()];
    for (position, (term, _)) in terms.iter().enumerate() {
        for slot in [term.source_a, term.source_b] {
            if slot == SOURCE_NONE {
                continue;
            }
            let entry = &mut first_touch[usize::from(slot)];
            *entry = (*entry).min(position);
        }
    }
    let dead_sources: Vec<u16> = (0..sources.len() as u16)
        .filter(|&source| first_touch[usize::from(source)] == usize::MAX)
        .collect();
    let mut fold_source: Vec<u16> = (0..sources.len())
        .filter(|&source| publishing[source])
        .map(|source| source as u16)
        .collect();
    // Descending first touch; ties by ascending slot, so the order is total. A
    // source no term reads (`usize::MAX`) sorts first — it is dead weight either
    // way.
    fold_source
        .sort_by_key(|&source| (std::cmp::Reverse(first_touch[usize::from(source)]), source));
    let num_foldable = fold_source.len() as u16;

    // ── Endpoint spans (see `BwdSegSetup::source_endpoints`) ─────────────────
    // `Move*` terms cannot decode from the wire (no lean class row); if one ever
    // did, pricing it as both halves errs on the side the floor must never
    // cross.
    let mut source_endpoints = vec![0u8; sources.len()];
    for (record, term) in terms.iter() {
        let endpoint0_only = matches!(
            term.category,
            TermCategory::C0LinearBf | TermCategory::C0LinearE4
        );
        for slot in [record.source_a, record.source_b] {
            if slot == SOURCE_NONE {
                continue;
            }
            let entry = &mut source_endpoints[usize::from(slot)];
            *entry = (*entry).max(if endpoint0_only { 1 } else { 2 });
        }
    }
    for &source in &fold_source {
        source_endpoints[usize::from(source)] = 2;
    }

    // ── The K-split ──────────────────────────────────────────────────────────
    // Both regimes split UNITS and both emit whole unit spans; only the RULE
    // differs. R0 keeps `split_round_robin` over positions verbatim — its atoms
    // are its records, no group exists to chop, so the emitted bytes are exactly
    // the pre-group stream's. Ext first chops over-heavy groups into whole-member
    // chunks (the deal is whole-unit, so an unchopped dominant group would pin one
    // list at its own cost), then takes the least-loaded deal (spec §4.5) over the
    // units, which is what keeps a group — or a chunk — off a `list_offset`
    // boundary.
    let units: Vec<SegDealUnit> = if regime == BwdRegime::R0 {
        seg_atoms
            .iter()
            .zip(&atom_spans)
            .map(|(atom, &(first, span))| SegDealUnit {
                cost: atom_work(atom),
                emit: SegUnitEmit::Atom { first, span },
            })
            .collect()
    } else {
        chop_atoms(
            &seg_atoms,
            &atom_spans,
            k,
            LEAN_DESCRIPTOR_PROGRAM_WORDS / LEAN_WORDS_PER_TERM,
        )
    };
    let costs: Vec<u64> = units.iter().map(|unit| unit.cost).collect();
    let lists = if regime == BwdRegime::R0 {
        let positions: Vec<usize> = (0..units.len()).collect();
        split_round_robin(&positions, k)
    } else {
        deal_atoms(&costs, k)
    };
    let mut stream: Vec<u16> = Vec::with_capacity(artifact.program.words.len());
    let mut list_offset = vec![0u16; k + 1];
    for (list, list_units) in lists.iter().enumerate() {
        list_offset[list] = u16::try_from(stream.len())
            .map_err(|_| BwdSegLowerError::ProgramOffsetOverflow { words })?;
        for &unit in list_units {
            match units[unit].emit {
                // The WHOLE unit: a header and its members are contiguous on the
                // wire and stay contiguous in the list, so no group straddles a
                // boundary.
                SegUnitEmit::Atom { first, span } => {
                    let at = first * LEAN_WORDS_PER_TERM;
                    stream.extend_from_slice(
                        &artifact.program.words[at..at + span * LEAN_WORDS_PER_TERM],
                    );
                }
                // One chunk of a chopped group: the original header with the member
                // count replaced (`word0` is class | core, `word2` the flags,
                // `word3` the canonical zero), then the chunk's members verbatim —
                // contiguous for the same reason.
                SegUnitEmit::GroupChunk {
                    header,
                    first_member,
                    members,
                } => {
                    let at = header * LEAN_WORDS_PER_TERM;
                    stream.push(artifact.program.words[at]);
                    stream.push(members as u16);
                    stream.push(artifact.program.words[at + 2]);
                    stream.push(0);
                    let at = first_member * LEAN_WORDS_PER_TERM;
                    stream.extend_from_slice(
                        &artifact.program.words[at..at + members * LEAN_WORDS_PER_TERM],
                    );
                }
            }
        }
    }
    list_offset[k] = u16::try_from(stream.len())
        .map_err(|_| BwdSegLowerError::ProgramOffsetOverflow { words })?;
    // The chop only ever ADDS records, so the inline capacity re-checks the
    // EMITTED stream — the cap is a statement about what the descriptor carries
    // and the kernel walks, not about the artifact. The record count follows the
    // same authority.
    if prog == ProgramMode::Inline && stream.len() > LEAN_DESCRIPTOR_PROGRAM_WORDS {
        return Err(BwdSegLowerError::ProgramOverflow {
            words: stream.len(),
            cap: LEAN_DESCRIPTOR_PROGRAM_WORDS,
        });
    }
    let record_count = stream.len() / LEAN_WORDS_PER_TERM;

    let work = list_work_stats(&lists, &costs);

    // Canonical BF -> the kernel's in-memory (Montgomery) form, ONCE, host-side:
    // the eval loop reads `immediates[id - 2]` straight into a `bf` register. The
    // table rides the descriptor BY VALUE in both program families, so it is
    // computed before the descriptor rather than alongside the setup's other
    // payloads.
    let immediates: Vec<u32> = binding
        .immediates
        .iter()
        .map(|&value| BF::from_u32_with_reduction(value).as_u32_raw_repr_reduced())
        .collect();

    // ── The descriptor ───────────────────────────────────────────────────────
    let body = SegDescBody {
        list_offset,
        k: k as u16,
        // RECORDS, not terms: the field's contract is
        // `list_offset[k] == LEAN_WORDS_PER_TERM * record_count`, and a group
        // header is a record of its own (spec §4.5). Equal to the term count for
        // every header-free program, which is every R0 and every ungrouped Ext one.
        record_count: record_count as u16,
        num_sources: sources.len() as u16,
        num_foldable,
        num_immediates: immediates.len() as u16,
        fold_source,
        sources,
        slots: table,
        c_init_coeff,
        immediates: immediates.clone(),
        eq_low: binding.eq_low,
        contributions: binding.contributions,
        eq_sizes: binding.eq_sizes,
        n_coefficients: coefficients.len() as u32,
        logical_rows,
        output: binding.output,
    };

    let (desc, program_words) = match prog {
        ProgramMode::Inline => {
            // SAFETY: `BwdSegDesc` is `repr(C)` plain data — arrays of `u16` /
            // `u32`, `repr(C)` plain-data structs and raw pointers — so the
            // all-zero bit pattern is a valid value (null pointers, empty
            // program). Allocating it zeroed rather than moving an `empty()`
            // through the stack is what makes the 26 KB by-value launch
            // parameter's INTERIOR PADDING deterministic: the four bytes before
            // `window` are never read by the kernel but are copied by the launch.
            let mut desc: Box<BwdSegDesc> = unsafe { zeroed_box() };
            fill_seg_desc!(desc, body);
            desc.program[..stream.len()].copy_from_slice(&stream);
            (BwdSegLaunchDesc::Inline(desc), Vec::new())
        }
        ProgramMode::DevPtr => {
            // SAFETY: as above; the twin is the same plain data with the array
            // replaced by a null pointer.
            let mut desc: Box<BwdSegProgPtrDesc> = unsafe { zeroed_box() };
            fill_seg_desc!(desc, body);
            // `program` stays NULL: the caller uploads `program_words` and
            // patches the pointer into its own host copy before launch.
            desc.program_words = stream.len() as u32;
            (BwdSegLaunchDesc::ProgPtr(desc), stream)
        }
    };

    Ok(BwdSegSetup {
        desc,
        coefficients,
        claim_point: binding.claim_point.to_vec(),
        immediates,
        program_words,
        work,
        dead_sources,
        source_endpoints,
    })
}

/// Resolve ONE address slot into its descriptor entry.
///
/// A slot is pure addressing plus the two facts that belong to a BACKING rather
/// than to a source, so this checks only geometry: the base must be a legal
/// column, the far end of the addressed span must still be representable, and a
/// procedural slot must not also claim a matrix.
fn lower_slot(index: u8, slot: &ResolvedAddrSlot) -> Result<BwdSegAddrSlot, BwdSegLowerError> {
    if let Some(kind) = slot.procedural_kind {
        if usize::from(kind) >= BWD_COEFF_PROCEDURAL_KINDS {
            return Err(BwdSegLowerError::UnknownProceduralKind {
                window: index,
                kind,
            });
        }
        // A procedural FAMILY reading an E4 backing is legal and common: once a
        // round materializes it, the values live in that backing and the slot is
        // an ordinary E4 read. What is not legal is a procedural family reading a
        // BASE matrix — nothing materializes into base field.
        match slot.base {
            Some(column) if !column.is_e4 => {
                return Err(BwdSegLowerError::ProceduralWindowWithMatrixRead { window: index })
            }
            // A procedural value comes from the row, so the column coordinate is
            // meaningless and a multi-column synthesizing slot is a lowering bug.
            None if slot.columns > 1 => {
                return Err(BwdSegLowerError::MultiColumnProceduralWindow {
                    window: index,
                    columns: slot.columns,
                })
            }
            _ => {}
        }
    }
    let Some(column) = slot.base else {
        return Ok(BwdSegAddrSlot {
            base: std::ptr::null(),
            log2_stride: 0,
            origin: BWD_COEFF_ORIGIN_PROCEDURAL,
            procedural_kind: slot.procedural_kind.ok_or(
                BwdSegLowerError::MissingReadBacking { window: index },
            )?,
            reserved: [0; 5],
        });
    };
    if slot.deferred_base {
        // A deferred slot carries an OFFSET, not an address: a non-null base
        // here would mean the caller resolved it after all and the patch would
        // then double-add it.
        if !column.matrix_base.is_null() {
            return Err(BwdSegLowerError::NullWindowGeometry { window: index });
        }
    } else {
        check_column_geometry(index, &column)?;
    }
    let element = if column.is_e4 {
        E4_COLUMN_BYTES
    } else {
        BF_COLUMN_BYTES
    };
    // The kernel steps `column << log2_stride` in ELEMENT units, so a stride that
    // is not a whole power of two in those units is unrepresentable. Every
    // production stride is one — a raw column stride is the poly length, a fold
    // region stride is `2 * size_after_one_fold` — so this is a wiring check, not
    // a limitation.
    if column.stride_bytes % element != 0 || !(column.stride_bytes / element).is_power_of_two() {
        return Err(BwdSegLowerError::StrideNotPowerOfTwo {
            window: index,
            stride_bytes: column.stride_bytes,
        });
    }
    let elements = column.stride_bytes / element;
    let base = column.ptr as usize;
    if base
        .checked_add(slot.columns * column.stride_bytes as usize)
        .is_none()
    {
        return Err(BwdSegLowerError::NullWindowGeometry { window: index });
    }
    Ok(BwdSegAddrSlot {
        // A deferred slot leaves the launch UNRESOLVED unless the caller patches
        // it, and a null base faults on first access rather than reading
        // whatever lives at a plausible address.
        base: if slot.deferred_base {
            std::ptr::null()
        } else {
            column.ptr
        },
        log2_stride: elements.trailing_zeros() as u8,
        origin: if column.is_e4 {
            BWD_COEFF_ORIGIN_READ_EXT
        } else {
            BWD_COEFF_ORIGIN_READ_BASE
        },
        procedural_kind: BWD_COEFF_PROCEDURAL_NONE,
        reserved: [0; 5],
    })
}

/// Resolve ONE wire source's class, depth and two lanes.
///
/// This is where the old per-window lowering's checks live, restated per source
/// because that is where the facts now are: a slot is shared by every source
/// reading its backing, while depth, class and destination are the source's own.
/// Interns a scratch-backed destination slot on first use when the caller
/// supplied none.
#[allow(clippy::too_many_arguments)]
fn lower_source(
    source: usize,
    addr: &ResolvedSourceAddr,
    binding: &BwdSegRoundBinding<'_>,
    table: &mut Vec<BwdSegAddrSlot>,
    slot_columns: &mut Vec<usize>,
    scratch_slot: &mut [Option<usize>],
    scratch: &ResolvedPublishScratch,
    layout: &PublishRoundLayout,
    publish_stride: u32,
    round: u8,
    fold_depth: u8,
    d2: D2Policy,
) -> Result<LoweredSource, BwdSegLowerError> {
    let read_slot = addr.read_slot;
    let slot = binding
        .slots
        .get(read_slot)
        .ok_or(BwdSegLowerError::SourceWindowOutOfRange {
            source,
            window: read_slot.min(u8::MAX as usize) as u8,
        })?;
    let window = read_slot as u8;
    if addr.read_column >= slot_columns[read_slot] {
        return Err(BwdSegLowerError::SourceColumnOutOfWindow {
            source,
            window,
            column: addr.read_column as u16,
        });
    }

    // Target depth IS the round; only the backing depth is the source's to carry.
    if addr.backing_depth > round || round - addr.backing_depth > BWD_COEFF_MAX_FOLD_DEPTH {
        return Err(BwdSegLowerError::InvalidDepths {
            window,
            backing_depth: addr.backing_depth,
            target_depth: round,
        });
    }
    let delta = round - addr.backing_depth;
    if delta > fold_depth || !(delta == 0 || delta == 1 || delta == fold_depth) {
        return Err(BwdSegLowerError::UnsupportedFoldDelta {
            window,
            delta,
            fold_depth,
        });
    }

    // THE ORIGIN IS THE ROUND'S, NOT THE FAMILY'S. See the module doc.
    let origin = match (slot.procedural_kind, slot.base) {
        (_, Some(column)) if column.is_e4 => SourceOrigin::E4,
        (Some(_), Some(_)) => {
            return Err(BwdSegLowerError::ProceduralWindowWithMatrixRead { window })
        }
        (None, Some(_)) => SourceOrigin::Bf,
        (Some(_), None) => SourceOrigin::Procedural,
        (None, None) => return Err(BwdSegLowerError::MissingReadBacking { window }),
    };
    // THE LANDMINE'S INVERSE. Deriving the origin from the round binding trusts
    // the binding, so the two ways a binding can lie about physical state are
    // rejected here rather than lowered:
    //
    //   1. a RAW source at NONZERO depth. A value at depth `k > 0` is the output
    //      of `k` folds, a fold weights with E4 challenges and therefore produces
    //      E4, so ONLY an E4 backing can honestly carry a nonzero depth. The two
    //      raw shapes both produce depth-zero values — a base matrix (never
    //      folded) and row synthesis (procedural, no backing at all) — so the
    //      predicate is "the read backing is not E4", `None` INCLUDED. A nonzero
    //      depth on either is a claim that raw data was folded in place, and it
    //      silently shortens the catch-up.
    //   2. a raw backing for a slot the PREVIOUS round PUBLISHED. The folded
    //      values live in the scratch region; refolding the raw source instead
    //      reads data the chain has already moved past.
    //
    // Both are exactly the "silent raw refold" the module doc says this file
    // exists to prevent, arrived at from the binding side instead of the family
    // side.
    if slot.base.is_none_or(|column| !column.is_e4) && addr.backing_depth != 0 {
        return Err(BwdSegLowerError::BaseReadAtFoldedDepth {
            window,
            backing_depth: addr.backing_depth,
        });
    }
    if origin != SourceOrigin::E4
        && chain_read_column(scratch, u32::from(round), read_slot).is_some()
    {
        return Err(BwdSegLowerError::RawReadOverPriorPublish { window });
    }
    let (class, publishes) = assign_class(origin, delta, d2);

    // The read span, per addressed column: the PAIR total, since the backing
    // carries both endpoint halves (`2 * rows` outputs) and each output consumes
    // its own `2^delta` inputs.
    if slot.base.is_some() {
        let needed = (2 * binding.rows * (1usize << delta)) as u32;
        if slot.read_elements < needed {
            return Err(BwdSegLowerError::ReadSpanOverflow {
                window,
                needed,
                have: slot.read_elements,
            });
        }
    }

    let cache = if publishes {
        // A shorter plan than the slot table means this slot reserves nothing —
        // which is exactly what an explicitly backed destination expects.
        let offset = layout
            .window_base
            .get(read_slot)
            .copied()
            .unwrap_or(PUBLISH_WINDOW_ABSENT);
        match (addr.publish, offset == PUBLISH_WINDOW_ABSENT) {
            // The caller supplied the region (production: a column of the
            // round's own folding buffer), and the plan — built by
            // `plan_publish_scratch`, which reserves nothing for explicitly backed
            // slots — left the entry ABSENT.
            (Some((slot_index, column)), true) => {
                let target = binding.slots.get(slot_index).ok_or(
                    BwdSegLowerError::SourceWindowOutOfRange {
                        source,
                        window: slot_index.min(u8::MAX as usize) as u8,
                    },
                )?;
                let backing =
                    target
                        .base
                        .ok_or(BwdSegLowerError::PlanMissingPublishRegion { window })?;
                // The write extent per column is `2 * rows * 16`, which the
                // destination stride must at least cover or consecutive columns
                // would overwrite each other.
                if !backing.is_e4 || backing.stride_bytes < publish_stride {
                    return Err(BwdSegLowerError::ExplicitPublishGeometry {
                        window,
                        is_e4: backing.is_e4,
                        stride_bytes: backing.stride_bytes,
                    });
                }
                if column >= target.columns {
                    return Err(BwdSegLowerError::SourceColumnOutOfWindow {
                        source,
                        window: slot_index.min(u8::MAX as usize) as u8,
                        column: column as u16,
                    });
                }
                bwd_seg_lane(slot_index, column)
                    .ok_or(BwdSegLowerError::NullWindowGeometry { window })?
            }
            (Some(_), false) => return Err(BwdSegLowerError::AmbiguousPublishBacking { window }),
            (None, true) => return Err(BwdSegLowerError::PlanMissingPublishRegion { window }),
            (None, false) => {
                // The plan's region for this read slot, interned as a table slot
                // on first use so every source of the slot publishes through one
                // entry.
                let index = match scratch_slot[read_slot] {
                    Some(index) => index,
                    None => {
                        if table.len() >= BWD_SEG_ADDR_SLOTS {
                            return Err(BwdSegLowerError::SourceWindowOverflow {
                                windows: table.len() + 1,
                                cap: BWD_SEG_ADDR_SLOTS,
                            });
                        }
                        // SAFETY: the offset is inside the parity buffer this plan
                        // sized and the caller allocated; this computes an address
                        // and never reads it.
                        let base = unsafe {
                            scratch.parity_base[usize::from(round & 1)].add(offset)
                        };
                        let elements = publish_stride / E4_COLUMN_BYTES;
                        debug_assert!(elements.is_power_of_two());
                        table.push(BwdSegAddrSlot {
                            base: base.cast_const(),
                            log2_stride: elements.trailing_zeros() as u8,
                            origin: BWD_COEFF_ORIGIN_READ_EXT,
                            procedural_kind: BWD_COEFF_PROCEDURAL_NONE,
                            reserved: [0; 5],
                        });
                        slot_columns.push(slot_columns[read_slot]);
                        let index = table.len() - 1;
                        scratch_slot[read_slot] = Some(index);
                        index
                    }
                };
                bwd_seg_lane(index, addr.read_column)
                    .ok_or(BwdSegLowerError::NullWindowGeometry { window })?
            }
        }
    } else {
        if addr.publish.is_some() {
            return Err(BwdSegLowerError::UnexpectedPublishBacking { window });
        }
        if layout.window_base.get(read_slot).copied().unwrap_or(PUBLISH_WINDOW_ABSENT)
            != PUBLISH_WINDOW_ABSENT
        {
            return Err(BwdSegLowerError::PlanPublishRegionUnused { window });
        }
        BWD_SEG_ADDR_NONE
    };

    // The chain: when the PREVIOUS round published for this slot, this round's E4
    // read must be exactly that region, at that round's stride.
    if origin == SourceOrigin::E4 && delta >= 1 {
        if let Some((expected_base, expected_stride)) =
            chain_read_column(scratch, u32::from(round), read_slot)
        {
            let base = slot.base.expect("an E4 origin has a backing");
            if base.ptr as usize != expected_base as usize
                || base.stride_bytes != expected_stride
            {
                return Err(BwdSegLowerError::ChainReadNotPriorPublish { window });
            }
        }
    }

    let src = bwd_seg_lane(read_slot, addr.read_column)
        .ok_or(BwdSegLowerError::NullWindowGeometry { window })?;
    Ok(LoweredSource {
        record: BwdSegSourceRecord {
            src,
            cache,
            class: class.code(),
            delta,
        },
        class,
        publishes,
    })
}

fn check_column_geometry(window: u8, column: &ResolvedColumn) -> Result<(), BwdSegLowerError> {
    if column.ptr.is_null() || column.stride_bytes == 0 {
        return Err(BwdSegLowerError::NullWindowGeometry { window });
    }
    let element = if column.is_e4 {
        E4_COLUMN_BYTES
    } else {
        BF_COLUMN_BYTES
    };
    if column.stride_bytes % element != 0 {
        return Err(BwdSegLowerError::WindowStrideMismatch {
            window,
            is_e4: column.is_e4,
            stride_bytes: column.stride_bytes,
        });
    }
    Ok(())
}

/// The pointer-range validations the planner could not make.
///
///   1. the two parity buffers are disjoint — otherwise ping-pong reads what the
///      prologue is writing;
///   2. no publish region overlaps any read range or another publish region; and
///   3. no read range lies inside the parity buffer this round publishes into.
///      Stricter than (2) on purpose: the whole buffer is the prologue's for the
///      launch, and its stale tail belongs to an earlier same-parity round.
/// A strided column set: `count` per-column intervals of `extent` bytes,
/// `stride` bytes apart. The window HULL `base + count * stride` and the
/// touched bytes coincide when the stride is the extent — the parity plan's
/// shape — but an explicitly backed publish strides at its backing's per-poly
/// stride, and a chain read of the same backing sits INSIDE that stride: hull
/// overlap is then normal, so aliasing is judged per column.
#[derive(Clone, Copy)]
struct StridedColumns {
    base: usize,
    stride: usize,
    count: usize,
    extent: usize,
}

impl StridedColumns {
    fn hull(&self) -> (usize, usize) {
        (
            self.base,
            self.base + (self.count - 1) * self.stride + self.extent,
        )
    }

    fn overlaps(&self, other: &StridedColumns) -> bool {
        if self.count == 0 || other.count == 0 {
            return false;
        }
        // Hull fast path: disjoint hulls cannot alias, and the hulls only
        // over-approximate when a stride exceeds its extent.
        let (a_lo, a_hi) = self.hull();
        let (b_lo, b_hi) = other.hull();
        if a_hi <= b_lo || b_hi <= a_lo {
            return false;
        }
        if self.stride == self.extent && other.stride == other.extent {
            return true;
        }
        // Interleaved hulls: judge the actual per-column extents. Quadratic,
        // but host-side, once per lowering, and only for hull-overlapping
        // pairs (in practice: column sets of one per-poly region family).
        for i in 0..self.count {
            let lo = self.base + i * self.stride;
            let hi = lo + self.extent;
            for j in 0..other.count {
                let other_lo = other.base + j * other.stride;
                if lo < other_lo + other.extent && other_lo < hi {
                    return true;
                }
            }
        }
        false
    }
}

/// Reject a launch whose publishes would clobber something it also reads.
///
/// Works on ADDRESSES, so a slot whose base is still null — a procedural slot,
/// or one whose backing is deferred to schedule time
/// ([`ResolvedAddrSlot::deferred_base`]) — is outside what this can decide and is
/// skipped. For the deferred kind that is the caller's obligation, and for the
/// production folding buffers it is structural: a round's destination buffer and
/// everything it reads are different allocations.
#[allow(clippy::too_many_arguments)]
fn check_alias(
    table: &[BwdSegAddrSlot],
    columns: &[usize],
    read_extent: &[usize],
    publishes: &[bool],
    scratch: &ResolvedPublishScratch,
    write_parity: usize,
    read_parity: usize,
    rows: usize,
) -> Result<(), BwdSegLowerError> {
    let buffer = |parity: usize| -> Option<(usize, usize)> {
        let base = scratch.parity_base[parity] as usize;
        let bytes = scratch.plan.bytes_per_parity[parity];
        (base != 0 && bytes != 0).then_some((base, base + bytes))
    };
    if let (Some(write), Some(read)) = (buffer(write_parity), buffer(read_parity)) {
        if write.0 < read.1 && read.0 < write.1 {
            return Err(BwdSegLowerError::ParityBuffersAlias);
        }
    }

    // Per-column write extent: both endpoint halves, as E4. Read extent: the
    // pair total at the window's delta, in the backing's own width — the same
    // count `lower_window`'s span guard bounded against the backing.
    let publish_extent = 2 * rows * E4_COLUMN_BYTES as usize;
    let stride_of = |index: usize| -> usize {
        let slot = &table[index];
        let element = if slot.origin == BWD_COEFF_ORIGIN_READ_EXT {
            E4_COLUMN_BYTES
        } else {
            BF_COLUMN_BYTES
        } as usize;
        element << slot.log2_stride
    };
    let publish_of = |index: usize| -> Option<StridedColumns> {
        (publishes[index] && !table[index].base.is_null()).then_some(StridedColumns {
            base: table[index].base as usize,
            stride: stride_of(index),
            count: columns[index],
            extent: publish_extent,
        })
    };
    let read_of = |index: usize| -> Option<StridedColumns> {
        (read_extent[index] != 0 && !table[index].base.is_null()).then_some(StridedColumns {
            base: table[index].base as usize,
            stride: stride_of(index),
            count: columns[index],
            extent: read_extent[index],
        })
    };
    for index in 0..table.len() {
        let Some(publish) = publish_of(index) else {
            continue;
        };
        for other_index in 0..table.len() {
            let mut aliases = read_of(other_index).is_some_and(|read| publish.overlaps(&read));
            if other_index != index {
                aliases = aliases
                    || publish_of(other_index).is_some_and(|other| publish.overlaps(&other));
            }
            if aliases {
                return Err(BwdSegLowerError::UnsafePublishAlias {
                    window: index as u8,
                    other: other_index as u8,
                });
            }
        }
    }

    if let Some(write) = buffer(write_parity) {
        for index in 0..table.len() {
            let Some(read) = read_of(index) else {
                continue;
            };
            let (read_lo, read_hi) = read.hull();
            if read_lo < write.1 && write.0 < read_hi {
                return Err(BwdSegLowerError::ReadAliasesPublishBuffer {
                    window: index as u8,
                });
            }
        }
    }
    Ok(())
}

/// The category a lean class names in `regime`, or `None` for a dead class.
fn lean_category(regime: BwdRegime, class: u8) -> Option<TermCategory> {
    let table = match regime {
        BwdRegime::R0 => LEAN_R0_OPCODES,
        BwdRegime::Ext => LEAN_CONT_OPCODES,
    };
    table
        .iter()
        .find(|(listed, _)| *listed == u16::from(class))
        .map(|(_, category)| *category)
}

/// Validate one TERM record against the regime and the source table, and annotate
/// it with its operands' classes. The COEFFICIENT field is the caller's, because
/// its meaning depends on where the record sits: a recipe id for a singleton, a
/// core id for a header, an immediate id for a member (spec §4.4).
///
/// `record` is the record's index in the word stream — headers INCLUDED, so it is
/// the index every error variant here reports.
fn annotate_record(
    record: usize,
    term: &LeanTerm,
    regime: BwdRegime,
    source_classes: &[SourceClass],
) -> Result<AnnotatedTerm, BwdSegLowerError> {
    let category = lean_category(regime, term.class).ok_or(LeanCodecError::ClassNotInRegime {
        term: record,
        opcode: u16::from(term.class),
    })?;
    let class_of = |slot: u16| -> Result<SourceClass, BwdSegLowerError> {
        source_classes
            .get(usize::from(slot))
            .copied()
            .ok_or(BwdSegLowerError::SourceSlotOutOfRange { term: record, slot })
    };
    let first = class_of(term.source_a)?;
    let second = if category_arity(category) == 1 {
        if term.source_b != SOURCE_NONE {
            return Err(LeanCodecError::SourceBMustBeNone { term: record }.into());
        }
        None
    } else {
        if term.source_b == SOURCE_NONE {
            return Err(LeanCodecError::SourceBMissing { term: record }.into());
        }
        Some(class_of(term.source_b)?)
    };
    Ok(AnnotatedTerm {
        category,
        operands: [Some(first), second],
    })
}

/// Validate every ATOM against the regime, the payloads and the source table, and
/// annotate every record with its operands' classes.
///
/// This restates most of `lean::validate_program`'s rule set against the objects
/// lowering has: that function needs a `CoeffLayer`, which the GPU side never
/// builds. One rule is NOT restated here: a group header's flags-vs-member-union
/// disagreement (`LeanCodecError::GroupFlagsMismatch`) is validated ISA-side only,
/// by `lean::validate_program` itself. Everything else the release kernel trusts
/// is checked here or nowhere.
///
/// The id spaces split with the atom shape (spec §4.4), which is the one thing
/// this walk knows that a flat record walk cannot: a SINGLETON's coefficient and a
/// HEADER's core are recipe-bank ids, a MEMBER's is an immediate id. Headers
/// contribute no [`AnnotatedTerm`] — they are control records, not terms — while
/// still consuming a record index, so every error index stays the offending
/// record's own.
fn annotate_atoms(
    atoms: &[LeanAtom],
    regime: BwdRegime,
    source_classes: &[SourceClass],
    coefficients: usize,
    immediates: usize,
) -> Result<Vec<SegAtom>, BwdSegLowerError> {
    if immediates > LEAN_MAX_IMMEDIATES {
        return Err(BwdSegLowerError::ImmediateTableOverflow { len: immediates });
    }
    // The literals occupy the two ids below the table, so `id` addresses the
    // table iff `RESERVED <= id < RESERVED + len`.
    let immediate_ids = usize::from(ImmediateId::RESERVED) + immediates;
    let bank = |coeff: u16| -> Result<(), BwdSegLowerError> {
        if usize::from(coeff) >= coefficients {
            return Err(BwdSegLowerError::CoefficientIndexPastBank {
                index: usize::from(coeff),
                entries: coefficients,
            });
        }
        Ok(())
    };
    let mut out = Vec::with_capacity(atoms.len());
    let mut record = 0usize;
    for atom in atoms {
        match atom {
            LeanAtom::Term(term) => {
                bank(term.coeff)?;
                out.push(SegAtom::Term(annotate_record(
                    record,
                    term,
                    regime,
                    source_classes,
                )?));
                record += 1;
            }
            LeanAtom::Group {
                core,
                has_c0,
                has_c2,
                members,
            } => {
                // R0 has no group headers at all — `decode_atoms` decodes class 2
                // there as the live `C2ProductBfBf` term class — so a group here
                // is an Ext-only shape by construction.
                debug_assert!(regime != BwdRegime::R0, "R0 decodes no group headers");
                bank(*core)?;
                let header = record;
                record += 1;
                let mut annotated = Vec::with_capacity(members.len());
                for member in members {
                    if usize::from(member.coeff) >= immediate_ids {
                        return Err(BwdSegLowerError::ImmediateOutOfRange {
                            record,
                            id: member.coeff,
                        });
                    }
                    annotated.push(SegMember {
                        annotated: annotate_record(record, member, regime, source_classes)?,
                        immediate: member.coeff,
                    });
                    record += 1;
                }
                debug_assert_eq!(record - header, 1 + members.len());
                out.push(SegAtom::Group {
                    core: *core,
                    has_c0: *has_c0,
                    has_c2: *has_c2,
                    members: annotated,
                });
            }
        }
    }
    Ok(out)
}

/// The per-list work of one split, over the PER-ATOM costs the deal used.
fn list_work_stats(lists: &[Vec<usize>], costs: &[u64]) -> ListWorkStats {
    let per_list: Vec<u64> = lists
        .iter()
        .map(|atoms| atoms.iter().map(|&atom| costs[atom]).sum())
        .collect();
    let max_work = per_list.iter().copied().max().unwrap_or(0);
    let total: u64 = per_list.iter().sum();
    let mean_work = total as f64 / per_list.len().max(1) as f64;
    ListWorkStats {
        max_work,
        mean_work,
        max_over_mean: if mean_work > 0.0 {
            max_work as f64 / mean_work
        } else {
            0.0
        },
    }
}

// ── Per-configuration DRAM traffic floors (measurement-trust pass §7.2.2) ────
//
// A floor of bytes read and written per LAUNCH assuming perfect caching, computed
// analytically host-side, so a realized NCU figure reads as caching effectiveness
// rather than a guess from wall time. The backward sibling of the forward
// `dag_traffic_floor` (`gkr_eval_isa/src/schedule_search/floor.rs`): same two
// rules — dedupe by distinct backing, and non-DRAM sources contribute nothing —
// over a different cone (the forward floor is output-cone-only over a DAG layer;
// this one is per-launch over a lowered seg descriptor).
//
// CONVENTIONS, stated once so the numbers are comparable:
//   1. Perfect caching AND perfect sector utilization WITHIN a launch, and NO
//      cache survival ACROSS launches. So it is a floor on COMPULSORY traffic and
//      NOT a lower bound on realized DRAM bytes: real L2 retains lines across
//      launch boundaries, in either direction, at any total size. The validation
//      hook is therefore a per-direction conservative SOFT bound, not a hard
//      inequality.
//   2. Sector-granularity waste (32 B sectors) and write-allocate effects are part
//      of the measured DISTANCE, not part of the floor. A strided 4-byte `bf`
//      column read that touches a whole sector per element realizes far above its
//      floor; that gap is a finding about the access pattern.
//   3. Per-launch accounting. Bytes published THIS launch are a write HERE; the
//      read of them NEXT launch is a read THERE. State this wherever a multi-round
//      sum is quoted.
//   4. Constant- and parameter-space traffic is OUTSIDE the floor by convention —
//      the descriptor (parameter space), the `const`-loader coefficient bank, the
//      claim point and the fold-weight bank. Not because it is invisible to
//      `dram__bytes_op_*` (a cold constant line does appear) but because its miss
//      count depends on cache state the walk cannot model. So this is a PARTIAL
//      lower bound, and a small positive `realized - floor` may be constant misses
//      rather than inefficiency.
//
// POLICY-PATH AWARENESS is automatic and is the point: the walk reads the round's
// ACTUAL lowered classes and window depths, never a class-agnostic column list. A
// materialized source appears as its publish backing at the fold depth this round
// assigns it (an `e4` endpoint pair read as a delta-1 chain step); an inline-folded
// source appears as its raw backing at its own fold span and is RE-COUNTED in every
// launch that recomputes the fold — the recompute is not amortized away. So the two
// D2 policy paths have DIFFERENT floors. This pass emits PER-LAUNCH floors only;
// the path-aggregate comparison rides with P3, which is what constructs the
// round-`r+1` state per arm.

/// One launch's compulsory-traffic floor.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct BwdSegTrafficFloor {
    pub read_bytes: u64,
    pub write_bytes: u64,
}

const FLOOR_EXT_BYTES: u64 = 16;
const FLOOR_BASE_BYTES: u64 = 4;

// The floor's element widths ARE the lowering's column widths; two names for one
// fact, so the assert is what keeps them one fact.
const _: () = {
    assert!(FLOOR_EXT_BYTES == E4_COLUMN_BYTES as u64);
    assert!(FLOOR_BASE_BYTES == BF_COLUMN_BYTES as u64);
};

/// The read + write floor of one lowered launch.
///
/// `coeff` and `program` are the LOADER, passed explicitly rather than sniffed
/// from the descriptor's pointers: lowering leaves `desc.coefficients` null and
/// staging patches it afterwards, so a null test would classify the same cell
/// differently pre- and post-stage. They are the caller's inputs to `lower_bwd_seg`,
/// so they are always known.
pub(crate) fn bwd_seg_traffic_floor(
    setup: &BwdSegSetup,
    coeff: CoeffMode,
    program: ProgramMode,
) -> BwdSegTrafficFloor {
    struct View<'a> {
        sources: &'a [BwdSegSourceRecord],
        slots: &'a [BwdSegAddrSlot],
        num_foldable: u64,
        logical_rows: u64,
        eq_low_bits: u32,
        n_coefficients: u64,
        program_words: u64,
    }
    let view = match &setup.desc {
        BwdSegLaunchDesc::Inline(desc) => View {
            sources: &desc.source[..usize::from(desc.num_sources)],
            slots: &desc.slot[..],
            num_foldable: u64::from(desc.num_foldable),
            logical_rows: u64::from(desc.logical_rows),
            eq_low_bits: desc.eq_sizes.low,
            n_coefficients: u64::from(desc.n_coefficients),
            program_words: 0,
        },
        BwdSegLaunchDesc::ProgPtr(desc) => View {
            sources: &desc.source[..usize::from(desc.num_sources)],
            slots: &desc.slot[..],
            num_foldable: u64::from(desc.num_foldable),
            logical_rows: u64::from(desc.logical_rows),
            eq_low_bits: desc.eq_sizes.low,
            n_coefficients: u64::from(desc.n_coefficients),
            program_words: u64::from(desc.program_words),
        },
    };

    // ── The read floor ──────────────────────────────────────────────────────
    // Dedupe by BACKING, not by term reference: a byte read by many terms counts
    // ONCE, because under perfect caching the second reference is a hit. The dedupe
    // key is `(window, column)` — `desc.source[slot]` is
    // `{window, source_class, column}` and the address is
    // `read_base + column * read_stride_bytes`, so that pair identifies the backing
    // exactly. `read_stride_bytes` is the COLUMN stride, not the element width, so
    // it is the dedupe input rather than a multiplier.
    //
    // Each backing carries the MAX endpoint factor over the slots sharing it
    // (`BwdSegSetup::source_endpoints`): one Endpoint0-only reader prices half
    // the pair set; any both-halves reader promotes the whole backing. Slots the
    // setup does not cover (test-edited descriptors) price both halves, which is
    // the pre-§7.3-fix behavior and never underprices.
    let endpoints = &setup.source_endpoints;
    let mut priced: Vec<(u16, u64)> = Vec::with_capacity(view.sources.len());
    for (slot, record) in view.sources.iter().enumerate() {
        let factor = u64::from(endpoints.get(slot).copied().unwrap_or(2));
        match priced.iter_mut().find(|(lane, _)| *lane == record.src) {
            Some((_, seen)) => *seen = (*seen).max(factor),
            None => priced.push((record.src, factor)),
        }
    }
    let mut read_bytes = 0u64;
    for &(lane, factor) in &priced {
        let window = &view.slots[bwd_seg_lane_slot(lane)];
        // Procedural / VirtualSetup sources read NO DRAM: `seg_raw_synthesized`
        // produces the value from the backing INDEX, so there is no raw column at
        // all. Their cost is compute, not traffic — the same rule as the forward
        // floor's `VirtualSetup` exclusion.
        if window.origin == BWD_COEFF_ORIGIN_PROCEDURAL {
            continue;
        }
        let element = if window.origin == BWD_COEFF_ORIGIN_READ_EXT {
            FLOOR_EXT_BYTES
        } else {
            FLOOR_BASE_BYTES
        };
        // Span is the PAIR HALF at the source's own fold depth, per endpoint:
        // the fold reads `raw(row + q*span)` and `raw(rows + row + q*span)` for
        // `q in [0, 2^delta)` with `span = 2*rows`, so a backing's footprint is
        // `2^delta * factor * logical_rows` elements — the full pair set at
        // `factor == 2`, the low halves alone at `factor == 1`, and nothing for
        // a backing no term and no fold touches.
        // The delta is the SOURCE's, so take the widest any source of this lane
        // demands — the same "max over sharers" rule as the endpoint factor.
        let delta = view
            .sources
            .iter()
            .filter(|record| record.src == lane)
            .map(|record| u32::from(record.delta))
            .max()
            .unwrap_or(0);
        read_bytes += element * (1u64 << delta) * factor * view.logical_rows;
    }
    // The eq table counts ONCE, and `eq_sizes.low` is a BIT WIDTH, not a length:
    // the kernel indexes with `lo = gid & ((1u << sizes.low) - 1u)` and uses
    // `sizes.low` as a shift, so the table has `1 << low` entries. The `min` is
    // because a thread only ever presents `lo < logical_rows`, so a table wider
    // than the launch is not fully touched.
    let eq_entries = if view.eq_low_bits >= 63 {
        view.logical_rows
    } else {
        view.logical_rows.min(1u64 << view.eq_low_bits)
    };
    read_bytes += eq_entries * FLOOR_EXT_BYTES;
    // The `ptr` / `progptr` shapes' device-resident payloads are part of the main
    // definition, not a parenthesis: where the payload is a device buffer it is
    // real DRAM traffic and belongs in the floor, counted ONCE under perfect
    // caching. So the floor DIFFERS between loader variants of the same cell, which
    // is correct — those shapes really do move those bytes through DRAM while their
    // `const`/inline twins route them through constant space. §9 item 6(b) carries
    // the open reporting question of whether to normalize that away when comparing
    // loader variants; the walk leaves it in, because the floor should describe the
    // shape that actually runs.
    if coeff == CoeffMode::DevPtr {
        read_bytes += view.n_coefficients * FLOOR_EXT_BYTES;
    }
    if program == ProgramMode::DevPtr {
        read_bytes += view.program_words * 2;
    }

    // ── The write floor ─────────────────────────────────────────────────────
    // Publish: `seg_fold_and_publish` stores exactly two `e4` per live row per
    // foldable source, at `row` and `rows + row`. The stride is THIS launch's
    // `logical_rows`, not a next-round row count — `logical_rows` is documented as
    // "the contribution half-stride and the endpoint half-stride of every
    // target-depth backing", and the two stores are at `row` and `rows + row` of
    // the current launch.
    // Contributions: `seg_store_row` writes two `e4` per live row, from warp 0
    // only, independent of `K` and of the epilogue.
    let write_bytes = (view.num_foldable * 2 + 2) * view.logical_rows * FLOOR_EXT_BYTES;

    BwdSegTrafficFloor {
        read_bytes,
        write_bytes,
    }
}

/// The R11 read-floor diagnostic counts (audit §7.3). The R0 read floor measured
/// impossible — 331.8 B/row overpriced, 4 of 4 captures — with TWO arithmetically
/// indistinguishable mechanisms: dead-slot pricing (the walk charges sources no
/// term reads) and cross-window aliasing (two `(window, column)` keys resolving to
/// one physical backing, double-priced). These are the counts that discriminate
/// them; `dead_sources` is the third and lives on [`BwdSegSetup`], because only
/// lowering sees the term stream's `first_touch`.
pub(crate) struct BwdSegFloorBackingCensus {
    /// `(window, column)`-deduped, non-procedural entries — the set the read
    /// floor prices.
    pub priced_sources: u32,
    /// The priced set deduped by EFFECTIVE ADDRESS
    /// (`read_base + column * read_stride_bytes`). A deficit against
    /// `priced_sources` is a cross-window alias. Start-address equality is the
    /// dedupe the kernel's own addressing justifies — a partial range overlap
    /// between different strides would need a range walk, and no lowering
    /// produces one (windows are whole-buffer views).
    pub distinct_backings: u32,
}

/// See [`BwdSegFloorBackingCensus`]. A pure function of the lowered descriptor,
/// like the floor walk itself.
pub(crate) fn bwd_seg_floor_backing_census(setup: &BwdSegSetup) -> BwdSegFloorBackingCensus {
    let (sources, slots): (&[BwdSegSourceRecord], &[BwdSegAddrSlot]) = match &setup.desc {
        BwdSegLaunchDesc::Inline(desc) => (
            &desc.source[..usize::from(desc.num_sources)],
            &desc.slot[..],
        ),
        BwdSegLaunchDesc::ProgPtr(desc) => (
            &desc.source[..usize::from(desc.num_sources)],
            &desc.slot[..],
        ),
    };
    let mut seen: Vec<u16> = Vec::with_capacity(sources.len());
    let mut addresses: Vec<usize> = Vec::with_capacity(sources.len());
    let mut priced_sources = 0u32;
    for record in sources {
        if seen.contains(&record.src) {
            continue;
        }
        seen.push(record.src);
        let window = &slots[bwd_seg_lane_slot(record.src)];
        if window.origin == BWD_COEFF_ORIGIN_PROCEDURAL {
            continue;
        }
        priced_sources += 1;
        let element = if window.origin == BWD_COEFF_ORIGIN_READ_EXT {
            E4_COLUMN_BYTES
        } else {
            BF_COLUMN_BYTES
        } as usize;
        let address = window.base as usize
            + (bwd_seg_lane_column(record.src) << window.log2_stride) * element;
        if !addresses.contains(&address) {
            addresses.push(address);
        }
    }
    BwdSegFloorBackingCensus {
        priced_sources,
        distinct_backings: addresses.len() as u32,
    }
}

/// The per-direction CONSERVATIVE soft bound (spec §7.2.2).
///
/// The tempting rule — `realized < floor` is impossible — is UNSOUND in both
/// directions and at any total size, because cache retention is per-LINE, not
/// per-total: a publish buffer written by one launch and re-read by the next can be
/// absorbed by L2 and never reach DRAM regardless of how large the launch's other
/// traffic is. Subtracting the WHOLE L2 assumes the most retention physically
/// possible for that direction, so the bound is weak by construction — it will
/// catch a gross floor-walk error and will not catch a subtle one. That is the
/// correct trade for a validity gate whose alternative fires on legitimate
/// measurements. §9 item 6(a) records that this replaces the requirement's original
/// `realized >= floor` wording and wants RR's confirmation.
pub(crate) fn bwd_seg_floor_soft_bound(floor_bytes: u64, l2_bytes: u64) -> u64 {
    floor_bytes.saturating_sub(l2_bytes)
}

#[cfg(test)]
impl BwdSegLaunchDesc {
    /// The descriptor exactly as a launch copies it — INTERIOR PADDING INCLUDED,
    /// which is the point: lowering allocates it zeroed, so two identical
    /// lowerings are byte-identical.
    pub(crate) fn launch_bytes(&self) -> &[u8] {
        let (base, len) = match self {
            BwdSegLaunchDesc::Inline(desc) => (
                &**desc as *const BwdSegDesc as *const u8,
                core::mem::size_of::<BwdSegDesc>(),
            ),
            BwdSegLaunchDesc::ProgPtr(desc) => (
                &**desc as *const BwdSegProgPtrDesc as *const u8,
                core::mem::size_of::<BwdSegProgPtrDesc>(),
            ),
        };
        // SAFETY: both descriptors are `repr(C)` plain data with no interior
        // mutability, and the slice borrows from `self`.
        unsafe { std::slice::from_raw_parts(base, len) }
    }
}

/// Test-only, so that `assert_eq!(lower_bwd_seg(...), Err(...))` compiles: the
/// descriptor is 26 KB of `Copy` plain data that derives no `PartialEq`, so it is
/// compared as the bytes a launch would carry.
#[cfg(test)]
impl PartialEq for BwdSegSetup {
    fn eq(&self, other: &Self) -> bool {
        self.desc.launch_bytes() == other.desc.launch_bytes()
            && self.coefficients == other.coefficients
            && self.claim_point == other.claim_point
            && self.immediates == other.immediates
            && self.program_words == other.program_words
            && self.work == other.work
    }
}

/// Test-only, and a SUMMARY on purpose: the derived form would print 26 KB of
/// mostly-zero arrays into a failure message.
#[cfg(test)]
impl core::fmt::Debug for BwdSegSetup {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let family = match &self.desc {
            BwdSegLaunchDesc::Inline(_) => "inline",
            BwdSegLaunchDesc::ProgPtr(_) => "progptr",
        };
        formatter
            .debug_struct("BwdSegSetup")
            .field("desc", &family)
            .field("coefficients", &self.coefficients.len())
            .field("claim_point", &self.claim_point.len())
            .field("immediates", &self.immediates.len())
            .field("program_words", &self.program_words.len())
            .field("work", &self.work)
            .finish()
    }
}
