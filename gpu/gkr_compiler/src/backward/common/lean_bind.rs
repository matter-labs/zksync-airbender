//! Placement-free source binding for a segmented lean program (segmented-lean-VM
//! design §4, §5; coefficient-ISA design §9.4, §10.2).
//!
//! The lean VM has no cell file, no residency and no paging, so a source binding
//! here is a small object: there is no
//! per-operand coordinate to emit, because the wire already carries the source
//! SLOT ([`lean`](super::lean)'s `source_a`/`source_b`), and the executor turns a
//! slot into an address through a per-source record. This module produces exactly
//! that:
//!
//!   * [`LeanSourceBinding::windows`] — the window partition of the layer's read
//!     backings, numbered by ascending backing; and
//!   * [`LeanSourceBinding::source_slots`] — one `(window, column)` per source, in
//!     SOURCE SLOT order, which is the CPU-side origin of the GPU descriptor's
//!     per-source record.
//!
//! # What it inherited from the retired cell-era binder
//!
//! The retired `bind_coeff_sources` took a placed program and emitted a
//! per-operand coordinate. Its CHECKS carry over — the window span, the backing
//! origin, the source alias, and the procedural kind — and they are what this
//! module states against a committed TERM ORDER instead of a placement. Its
//! `first_access` marker does NOT carry over: there is no publish-on-first-access
//! state in a VM with no residency, so [`bind_lean_sources`] asks the shared core
//! for no marker at all.
//!
//! # What is deliberately NOT here
//!
//! No per-operand coordinate, no `first_access`, no `materialize` flag, no
//! residency mode, no stride and no device pointer. Strides and publish backings
//! are the GPU descriptor's (design §13 keeps the artifact free of physical
//! pointers), and the ROUND-dependent depth rules (`target_depth == round`,
//! catch-up ∈ `{0, 1, fold_depth}`) belong to GPU round lowering, which is the
//! only place a round exists.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use gkr_eval_ir::{FieldKind, ReadPlace};
use serde::{Deserialize, Serialize};

use super::model::{CoeffLayer, CoeffTerm, SourceId, TermId};
use super::source_layout::{WindowFamily, window_family};
use crate::source_bind::{BindFailure, LogicalSourceUse, bind_source_sequence_with_limits};

/// Procedural source kinds the format admits — the four [`VirtualSetupKind`]
/// values, which `stats::window_family` tags `0..4`.
///
/// The GPU descriptor mirrors this number (`BWD_COEFF_PROCEDURAL_KINDS`) and
/// reserves `0xff` for "not procedural", so a kind at or above this is a window
/// the resolver cannot serve. `procedural_kinds_are_dense_and_bounded` pins the
/// tagging against the enum.
///
/// [`VirtualSetupKind`]: gkr_eval_ir::VirtualSetupKind
pub const LEAN_PROCEDURAL_KINDS: u8 = 4;

// ── Output ───────────────────────────────────────────────────────────────────

/// One addressable column of one window.
///
/// The source is artifactized as a `u32` slot: [`SourceId`] carries no serde
/// derives and this struct nests inside the serialized coordinate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LeanBoundColumn {
    /// The backing's OWN column, not the window-relative offset.
    pub column: usize,
    /// Slot into `CoeffLayer::sources`.
    pub source: u32,
}

/// One bound source window: at most [`SOURCE_WINDOW_COLUMNS`] contiguous columns
/// of ONE logical backing, of which only [`LeanBoundWindow::columns`] are
/// addressable.
///
/// [`SOURCE_WINDOW_COLUMNS`]: super::limits::SOURCE_WINDOW_COLUMNS
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LeanBoundWindow {
    pub family: WindowFamily,
    pub first_column: usize,
    /// Referenced columns, ascending, all in
    /// `[first_column, first_column + SOURCE_WINDOW_COLUMNS)`. Only these are
    /// addressable: an unreferenced column inside the span is a hole.
    pub columns: Vec<LeanBoundColumn>,
}

impl LeanBoundWindow {
    /// The backing matrix's own field. Only a cross-layer output or cache can be
    /// `Ext`; base storage and procedural setup polynomials are base-valued.
    pub fn backing_field(&self) -> FieldKind {
        match self.family {
            WindowFamily::LayerOutput { ext, .. } | WindowFamily::CacheOutput { ext, .. } => {
                if ext { FieldKind::Ext } else { FieldKind::Base }
            }
            _ => FieldKind::Base,
        }
    }

    /// Whether the resolver evaluates this window's columns in closed form instead
    /// of reading DRAM (§9.6's procedural source kind).
    pub fn is_procedural(&self) -> bool {
        self.procedural_kind().is_some()
    }

    /// The procedural kind tag, or `None` for a real matrix.
    pub fn procedural_kind(&self) -> Option<u8> {
        match self.family {
            WindowFamily::VirtualSetup { kind } => Some(kind),
            _ => None,
        }
    }
}

/// One source's bound coordinate: the window it lives in and its offset inside
/// that window's span.
///
/// One per source, in `CoeffLayer::sources` slot order — the wire names a SLOT, so
/// the executor indexes this array directly. `column` is `u16` because that is the
/// width the GPU descriptor's per-source record packs it at; the value itself is
/// always below [`SOURCE_WINDOW_COLUMNS`](super::limits::SOURCE_WINDOW_COLUMNS).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LeanSourceSlot {
    pub window: u8,
    /// Offset from the window's `first_column`.
    pub column: u16,
}

/// A committed lean program's complete source binding.
///
/// Carries no fold depth: the depth a program is bound for is a property of the
/// typed layer program, and duplicating it here would create a second place for
/// it to be wrong.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LeanSourceBinding {
    pub windows: Vec<LeanBoundWindow>,
    pub source_slots: Vec<LeanSourceSlot>,
}

impl LeanSourceBinding {
    /// The source a coordinate names, or `None` for an unassigned column.
    pub fn resolve(&self, window: u8, column: u16) -> Option<SourceId> {
        let entry = self.windows.get(window as usize)?;
        let absolute = entry.first_column.checked_add(usize::from(column))?;
        entry
            .columns
            .binary_search_by_key(&absolute, |c| c.column)
            .ok()
            .map(|index| SourceId(entry.columns[index].source))
    }
}

// ── Errors ───────────────────────────────────────────────────────────────────

/// Everything the lean binder can reject. One variant per check, and every one is
/// derivable from the inputs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LeanBindError {
    /// The layout needs more than [`MAX_SOURCE_WINDOWS`] windows.
    /// `needed` is the exact count, not the cap: a binder that reported only "too
    /// many" would not say how far over.
    ///
    /// [`MAX_SOURCE_WINDOWS`]: super::limits::MAX_SOURCE_WINDOWS
    WindowOverflow { needed: usize },
    /// A window column lies outside its own span
    /// `[first_column, first_column + SOURCE_WINDOW_COLUMNS)`, or the span's
    /// columns are not strictly ascending from `first_column`.
    ///
    /// **A MERGEABLE window maps here too**, reported as
    /// `{ window, column: first_column }`: a window whose backing equals the
    /// PREVIOUS window's and whose base is still inside that window's span could
    /// have been the same window, so the partition is not canonical. That is a
    /// defect of the window's BASE, which is what this variant is about, and the
    /// five-variant list has no separate home for it — `WindowBackingMismatch` would
    /// misreport it, since both windows name their backing correctly.
    ColumnOverflow { window: u8, column: usize },
    /// A window column's declared BACKING COORDINATE — the pair
    /// ([`LeanBoundWindow::family`], column address) — is not the one its own
    /// source resolves to, or two distinct sources claim one backing coordinate.
    ///
    /// The family is not decoration: it is what selects DRAM versus procedural
    /// resolution ([`LeanBoundWindow::is_procedural`]) and the backing's own field
    /// width ([`LeanBoundWindow::backing_field`]), so it must be re-derived from
    /// the source and never trusted.
    WindowBackingMismatch { window: u8 },
    /// A procedurally resolved window claims more than one column. Each procedural
    /// kind is its own single-column family, and GPU lowering's precondition set
    /// rejects a multi-column procedural window outright.
    ProceduralMultiColumn { window: u8 },
    /// A procedural window's kind is not one of the
    /// [`LEAN_PROCEDURAL_KINDS`] the resolver serves.
    UnknownProceduralKind { window: u8, kind: u8 },
}

// ── Binding ──────────────────────────────────────────────────────────────────

/// The sources one term resolves, in the order the lean wire spells them.
///
/// Mirrors `lean::source_slots`'s BF-FIRST normalization of a mixed `C2Product`,
/// so this sequence is the wire's own operand order rather than a second opinion
/// about it. Nothing here DEPENDS on the normalization — the window layout is a
/// function of the referenced `(backing, column)` set and is invariant to the
/// sequence's order, which `binding_is_a_pure_function_of_the_layer_and_the_order`
/// pins — so a divergence from the encoder could not corrupt a coordinate; the
/// spelling is matched so the two passes describe the same program.
///
/// A native dual factor is ONE source per slot even though it consumes both
/// projections of it — with no resident state there is nothing else a slot could
/// resolve.
fn operand_sources(term: &CoeffTerm) -> (SourceId, Option<SourceId>) {
    match term {
        CoeffTerm::C0Linear { value, .. } => (value.source, None),
        CoeffTerm::C2Product {
            lhs,
            rhs,
            lhs_field,
            rhs_field,
            ..
        } => {
            let transposed = matches!((lhs_field, rhs_field), (FieldKind::Ext, FieldKind::Base));
            let (first, second) = if transposed { (rhs, lhs) } else { (lhs, rhs) };
            (first.source, Some(second.source))
        }
        CoeffTerm::DualProduct { lhs, rhs, .. } => (*lhs, Some(*rhs)),
    }
}

/// Bind one committed lean program's sources.
///
/// Deterministic and placement-free: the window partition is a pure function of
/// the `(backing, column)` set the ordered terms resolve, and windows are numbered
/// by ascending backing, so neither the order nor the `K`-split can move a window
/// index.
///
/// `cross_fields` is the circuit's cross-layer field map (a
/// [`DistilledLayer`](crate::backward::common::distill::DistilledLayer)'s
/// `cross_fields`): it
/// decides which homogeneous matrix a cross-layer output read belongs to, exactly
/// as it does for the census.
///
/// `target_depth` is the fold depth this program is bound FOR, and it is recorded
/// rather than validated here. Every rule about it is round-dependent, so GPU
/// round lowering validates the depth against the round it is binding. Nothing in
/// the window layout depends on it.
///
/// # Panics
///
/// If `order` names a term outside `layer.terms`, if a term names a source outside
/// `layer.sources`, or if `order` leaves a source of the layer resolved by nothing.
/// All three are compiler bugs rather than input defects:
/// [`order_terms`](super::order::order_terms) returns a permutation of the layer's
/// terms, [`lower_coeff_layer`](super::lower::lower_coeff_layer) interns a source
/// only when a term consumes it, and
/// the family-specific compiler checks coverage explicitly before it gets here.
pub(crate) fn bind_lean_sources_with_limits(
    layer: &CoeffLayer,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
    order: &[TermId],
    target_depth: u8,
    source_window_columns: usize,
    max_source_windows: usize,
) -> Result<LeanSourceBinding, LeanBindError> {
    // Recorded, not validated — see the doc above. Named in the signature because
    // the coordinate this binding belongs to is bound at one depth and callers read
    // the two together.
    let _ = target_depth;

    // Where each source lives. `(family, column)` IS the read place, so this is
    // the identity the window partition is taken over.
    let placed: Vec<(WindowFamily, usize)> = layer
        .sources
        .iter()
        .map(|source| window_family(source, cross_fields))
        .collect();
    let at = |source: SourceId| -> (WindowFamily, usize) {
        *placed.get(source.0 as usize).unwrap_or_else(|| {
            panic!(
                "term names {source:?}, which is past the layer's {} sources",
                placed.len()
            )
        })
    };

    // The resolution sequence: one entry per operand word of every ordered term,
    // which in a VM with no residency is one entry per physical source resolution.
    let mut sequence: Vec<SourceId> = Vec::with_capacity(2 * order.len());
    for id in order {
        let term = layer.terms.get(id.0 as usize).unwrap_or_else(|| {
            panic!(
                "order names {id:?}, which is past the layer's {} terms",
                layer.terms.len()
            )
        });
        let (first, second) = operand_sources(term);
        sequence.push(first);
        sequence.extend(second);
    }

    // The exact window count the referenced set needs, computed BEFORE the shared
    // core is asked for a layout so the overflow can report it. Windows are the
    // scarce resource (§9.4's `source_window:6`), and a binder that only learned
    // "more than 64" could not say how far over the layer is.
    let mut per_family: BTreeMap<WindowFamily, BTreeSet<usize>> = BTreeMap::new();
    for &source in &sequence {
        let (family, column) = at(source);
        per_family.entry(family).or_default().insert(column);
    }
    let needed: usize = per_family
        .values()
        .map(|columns| {
            let mut windows = 0;
            let mut first = None;
            for &column in columns {
                if first.is_none_or(|base| column >= base + source_window_columns) {
                    windows += 1;
                    first = Some(column);
                }
            }
            windows
        })
        .sum();
    if needed > max_source_windows {
        return Err(LeanBindError::WindowOverflow { needed });
    }

    // Backings are indexed in `WindowFamily` order and the core numbers windows by
    // ascending backing, so the window order is deterministic and independent of
    // the term order.
    let families: BTreeMap<WindowFamily, u8> = per_family
        .keys()
        .enumerate()
        .map(|(index, &family)| (family, index as u8))
        .collect();
    let uses: Vec<LogicalSourceUse> = sequence
        .iter()
        .map(|&source| {
            let (family, column) = at(source);
            LogicalSourceUse {
                slot: families[&family],
                column,
                // A lean source's fold state is a property of the WINDOW's backing
                // and target depth, never of a use, so there is no per-column fold
                // descriptor to agree on here.
                fold_desc: None,
            }
        })
        .collect();

    // No `first_access` marker: a VM with no residency publishes nothing on first
    // access, so there is no bit to assign and nowhere to record one.
    let bound =
        bind_source_sequence_with_limits(&uses, false, source_window_columns, max_source_windows)
            .map_err(|failure| match failure {
            BindFailure::WindowOverflow => {
                unreachable!("the exact window count was checked against the cap above")
            }
            BindFailure::ConflictingFoldDesc { .. } => {
                unreachable!("a lean use carries no fold descriptor")
            }
        })?;

    let family_at: Vec<WindowFamily> = families.keys().copied().collect();
    // `(family, column) -> source` over the RESOLVED set. Two distinct sources
    // mapping to one backing coordinate is the alias defect `audit_windows`
    // reports; the map keeps the first and the audit finds the collision.
    let mut source_at: BTreeMap<(WindowFamily, usize), SourceId> = BTreeMap::new();
    for &source in &sequence {
        source_at.entry(at(source)).or_insert(source);
    }

    let windows: Vec<LeanBoundWindow> = bound
        .windows
        .iter()
        .map(|window| {
            let family = family_at[window.slot as usize];
            LeanBoundWindow {
                family,
                first_column: window.first_column,
                columns: window
                    .columns
                    .iter()
                    .map(|&column| LeanBoundColumn {
                        column,
                        source: source_at[&(family, column)].0,
                    })
                    .collect(),
            }
        })
        .collect();

    audit_windows_with_columns(&windows, layer, cross_fields, source_window_columns)?;

    // One slot per source, dense: the wire names a slot, so the executor indexes
    // this array and a hole would be unaddressable.
    let mut slots: Vec<Option<LeanSourceSlot>> = vec![None; layer.sources.len()];
    for (index, window) in windows.iter().enumerate() {
        for column in &window.columns {
            slots[column.source as usize] = Some(LeanSourceSlot {
                window: index as u8,
                column: (column.column - window.first_column) as u16,
            });
        }
    }
    let source_slots = slots
        .into_iter()
        .enumerate()
        .map(|(slot, bound)| {
            bound.unwrap_or_else(|| {
                panic!(
                    "source {slot} is resolved by no ordered term: the committed order must \
                     cover the layer"
                )
            })
        })
        .collect();

    Ok(LeanSourceBinding {
        windows,
        source_slots,
    })
}

/// The span, canonical-partition, origin, alias and procedural-kind checks, against
/// the layer the binding claims to bind.
///
/// The placement-free half of the retired cell-era binding certificate. It runs
/// on every binding the constructor above produces —
/// the checks are `O(sources)` and they are the only thing that gives
/// [`LeanBoundWindow::family`] its meaning, since the GPU descriptor picks DRAM
/// versus procedural resolution off it. Three of the four defects are unreachable
/// through the constructor by construction; they are checked anyway, because "the
/// constructor cannot produce it" is a claim about today's constructor.
fn audit_windows_with_columns(
    windows: &[LeanBoundWindow],
    layer: &CoeffLayer,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
    source_window_columns: usize,
) -> Result<(), LeanBindError> {
    // How many of the layer's sources resolve to each backing coordinate. The
    // partition assumes `(family, column)` is INJECTIVE over sources — a read
    // family plus its address IS the read place — and a layer that interned the
    // same place twice breaks it silently: the window would address one of the two
    // and every use of the other would read the wrong source. Counting is the only
    // way to see it, because the shared core deduplicates the pair before a window
    // ever exists.
    let mut occupants: BTreeMap<(WindowFamily, usize), usize> = BTreeMap::new();
    for source in &layer.sources {
        *occupants
            .entry(window_family(source, cross_fields))
            .or_default() += 1;
    }

    let mut claimed: BTreeMap<(WindowFamily, usize), u8> = BTreeMap::new();
    let mut sources: BTreeSet<u32> = BTreeSet::new();
    // The preceding window's `(backing, base)`, for the unmergeable rule below.
    let mut preceding: Option<(WindowFamily, usize)> = None;
    for (index, window) in windows.iter().enumerate() {
        let at = index as u8;
        // Span: dense, ascending, and inside the window's own 128 columns.
        let mut last_column: Option<usize> = None;
        for column in &window.columns {
            let inside = column.column >= window.first_column
                && column.column - window.first_column < source_window_columns;
            let ascending = last_column.is_none_or(|last| last < column.column);
            if !inside || !ascending {
                return Err(LeanBindError::ColumnOverflow {
                    window: at,
                    column: column.column,
                });
            }
            last_column = Some(column.column);
        }
        if window
            .columns
            .first()
            .is_none_or(|first| first.column != window.first_column)
        {
            let column = window
                .columns
                .first()
                .map_or(window.first_column, |c| c.column);
            return Err(LeanBindError::ColumnOverflow { window: at, column });
        }

        // Procedural: one column per kind, and a kind the resolver knows. Checked
        // on the DECLARED family, before the per-column origin below re-derives it,
        // so a window claiming a procedural family it cannot serve is reported as
        // the procedural defect it is rather than as a backing mismatch.
        if let Some(kind) = window.procedural_kind() {
            if window.columns.len() != 1 {
                return Err(LeanBindError::ProceduralMultiColumn { window: at });
            }
            if kind >= LEAN_PROCEDURAL_KINDS {
                return Err(LeanBindError::UnknownProceduralKind { window: at, kind });
            }
        }

        // Origin and alias: the declared `(family, column)` is the one the column's
        // own source resolves to, and no two sources — and no two window entries —
        // claim one backing coordinate.
        for column in &window.columns {
            let Some(source) = layer.source(SourceId(column.source)) else {
                return Err(LeanBindError::WindowBackingMismatch { window: at });
            };
            if window_family(source, cross_fields) != (window.family, column.column) {
                return Err(LeanBindError::WindowBackingMismatch { window: at });
            }
            if occupants.get(&(window.family, column.column)) != Some(&1) {
                return Err(LeanBindError::WindowBackingMismatch { window: at });
            }
            if claimed.insert((window.family, column.column), at).is_some()
                || !sources.insert(column.source)
            {
                return Err(LeanBindError::WindowBackingMismatch { window: at });
            }
        }

        // Unmergeable within one backing — the rule that makes the partition
        // CANONICAL rather than merely valid (mirrors the cell-era certificate's
        // final window check). Windows are numbered by ascending
        // `(backing, column)`, so two windows of one backing are adjacent, and a
        // second one based inside the first's 128-column span could have been the
        // first. A layout that admitted it would not be minimal, and window indices
        // are the scarce resource the six-bit field rations.
        if let Some((family, base)) = preceding
            && family == window.family
            && window.first_column < base + source_window_columns
        {
            return Err(LeanBindError::ColumnOverflow {
                window: at,
                column: window.first_column,
            });
        }
        preceding = Some((window.family, window.first_column));
    }
    Ok(())
}
