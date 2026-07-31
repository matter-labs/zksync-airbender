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

use cs::gkr_compiler::dag_ir::{FieldKind, ReadPlace};
use serde::{Deserialize, Serialize};

use super::model::{CoeffLayer, CoeffTerm, SourceId, TermId};
use super::stats::{WindowFamily, window_count, window_family};
use crate::source_bind::{
    self, BindFailure, LogicalSourceUse, SOURCE_WINDOW_COLUMNS, bind_source_sequence,
};

/// Procedural source kinds the format admits — the four [`VirtualSetupKind`]
/// values, which `stats::window_family` tags `0..4`.
///
/// The GPU descriptor mirrors this number (`BWD_COEFF_PROCEDURAL_KINDS`) and
/// reserves `0xff` for "not procedural", so a kind at or above this is a window
/// the resolver cannot serve. `procedural_kinds_are_dense_and_bounded` pins the
/// tagging against the enum.
///
/// [`VirtualSetupKind`]: cs::gkr_compiler::dag_ir::VirtualSetupKind
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
/// COORDINATE ([`target_depth`]), and duplicating it here would create a second
/// place for it to be wrong.
///
/// [`target_depth`]: super::lean_artifact::LeanCoordinateArtifact::target_depth
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
        CoeffTerm::C2Product { lhs, rhs, lhs_field, rhs_field, .. } => {
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
/// [`DistilledLayer`](crate::bwd::distill::DistilledLayer)'s `cross_fields`): it
/// decides which homogeneous matrix a cross-layer output read belongs to, exactly
/// as it does for the census.
///
/// `target_depth` is the fold depth this program is bound FOR, and it is RECORDED
/// rather than validated here: it is passed through to
/// [`LeanCoordinateArtifact::target_depth`] and every rule about it is
/// round-dependent, so GPU round lowering is what validates a depth — against the
/// round it is binding. Nothing in the window layout depends on it, because §10.2's
/// publish policy needs a `first_access` marker to hang off and the lean VM has
/// none.
///
/// # Panics
///
/// If `order` names a term outside `layer.terms`, if a term names a source outside
/// `layer.sources`, or if `order` leaves a source of the layer resolved by nothing.
/// All three are compiler bugs rather than input defects:
/// [`order_terms`](super::order::order_terms) returns a permutation of the layer's
/// terms, [`lower_coeff_layer`](super::lower::lower_coeff_layer) interns a source
/// only when a term consumes it, and
/// [`compile_lean_coordinate`](super::lean_artifact::compile_lean_coordinate)
/// checks the coverage explicitly before it gets here.
///
/// [`LeanCoordinateArtifact::target_depth`]: super::lean_artifact::LeanCoordinateArtifact
pub fn bind_lean_sources(
    layer: &CoeffLayer,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
    order: &[TermId],
    target_depth: u8,
) -> Result<LeanSourceBinding, LeanBindError> {
    // Recorded, not validated — see the doc above. Named in the signature because
    // the coordinate this binding belongs to is bound at one depth and callers read
    // the two together.
    let _ = target_depth;

    // Where each source lives. `(family, column)` IS the read place, so this is
    // the identity the window partition is taken over.
    let placed: Vec<(WindowFamily, usize)> =
        layer.sources.iter().map(|source| window_family(source, cross_fields)).collect();
    let at = |source: SourceId| -> (WindowFamily, usize) {
        *placed.get(source.0 as usize).unwrap_or_else(|| {
            panic!("term names {source:?}, which is past the layer's {} sources", placed.len())
        })
    };

    // The resolution sequence: one entry per operand word of every ordered term,
    // which in a VM with no residency is one entry per physical source resolution.
    let mut sequence: Vec<SourceId> = Vec::with_capacity(2 * order.len());
    for id in order {
        let term = layer.terms.get(id.0 as usize).unwrap_or_else(|| {
            panic!("order names {id:?}, which is past the layer's {} terms", layer.terms.len())
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
    let needed: usize = per_family.values().map(window_count).sum();
    if needed > source_bind::MAX_SOURCE_WINDOWS {
        return Err(LeanBindError::WindowOverflow { needed });
    }

    // Backings are indexed in `WindowFamily` order and the core numbers windows by
    // ascending backing, so the window order is deterministic and independent of
    // the term order.
    let families: BTreeMap<WindowFamily, u8> =
        per_family.keys().enumerate().map(|(index, &family)| (family, index as u8)).collect();
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
    let bound = bind_source_sequence(&uses, false).map_err(|failure| match failure {
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

    audit_windows(&windows, layer, cross_fields)?;

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

    Ok(LeanSourceBinding { windows, source_slots })
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
fn audit_windows(
    windows: &[LeanBoundWindow],
    layer: &CoeffLayer,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
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
        *occupants.entry(window_family(source, cross_fields)).or_default() += 1;
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
                && column.column - window.first_column < SOURCE_WINDOW_COLUMNS;
            let ascending = last_column.is_none_or(|last| last < column.column);
            if !inside || !ascending {
                return Err(LeanBindError::ColumnOverflow { window: at, column: column.column });
            }
            last_column = Some(column.column);
        }
        if window.columns.first().is_none_or(|first| first.column != window.first_column) {
            let column = window.columns.first().map_or(window.first_column, |c| c.column);
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
            && window.first_column < base + SOURCE_WINDOW_COLUMNS
        {
            return Err(LeanBindError::ColumnOverflow { window: at, column: window.first_column });
        }
        preceding = Some((window.family, window.first_column));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use cs::gkr_compiler::dag_ir::{BwdRegime, VirtualSetupKind};

    use super::*;
    use crate::bwd::coeff::model::{CoeffSource, CoefficientRecipeId, ProjectionId};
    use crate::bwd::source::OriginLeaf;

    fn layer(sources: Vec<CoeffSource>, terms: Vec<CoeffTerm>) -> CoeffLayer {
        CoeffLayer {
            regime: BwdRegime::Ext,
            c_init: None,
            coefficients: Vec::new(),
            sources,
            terms,
            groups: Vec::new(),
            immediates: Vec::new(),
        }
    }

    fn witness(column: usize) -> CoeffSource {
        CoeffSource {
            origin: OriginLeaf::Read(ReadPlace::BaseLayerWitness { column }),
            field: FieldKind::Ext,
        }
    }

    fn output(layer: usize, offset: usize) -> CoeffSource {
        CoeffSource {
            origin: OriginLeaf::Read(ReadPlace::LayerOutput { layer, offset }),
            field: FieldKind::Ext,
        }
    }

    fn virtual_setup(kind: VirtualSetupKind) -> CoeffSource {
        CoeffSource { origin: OriginLeaf::VirtualSetup { kind }, field: FieldKind::Base }
    }

    fn c0(index: u32, source: u32) -> CoeffTerm {
        CoeffTerm::C0Linear {
            id: TermId(index),
            coefficient: CoefficientRecipeId::ONE,
            value: ProjectionId::endpoint0(SourceId(source)),
            field: FieldKind::Ext,
        }
    }

    fn dual(index: u32, lhs: u32, rhs: u32) -> CoeffTerm {
        CoeffTerm::DualProduct {
            id: TermId(index),
            coefficient: CoefficientRecipeId::ONE,
            lhs: SourceId(lhs),
            rhs: SourceId(rhs),
        }
    }

    fn ids(count: u32) -> Vec<TermId> {
        (0..count).map(TermId).collect()
    }

    fn no_cross() -> HashMap<ReadPlace, FieldKind> {
        HashMap::new()
    }

    /// One window per backing, columns dense and ascending, one slot per source,
    /// and every slot resolves back to its own source.
    #[test]
    fn a_binding_is_dense_over_the_source_table() {
        let layer =
            layer(vec![witness(4), witness(5), output(0, 9)], vec![c0(0, 0), dual(1, 1, 2)]);
        let binding = bind_lean_sources(&layer, &no_cross(), &ids(2), 3).expect("binds");

        assert_eq!(binding.windows.len(), 2, "witness columns and one layer output");
        assert_eq!(binding.windows[0].family, WindowFamily::BaseLayerWitness);
        assert_eq!(binding.windows[0].first_column, 4);
        assert_eq!(
            binding.windows[0].columns,
            vec![
                LeanBoundColumn { column: 4, source: 0 },
                LeanBoundColumn { column: 5, source: 1 },
            ],
        );
        assert_eq!(binding.source_slots.len(), 3, "one slot per source");
        assert_eq!(binding.source_slots[1], LeanSourceSlot { window: 0, column: 1 });
        for (slot, bound) in binding.source_slots.iter().enumerate() {
            assert_eq!(
                binding.resolve(bound.window, bound.column),
                Some(SourceId(slot as u32)),
                "slot {slot} must resolve to its own source",
            );
        }
    }

    /// Deterministic: the same layer binds to the same bytes on every call, and the
    /// window numbering follows the BACKING order, not the term order.
    #[test]
    fn binding_is_a_pure_function_of_the_layer_and_the_order() {
        let layer = layer(
            vec![output(1, 0), witness(0), virtual_setup(VirtualSetupKind::RangeCheck16Bits)],
            vec![c0(0, 2), c0(1, 0), c0(2, 1)],
        );
        let forward = bind_lean_sources(&layer, &no_cross(), &ids(3), 0).expect("binds");
        let reversed: Vec<TermId> = ids(3).into_iter().rev().collect();
        let backward = bind_lean_sources(&layer, &no_cross(), &reversed, 0).expect("binds");
        assert_eq!(forward, backward, "the window layout is order-independent");
        assert_eq!(
            forward.windows.iter().map(|w| w.family).collect::<Vec<_>>(),
            vec![
                WindowFamily::BaseLayerWitness,
                WindowFamily::LayerOutput { layer: 1, ext: true },
                WindowFamily::VirtualSetup { kind: 0 },
            ],
            "windows are numbered by ascending backing",
        );
    }

    /// A layer whose distinct backings exceed the six-bit window field is rejected
    /// with the EXACT count it needs.
    #[test]
    fn too_many_backings_overflow_the_window_field() {
        let count = source_bind::MAX_SOURCE_WINDOWS + 1;
        let sources: Vec<CoeffSource> = (0..count).map(|layer| output(layer, 0)).collect();
        let terms: Vec<CoeffTerm> = (0..count).map(|i| c0(i as u32, i as u32)).collect();
        let layer = layer(sources, terms);
        assert_eq!(
            bind_lean_sources(&layer, &no_cross(), &ids(count as u32), 3),
            Err(LeanBindError::WindowOverflow { needed: count }),
        );
    }

    /// One backing needs a second window as soon as its referenced columns span
    /// more than the 128 a window covers — and that is not an overflow.
    #[test]
    fn a_wide_backing_is_split_into_freely_based_windows() {
        let sources = vec![witness(0), witness(SOURCE_WINDOW_COLUMNS), witness(1)];
        let layer = layer(sources, vec![c0(0, 0), c0(1, 1), c0(2, 2)]);
        let binding = bind_lean_sources(&layer, &no_cross(), &ids(3), 3).expect("binds");
        assert_eq!(binding.windows.len(), 2);
        assert_eq!(binding.windows[0].first_column, 0);
        assert_eq!(binding.windows[1].first_column, SOURCE_WINDOW_COLUMNS);
        assert_eq!(binding.source_slots[1], LeanSourceSlot { window: 1, column: 0 });
    }

    /// Two sources interned at ONE backing coordinate: the window would resolve to
    /// one of them and silently mis-address the other.
    #[test]
    fn two_sources_at_one_backing_coordinate_are_rejected() {
        let layer = layer(vec![witness(7), witness(7)], vec![c0(0, 0), c0(1, 1)]);
        assert_eq!(
            bind_lean_sources(&layer, &no_cross(), &ids(2), 3),
            Err(LeanBindError::WindowBackingMismatch { window: 0 }),
        );
    }

    /// Every procedural kind the corpus can carry tags densely inside
    /// [`LEAN_PROCEDURAL_KINDS`], which is what makes the bound checkable at all.
    #[test]
    fn procedural_kinds_are_dense_and_bounded() {
        let kinds = [
            VirtualSetupKind::RangeCheck16Bits,
            VirtualSetupKind::RangeCheckTimestamp,
            VirtualSetupKind::InitsAndTeardownsLow,
            VirtualSetupKind::InitsAndTeardownsHigh,
        ];
        let count = kinds.len();
        let sources: Vec<CoeffSource> = kinds.into_iter().map(virtual_setup).collect();
        let terms: Vec<CoeffTerm> = (0..count).map(|i| c0(i as u32, i as u32)).collect();
        let layer = layer(sources, terms);
        let binding = bind_lean_sources(&layer, &no_cross(), &ids(4), 0).expect("binds");
        let tags: BTreeSet<u8> =
            binding.windows.iter().filter_map(|w| w.procedural_kind()).collect();
        assert_eq!(tags, BTreeSet::from([0, 1, 2, 3]), "one single-column window per kind");
        assert_eq!(tags.len(), usize::from(LEAN_PROCEDURAL_KINDS));
        assert!(binding.windows.iter().all(|w| w.is_procedural() && w.columns.len() == 1));
        assert!(
            binding.windows.iter().all(|w| w.backing_field() == FieldKind::Base),
            "a procedural setup polynomial is base-valued",
        );
    }

    /// A cross-layer output is the only family that can be `Ext`-backed.
    #[test]
    fn only_a_cross_layer_backing_can_be_ext_valued() {
        let layer = layer(vec![output(2, 3), witness(0)], vec![c0(0, 0), c0(1, 1)]);
        let binding = bind_lean_sources(&layer, &no_cross(), &ids(2), 3).expect("binds");
        let ext: Vec<FieldKind> = binding.windows.iter().map(|w| w.backing_field()).collect();
        assert_eq!(ext, vec![FieldKind::Base, FieldKind::Ext], "witness first, output second");
    }

    // ── The audit's own rejection paths ──────────────────────────────────────
    //
    // `bind_lean_sources` cannot construct these three: the shared core never emits
    // an out-of-span column, and `window_family` puts every procedural kind at
    // column zero with a tag below `LEAN_PROCEDURAL_KINDS`. The audit is what keeps
    // that true, so it is exercised directly rather than through a constructor that
    // is currently incapable of the defect.

    fn audited(windows: Vec<LeanBoundWindow>, layer: &CoeffLayer) -> Result<(), LeanBindError> {
        audit_windows(&windows, layer, &no_cross())
    }

    #[test]
    fn a_column_outside_its_window_span_is_rejected() {
        let layer = layer(vec![witness(0), witness(SOURCE_WINDOW_COLUMNS)], vec![c0(0, 0)]);
        let window = LeanBoundWindow {
            family: WindowFamily::BaseLayerWitness,
            first_column: 0,
            columns: vec![
                LeanBoundColumn { column: 0, source: 0 },
                LeanBoundColumn { column: SOURCE_WINDOW_COLUMNS, source: 1 },
            ],
        };
        assert_eq!(
            audited(vec![window], &layer),
            Err(LeanBindError::ColumnOverflow { window: 0, column: SOURCE_WINDOW_COLUMNS }),
        );
    }

    #[test]
    fn a_window_not_based_at_its_first_column_is_rejected() {
        let layer = layer(vec![witness(3)], vec![c0(0, 0)]);
        let window = LeanBoundWindow {
            family: WindowFamily::BaseLayerWitness,
            first_column: 2,
            columns: vec![LeanBoundColumn { column: 3, source: 0 }],
        };
        assert_eq!(
            audited(vec![window], &layer),
            Err(LeanBindError::ColumnOverflow { window: 0, column: 3 }),
        );
    }

    /// A procedural window addresses ONE column, because each procedural kind is
    /// its own single-column family. Two columns means the resolver would have to
    /// index a closed form it has no index for — the precondition GPU lowering
    /// rejects outright.
    #[test]
    fn a_multi_column_procedural_window_is_rejected() {
        let layer = layer(
            vec![
                virtual_setup(VirtualSetupKind::RangeCheck16Bits),
                virtual_setup(VirtualSetupKind::RangeCheckTimestamp),
            ],
            vec![c0(0, 0), c0(1, 1)],
        );
        let wide = LeanBoundWindow {
            family: WindowFamily::VirtualSetup { kind: 0 },
            first_column: 0,
            columns: vec![
                LeanBoundColumn { column: 0, source: 0 },
                LeanBoundColumn { column: 1, source: 1 },
            ],
        };
        assert_eq!(
            audited(vec![wide], &layer),
            Err(LeanBindError::ProceduralMultiColumn { window: 0 }),
        );
    }

    /// A procedural kind past the four the resolver serves. The descriptor reserves
    /// `0xff` for "not procedural", so an unserved kind is not merely unknown — it
    /// is indistinguishable from a real matrix on the wire.
    #[test]
    fn a_procedural_kind_the_resolver_does_not_serve_is_rejected() {
        let layer = layer(vec![virtual_setup(VirtualSetupKind::RangeCheck16Bits)], vec![c0(0, 0)]);
        let window = LeanBoundWindow {
            family: WindowFamily::VirtualSetup { kind: LEAN_PROCEDURAL_KINDS },
            first_column: 0,
            columns: vec![LeanBoundColumn { column: 0, source: 0 }],
        };
        assert_eq!(
            audited(vec![window], &layer),
            Err(LeanBindError::UnknownProceduralKind { window: 0, kind: LEAN_PROCEDURAL_KINDS }),
        );
    }

    /// A column whose source the layer does not have — the origin check's other
    /// half, and the one an empty source table exposes on its own.
    #[test]
    fn a_column_naming_an_unknown_source_is_rejected() {
        let empty = layer(Vec::new(), Vec::new());
        let window = LeanBoundWindow {
            family: WindowFamily::BaseLayerWitness,
            first_column: 0,
            columns: vec![LeanBoundColumn { column: 0, source: 0 }],
        };
        assert_eq!(
            audited(vec![window], &empty),
            Err(LeanBindError::WindowBackingMismatch { window: 0 }),
        );
    }

    /// The unmergeable rule: two windows of ONE backing whose bases are within a
    /// span of each other could have been one window, so the partition is not
    /// canonical. Reported against the SECOND window's base.
    #[test]
    fn mergeable_same_backing_windows_are_rejected() {
        let adjacent = layer(vec![witness(0), witness(1)], vec![c0(0, 0), c0(1, 1)]);
        let window = |first_column: usize, source: u32| LeanBoundWindow {
            family: WindowFamily::BaseLayerWitness,
            first_column,
            columns: vec![LeanBoundColumn { column: first_column, source }],
        };
        assert_eq!(
            audited(vec![window(0, 0), window(1, 1)], &adjacent),
            Err(LeanBindError::ColumnOverflow { window: 1, column: 1 }),
            "column 1 fits window 0's span, so the two are one window",
        );
        // Exactly one span apart is the first legal base, and a DIFFERENT backing
        // may share a base — the rule is per backing, not global.
        let far = layer(vec![witness(0), witness(SOURCE_WINDOW_COLUMNS)], vec![c0(0, 0), c0(1, 1)]);
        assert_eq!(audited(vec![window(0, 0), window(SOURCE_WINDOW_COLUMNS, 1)], &far), Ok(()));
        let mixed = layer(vec![witness(0), output(0, 0)], vec![c0(0, 0), c0(1, 1)]);
        let other = LeanBoundWindow {
            family: WindowFamily::LayerOutput { layer: 0, ext: true },
            first_column: 0,
            columns: vec![LeanBoundColumn { column: 0, source: 1 }],
        };
        assert_eq!(audited(vec![window(0, 0), other], &mixed), Ok(()));
    }

    /// A window whose DECLARED family is not the one its column's own source
    /// resolves to. Nothing else in the certificate can catch this: the column table
    /// is keyed by column alone, so such a window still resolves to the right
    /// `SourceId` while selecting the wrong backing — DRAM versus procedural, and
    /// the wrong width.
    #[test]
    fn a_window_declaring_the_wrong_family_is_rejected() {
        let one_witness = layer(vec![witness(0)], vec![c0(0, 0)]);
        let relabelled = LeanBoundWindow {
            family: WindowFamily::BaseLayerMemory,
            first_column: 0,
            columns: vec![LeanBoundColumn { column: 0, source: 0 }],
        };
        assert_eq!(
            audited(vec![relabelled], &one_witness),
            Err(LeanBindError::WindowBackingMismatch { window: 0 }),
            "the source is a witness column, not a memory column",
        );
    }

    /// An empty window has no first column to be based at.
    #[test]
    fn an_empty_window_is_rejected() {
        let layer = layer(vec![witness(0)], vec![c0(0, 0)]);
        let bare = LeanBoundWindow {
            family: WindowFamily::BaseLayerWitness,
            first_column: 0,
            columns: Vec::new(),
        };
        assert_eq!(
            audited(vec![bare], &layer),
            Err(LeanBindError::ColumnOverflow { window: 0, column: 0 }),
        );
    }

    /// `target_depth` is recorded, not validated: the binding is the same object at
    /// every depth, because nothing in the window layout depends on one. GPU round
    /// lowering owns the depth rules, all of which are round-dependent.
    #[test]
    fn the_binding_does_not_depend_on_the_target_depth() {
        let layer = layer(vec![witness(0), output(1, 2)], vec![c0(0, 0), dual(1, 0, 1)]);
        let at_zero = bind_lean_sources(&layer, &no_cross(), &ids(2), 0).expect("binds");
        for depth in 1..=8u8 {
            assert_eq!(
                bind_lean_sources(&layer, &no_cross(), &ids(2), depth),
                Ok(at_zero.clone()),
                "depth {depth}",
            );
        }
    }

    #[test]
    #[should_panic(expected = "must cover the layer")]
    fn an_order_that_leaves_a_source_unresolved_is_rejected() {
        let layer = layer(vec![witness(0), witness(1)], vec![c0(0, 0), c0(1, 1)]);
        let _ = bind_lean_sources(&layer, &no_cross(), &ids(1), 3);
    }

    #[test]
    #[should_panic(expected = "past the layer's 1 terms")]
    fn an_order_naming_an_unknown_term_is_rejected() {
        let layer = layer(vec![witness(0)], vec![c0(0, 0)]);
        let _ = bind_lean_sources(&layer, &no_cross(), &[TermId(7)], 3);
    }
}
