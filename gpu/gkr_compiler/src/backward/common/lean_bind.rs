//! Source-window binding for backward window programs.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use gkr_eval_ir::{FieldKind, ReadPlace};

use super::model::{CoeffLayer, CoeffTerm, SourceId, TermId};
use super::source_layout::{window_family, WindowFamily};
use crate::backward::common::limits::{MAX_SOURCE_WINDOWS, SOURCE_WINDOW_COLUMNS};
use crate::source_bind::{bind_source_sequence, BindFailure, LogicalSourceUse};

/// Number of procedural source kinds supported by the descriptor.
///
/// [`VirtualSetupKind`]: gkr_eval_ir::VirtualSetupKind
pub(crate) const LEAN_PROCEDURAL_KINDS: u8 = 4;

// ── Output ───────────────────────────────────────────────────────────────────

/// One addressable column of one window.
#[derive(Clone, Debug, PartialEq, Eq)]
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
#[derive(Clone, Debug, PartialEq, Eq)]
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
                if ext {
                    FieldKind::Ext
                } else {
                    FieldKind::Base
                }
            }
            _ => FieldKind::Base,
        }
    }

    /// The procedural kind tag, or `None` for a real matrix.
    pub fn procedural_kind(&self) -> Option<u8> {
        match self.family {
            WindowFamily::VirtualSetup { kind } => Some(kind),
            _ => None,
        }
    }
}

/// A committed lean program's complete source binding.
///
/// Carries no fold depth: the depth a program is bound for is a property of the
/// typed layer program, and duplicating it here would create a second place for
/// it to be wrong.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeanSourceSlot {
    pub window: u8,
    pub column: u16,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeanSourceBinding {
    pub windows: Vec<LeanBoundWindow>,
    pub source_slots: Vec<LeanSourceSlot>,
}

impl LeanSourceBinding {
    pub fn resolve(&self, window: u8, column: u16) -> Option<SourceId> {
        let entry = self.windows.get(window as usize)?;
        let absolute = entry.first_column.checked_add(usize::from(column))?;
        entry
            .columns
            .binary_search_by_key(&absolute, |candidate| candidate.column)
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
    /// The family selects procedural resolution and backing field width, so it
    /// must be derived from the source.
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
/// # Panics
///
/// If `order` names a term outside `layer.terms`, if a term names a source outside
/// `layer.sources`, or if `order` leaves a source of the layer resolved by nothing.
/// All three are compiler bugs rather than input defects:
/// [`order_terms`](super::order::order_terms) returns a permutation of the layer's
/// terms, [`lower_coeff_layer`](super::lower::lower_coeff_layer) interns a source
/// only when a term consumes it, and
/// the family-specific compiler checks coverage explicitly before it gets here.
pub(crate) fn bind_lean_sources(
    layer: &CoeffLayer,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
    order: &[TermId],
) -> Result<LeanSourceBinding, LeanBindError> {
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
    // With no residency, this is one entry per physical source resolution.
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
    // core is asked for a layout so the overflow can report it. A binder that only learned
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
                if first.is_none_or(|base| column >= base + SOURCE_WINDOW_COLUMNS) {
                    windows += 1;
                    first = Some(column);
                }
            }
            windows
        })
        .sum();
    if needed > MAX_SOURCE_WINDOWS {
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
            }
        })
        .collect();

    let bound = bind_source_sequence(&uses).map_err(|failure| match failure {
        BindFailure::WindowOverflow => {
            unreachable!("the exact window count was checked against the cap above")
        }
    })?;

    let family_at: Vec<WindowFamily> = families.keys().copied().collect();
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

    validate_windows(&windows, layer, cross_fields, SOURCE_WINDOW_COLUMNS)?;

    let mut source_slots = vec![
        LeanSourceSlot {
            window: 0,
            column: 0
        };
        layer.sources.len()
    ];
    for (window_index, window) in windows.iter().enumerate() {
        for column in &window.columns {
            source_slots[column.source as usize] = LeanSourceSlot {
                window: window_index as u8,
                column: u16::try_from(column.column - window.first_column)
                    .expect("a bound source offset fits the fixed window"),
            };
        }
    }

    Ok(LeanSourceBinding {
        windows,
        source_slots,
    })
}

fn validate_windows(
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

        // Unmergeable within one backing. Windows are numbered by ascending
        // `(backing, column)`, so two windows of one backing are adjacent, and a
        // second one based inside the first's 128-column span could have been the
        // first. A layout that admitted it would not be minimal, and window indices
        // are the scarce resource the six-bit field rations.
        if let Some((family, base)) = preceding {
            if family == window.family && window.first_column < base + source_window_columns {
                return Err(LeanBindError::ColumnOverflow {
                    window: at,
                    column: window.first_column,
                });
            }
        }
        preceding = Some((window.family, window.first_column));
    }
    Ok(())
}
